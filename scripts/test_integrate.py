#!/usr/bin/env python3
"""Tests for scripts/integrate.sh in a temporary git repository with a stub
scripts/gate.sh (fails when the file named by $STUB_GATE_FAIL_IF exists)."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parent
INTEGRATION = "claude/zen-lovelace-rvlcw2"
TRAILER = "Co-Authored-By: Test <test@example.invalid>\nClaude-Session: test"

STUB_GATE = """#!/usr/bin/env bash
echo "== gate on $(git rev-parse HEAD)"
if [ -n "${STUB_GATE_FAIL_IF:-}" ] && [ -e "$STUB_GATE_FAIL_IF" ]; then
  echo "error: stub gate failed"; exit 1
fi
echo "== gate passed on $(git rev-parse HEAD)"
"""


class IntegrateTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = Path(self.tmp.name) / "repo"
        self.logs = Path(self.tmp.name) / "logs"
        self.repo.mkdir()
        self.env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@e.invalid",
                        GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@e.invalid",
                        GIT_EDITOR="true", INTEGRATE_TRAILER=TRAILER,
                        INTEGRATE_LOG_DIR=str(self.logs),
                        INTEGRATE_GATE_PATTERN="no-such-gate-process-" + os.urandom(4).hex())
        self.env.pop("STUB_GATE_FAIL_IF", None)
        self.git("init", "-q", "-b", INTEGRATION)
        (self.repo / "scripts").mkdir()
        for name in ("integrate.sh", "check_import_closure.py"):
            shutil.copy(SCRIPTS / name, self.repo / "scripts" / name)
        (self.repo / "scripts" / "gate.sh").write_text(STUB_GATE)
        (self.repo / "scripts" / "gate.sh").chmod(0o755)
        (self.repo / "PercLib").mkdir()
        self.write("PercLib/A.lean", "module\n\ndef a := 1\n")
        self.write("PercLib/M.lean", "module\n\ndef m := 1\n")
        self.write("PercLib.lean",
                   "module\n\npublic import PercLib.A\npublic import PercLib.M\n")
        self.commit_all("init")
        self.base = self.git("rev-parse", "HEAD")

    def tearDown(self):
        self.tmp.cleanup()

    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.repo, env=self.env, check=True,
                              capture_output=True, text=True).stdout.strip()

    def write(self, rel, text):
        (self.repo / rel).write_text(text)

    def commit_all(self, msg):
        self.git("add", "-A")
        self.git("commit", "-q", "-m", msg)

    def branch(self, name, files, imports=()):
        """work/<name> off the base: new or changed files, and import lines appended
        after the last import of PercLib.lean (so two such branches conflict)."""
        self.git("checkout", "-q", "-b", f"work/{name}", self.base)
        for rel, text in files.items():
            self.write(rel, text)
        if imports:
            root = (self.repo / "PercLib.lean").read_text()
            self.write("PercLib.lean",
                       root + "".join(f"public import {m}\n" for m in imports))
        self.commit_all(f"{name} work")
        self.git("checkout", "-q", INTEGRATION)

    def integrate(self, *branches, **env):
        return subprocess.run(["bash", "scripts/integrate.sh", self.base, *branches],
                              cwd=self.repo, env=dict(self.env, **env),
                              capture_output=True, text=True)

    def root_imports(self):
        return [l for l in (self.repo / "PercLib.lean").read_text().splitlines()
                if l.startswith("public import")]

    def test_clean_merge_with_message_and_trailer(self):
        self.branch("x", {"PercLib/X.lean": "module\n"}, ["PercLib.X"])
        result = self.integrate("work/x", MSG_1="Merge work/x (one line)")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("merged (1): work/x", result.stdout)
        self.assertIn("gate: == gate passed on", result.stdout)
        self.assertLessEqual(len(result.stdout.split("== integrate summary")[1].splitlines()), 20)
        msg = self.git("log", "-1", "--format=%B")
        self.assertTrue(msg.startswith("Merge work/x (one line)\n\nCo-Authored-By: Test"), msg)
        self.assertEqual(len(self.git("log", "-1", "--format=%P").split()), 2)

    def test_import_line_conflict_resolved(self):
        self.branch("x", {"PercLib/X.lean": "module\n"}, ["PercLib.X"])
        self.branch("b", {"PercLib/B.lean": "module\n"}, ["PercLib.B"])
        result = self.integrate("work/x", "work/b")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("merged (2): work/x work/b", result.stdout)
        self.assertEqual(self.root_imports(), [
            "public import PercLib.A", "public import PercLib.B",
            "public import PercLib.M", "public import PercLib.X"])
        self.assertNotIn("<<<<<<<", (self.repo / "PercLib.lean").read_text())
        self.assertTrue(self.git("log", "-1", "--format=%B").startswith("Merge work/b\n\n"))

    def test_non_import_conflict_skipped_and_closure_import_added(self):
        self.branch("c", {"PercLib/A.lean": "module\n\ndef a := 2\n"})
        self.branch("d", {"PercLib/A.lean": "module\n\ndef a := 3\n"})
        self.branch("z", {"PercLib/C.lean": "module\n"})  # no import line
        result = self.integrate("work/c", "work/d", "work/z")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("merged (2): work/c work/z; closure imports added: 1", result.stdout)
        self.assertIn("work/d: conflict in PercLib/A.lean", result.stdout)
        self.assertEqual((self.repo / "PercLib/A.lean").read_text(), "module\n\ndef a := 2\n")
        self.assertEqual(self.root_imports(), [
            "public import PercLib.A", "public import PercLib.C", "public import PercLib.M"])
        self.assertEqual(self.git("status", "--porcelain", "--untracked-files=no"), "")

    def test_gate_failure_drops_last_branch(self):
        self.branch("x", {"PercLib/X.lean": "module\n"}, ["PercLib.X"])
        self.branch("bad", {"BAD": "x\n"})
        result = self.integrate("work/x", "work/bad", STUB_GATE_FAIL_IF="BAD")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("merged (1): work/x", result.stdout)
        self.assertIn("work/bad: dropped after gate failure", result.stdout)
        self.assertFalse((self.repo / "BAD").exists())
        self.assertEqual(len(list(self.logs.glob("gate-*.log"))), 2)

    def test_gate_failure_with_no_branch_left_resets_to_tip(self):
        self.branch("bad", {"BAD": "x\n"})
        result = self.integrate("work/bad", STUB_GATE_FAIL_IF="BAD")
        self.assertEqual(result.returncode, 1)
        self.assertIn("no branch left", result.stdout)
        self.assertEqual(self.git("rev-parse", "HEAD"), self.base)

    def test_refuses_dirty_tree(self):
        self.write("PercLib/A.lean", "changed\n")
        result = self.integrate("work/x")
        self.assertEqual(result.returncode, 2)
        self.assertIn("dirty", result.stderr)

    def test_refuses_while_gate_runs(self):
        marker = self.env["INTEGRATE_GATE_PATTERN"]
        sleeper = subprocess.Popen(["bash", "-c", f"sleep 30; : {marker}"])
        try:
            result = self.integrate("work/x")
        finally:
            sleeper.kill()
            sleeper.wait()
        self.assertEqual(result.returncode, 2)
        self.assertIn("is running", result.stderr)


if __name__ == "__main__":
    unittest.main()
