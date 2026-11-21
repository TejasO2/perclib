#!/usr/bin/env python3
"""Unit tests of scripts/automerge_classify.py, on fixtures in the shape of the GitHub API."""
import copy
import difflib
import io
import json
import shutil
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import automerge_classify as am  # noqa: E402

BASE_FILE = '''module

public import PercLib.Basic

/-! # Example

## Main results
* `foo_le`: a bound. The word def in a docstring is harmless.
-/

namespace PercLib

variable {n : ℕ}

/-- A helper; its proof may change. -/
theorem helper (h : n ≤ 3) : n ≤ 4 := by
  omega

@[tag "AB12"]
theorem foo_le (h : n ≤ 3) :
    n ≤ 5 := by
  have := helper h
  omega

noncomputable def bar : ℕ := 3

end PercLib
'''

PROOF_EDIT = BASE_FILE.replace('''  have := helper h
  omega''', '''  -- a new comment, mentioning a def and @[tag "ZZZZ"] is fine in a comment? no: see test
  exact Nat.le_trans (helper h) (by norm_num)''')

PROOF_EDIT_CLEAN = BASE_FILE.replace('''  have := helper h
  omega''', '''  -- shorter proof
  exact Nat.le_trans (helper h) (by norm_num)''')

NEW_LEMMA = BASE_FILE.replace('noncomputable def bar', '''/-- Another lemma; the instance of the
class of bounds is mentioned only in this docstring. -/
theorem foo_lt (h : n ≤ 3) : n < 6 := by
  have := foo_le h
  omega

noncomputable def bar''')


def patch(old, new):
    lines = difflib.unified_diff(old.split('\n')[:-1] if old else [],
                                 new.split('\n')[:-1], lineterm='', n=3)
    return '\n'.join(l for l in lines if not l.startswith(('---', '+++')))


def entry(path, old, new, status=None, **extra):
    status = status or ('added' if old is None else 'modified')
    d = dict(filename=path, status=status, additions=1, deletions=1, changes=2,
             patch=patch(old or '', new))
    d.update(extra)
    return d


class Fixture:
    """A pull request: file listing plus the base and head trees on disk."""

    def __init__(self):
        self.root = Path(tempfile.mkdtemp(prefix='automerge-test-'))
        FIXTURES.append(self.root)
        self.entries = []

    def lean(self, path, old, new, **extra):
        for side, text in (('base', old), ('head', new)):
            if text is not None:
                f = self.root / side / path
                f.parent.mkdir(parents=True, exist_ok=True)
                f.write_text(text)
        self.entries.append(entry(path, old, new, **extra))
        return self

    def classify(self, title=None):
        am.classify(copy.deepcopy(self.entries), self.root / 'base', self.root / 'head',
                    title)


PATH = 'PercLib/Probability/Example.lean'
FIXTURES = []


def tearDownModule():
    for root in FIXTURES:
        shutil.rmtree(root, ignore_errors=True)


class PathTests(unittest.TestCase):
    def rejected(self, entries, title=None):
        with self.assertRaises(am.Reject):
            am.check_paths(entries, title)

    def test_each_excluded_path_rejected(self):
        for path in ['PercLib/Basic.lean', 'PercLib/Models/Basic.lean',
                     'PercLib/Probability/Defs.lean', 'PercLib.lean', 'scripts/gate.sh',
                     'scripts/Foo.lean', '.github/workflows/ci.yml',
                     '.github/automerge-authors', '.github/CODEOWNERS', 'lean-toolchain',
                     'lake-manifest.json', 'lakefile.toml', 'docs/DECISIONS.md',
                     'docs/STATUS.md', 'README.md', 'wiki/articles/x.md',
                     'tasks/open/foo.md', 'tasks/done/foo.md', 'PercLib/Foo.md',
                     'PercLib/../scripts/x.lean', 'PercLib/a b.lean', 'Other/Foo.lean']:
            with self.subTest(path=path):
                self.rejected([dict(filename=path, status='modified', patch='@@ -1 +1 @@\n-a\n+b',
                                    changes=2, additions=1, deletions=1)])

    def test_removed_and_renamed_lean_rejected(self):
        self.rejected([dict(filename=PATH, status='removed', patch='', changes=1)])
        self.rejected([dict(filename=PATH, status='renamed',
                            previous_filename='PercLib/Old.lean', changes=0)])

    def test_rename_into_percLib_from_outside_rejected(self):
        for prev in ['scripts/Helper.lean', 'Scratch/Foo.lean', 'PercLib/Defs.lean',
                     'tasks/open/foo.md']:
            with self.subTest(prev=prev):
                self.rejected([dict(filename=PATH, status='renamed', previous_filename=prev,
                                    changes=0, additions=0, deletions=0, patch='')])

    def test_missing_patch_rejected(self):
        self.rejected([dict(filename=PATH, status='modified', changes=5000)])

    def test_own_task_move_accepted(self):
        move = dict(filename='tasks/done/nm-foo.md', previous_filename='tasks/open/nm-foo.md',
                    status='renamed', changes=0, additions=0, deletions=0)
        self.assertEqual(am.check_paths([move], 'nm-foo: prove the bound'), [])
        claimed = dict(move, previous_filename='tasks/claimed/nm-foo.md')
        self.assertEqual(am.check_paths([claimed], 'nm-foo'), [])

    def test_task_moves_rejected(self):
        move = dict(filename='tasks/done/nm-foo.md', previous_filename='tasks/open/nm-foo.md',
                    status='renamed', changes=0, additions=0, deletions=0)
        self.rejected([move], 'nm-bar: something else')       # not its own task
        self.rejected([move], 'nm-foo2: prefix of another id')
        self.rejected([move], None)
        self.rejected([dict(move, changes=2, additions=1, deletions=1)], 'nm-foo')  # edited
        self.rejected([dict(move, filename='tasks/done/nm-bar.md')], 'nm-foo')
        self.rejected([dict(move, filename='tasks/open/nm-foo.md',
                            previous_filename='tasks/done/nm-foo.md')], 'nm-foo')
        self.rejected([dict(filename='tasks/open/new.md', status='added', changes=3)], 'new')
        other = dict(move, filename='tasks/done/nm-baz.md',
                     previous_filename='tasks/open/nm-baz.md')
        self.rejected([move, other], 'nm-foo')


class ClassifyTests(unittest.TestCase):
    def accept(self, fixture, title=None):
        fixture.classify(title)

    def reject(self, fixture, title=None, contains=None):
        with self.assertRaises(am.Reject) as cm:
            fixture.classify(title)
        if contains:
            self.assertIn(contains, str(cm.exception))

    def test_proof_only_accepted(self):
        self.accept(Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN))

    def test_new_lemma_with_docstring_words_accepted(self):
        self.accept(Fixture().lean(PATH, BASE_FILE, NEW_LEMMA))

    def test_proof_only_with_own_task_move_accepted(self):
        f = Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN)
        f.entries.append(dict(filename='tasks/done/ex.md', previous_filename='tasks/open/ex.md',
                              status='renamed', changes=0, additions=0, deletions=0))
        self.accept(f, 'ex: shorten a proof')
        self.reject(f, 'other: title of another task')

    def test_new_or_removed_file_rejected(self):
        new = 'module\n\npublic import PercLib.Basic\n\ntheorem t : True := trivial\n'
        self.reject(Fixture().lean('PercLib/New/Proofs.lean', None, new), contains='added')
        f = Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN)
        f.entries[0]['status'] = 'removed'
        self.reject(f, contains='removed')

    def test_tag_line_in_patch_rejected_even_in_comment(self):
        self.reject(Fixture().lean(PATH, BASE_FILE, PROOF_EDIT), contains='tag')

    def test_tag_line_added_rejected(self):
        new = NEW_LEMMA.replace('theorem foo_lt', '@[tag "CD34"]\ntheorem foo_lt')
        self.reject(Fixture().lean(PATH, BASE_FILE, new), contains='tag')

    def test_tag_removed_or_changed_rejected(self):
        for new in [BASE_FILE.replace('@[tag "AB12"]\n', ''),
                    BASE_FILE.replace('@[tag "AB12"]', '@[tag "AB13"]'),
                    BASE_FILE.replace('@[tag "AB12"]', '@[simp, tag "AB12"]')]:
            with self.subTest(new=new[:0]):
                self.reject(Fixture().lean(PATH, BASE_FILE, new))

    def test_tagged_statement_change_rejected(self):
        # The changed line holds no tag and no keyword; only the statement comparison
        # (and the command check) can see it.
        new = BASE_FILE.replace('    n ≤ 5 := by', '    n ≤ 6 := by')
        self.reject(Fixture().lean(PATH, BASE_FILE, new), contains='AB12')

    def test_tagged_statement_far_from_tag_rejected(self):
        base = BASE_FILE.replace('theorem foo_le (h : n ≤ 3) :\n    n ≤ 5 := by',
                                 'theorem foo_le (h : n ≤ 3)\n' +
                                 ''.join(f'    (h{i} : {i} = {i})\n' for i in range(12)) +
                                 '    : n ≤ 5 := by')
        head = base.replace('(h7 : 7 = 7)', '(h7 : 7 ≤ 7)')
        self.reject(Fixture().lean(PATH, base, head), contains='AB12')

    def test_untagged_statement_change_accepted(self):
        new = BASE_FILE.replace('theorem helper (h : n ≤ 3) : n ≤ 4',
                                'theorem helper (h : n ≤ 3) : n ≤ 3 + 1')
        self.accept(Fixture().lean(PATH, BASE_FILE, new))

    def test_hidden_def_rejected(self):
        variants = {
            'new def': NEW_LEMMA.replace('theorem foo_lt', 'def sneaky : ℕ := 1\n\ntheorem foo_lt'),
            'private def': BASE_FILE.replace('end PercLib', 'private def s : ℕ := 2\n\nend PercLib'),
            'def inside a proof': PROOF_EDIT_CLEAN.replace(
                '  -- shorter proof', '  let _ : ℕ := 0\n  def x := 1'),
            'def body edited': BASE_FILE.replace('noncomputable def bar : ℕ := 3',
                                                 'noncomputable def bar : ℕ :=\n  3'),
            'def continuation edited': BASE_FILE.replace(
                'noncomputable def bar : ℕ := 3', 'noncomputable def bar : ℕ :=\n  3').replace(
                '  3\n\nend', '  4\n\nend'),
            'instance': BASE_FILE.replace('end PercLib', 'instance : Inhabited Foo := ⟨0⟩\nend PercLib'),
            'structure': BASE_FILE.replace('end PercLib', 'structure S where\n  x : ℕ\nend PercLib'),
            'abbrev': BASE_FILE.replace('end PercLib', 'abbrev T := ℕ\nend PercLib'),
            'class': BASE_FILE.replace('end PercLib', 'class C (α : Type) : Prop\nend PercLib'),
            'notation': BASE_FILE.replace('end PercLib', 'notation "‖" x "‖" => x\nend PercLib'),
            'local notation': BASE_FILE.replace('end PercLib', 'local notation "q" => 3\nend PercLib'),
            'axiom': BASE_FILE.replace('end PercLib', 'axiom ax : False\nend PercLib'),
            'opaque': BASE_FILE.replace('end PercLib', 'opaque o : ℕ\nend PercLib'),
            'attribute': BASE_FILE.replace('end PercLib', 'attribute [simp] foo_le\nend PercLib'),
            'instance attr on theorem': BASE_FILE.replace('/-- A helper', '@[instance]\n/-- A helper'),
            'variable': BASE_FILE.replace('variable {n : ℕ}', 'variable {n : ℕ} [Fact (n = 1)]'),
            'open': BASE_FILE.replace('namespace PercLib', 'namespace PercLib\n\nopen Real'),
            'import': BASE_FILE.replace('public import PercLib.Basic',
                                        'public import PercLib.Basic\npublic import Mathlib'),
            'run_cmd': BASE_FILE.replace('end PercLib', 'run_cmd pure ()\nend PercLib'),
            '#eval': BASE_FILE.replace('end PercLib', '#eval 1\nend PercLib'),
            'set_option in proof': PROOF_EDIT_CLEAN.replace(
                '  exact', '  set_option maxRecDepth 9000 in\n  exact'),
            'native_decide': PROOF_EDIT_CLEAN.replace('(by norm_num)', '(by native_decide)'),
            'elab': BASE_FILE.replace('end PercLib', 'elab "x" : tactic => pure ()\nend PercLib'),
            'def after block comment': BASE_FILE.replace(
                'end PercLib', '/- a comment -/ def z := 1\nend PercLib'),
            'def in docstring-adjacent line': NEW_LEMMA.replace(
                'class of bounds is mentioned only in this docstring. -/',
                'class of bounds is mentioned only in this docstring. -/ def w := 1\n'),
        }
        for name, new in variants.items():
            with self.subTest(variant=name):
                self.reject(Fixture().lean(PATH, BASE_FILE, new))

    def test_edit_inside_definition_body_rejected(self):
        # No keyword on the changed line: the command check must see the enclosing def.
        base = BASE_FILE.replace('noncomputable def bar : ℕ := 3',
                                 'noncomputable def bar : ℕ :=\n  3 + 0')
        self.reject(Fixture().lean(PATH, base, base.replace('  3 + 0', '  4 + 0')),
                    contains="inside a 'noncomputable' command")
        base = BASE_FILE.replace('end PercLib', 'structure S where\n  x : ℕ\n\nend PercLib')
        self.reject(Fixture().lean(PATH, base, base.replace('  x : ℕ', '  x : ℤ')),
                    contains="inside a 'structure' command")
        base = BASE_FILE.replace('end PercLib',
                                 '@[simp]\ninstance : Inhabited S :=\n  ⟨1⟩\n\nend PercLib')
        self.reject(Fixture().lean(PATH, base, base.replace('  ⟨1⟩', '  ⟨2⟩')),
                    contains="inside a 'instance' command")

    def test_column_zero_continuation_rejected(self):
        new = BASE_FILE.replace('noncomputable def bar : ℕ := 3',
                                'noncomputable def bar : ℕ :=\n3')
        self.reject(Fixture().lean(PATH, BASE_FILE, new))

    def test_patch_must_match_contents(self):
        f = Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN)
        # The head file on disk differs from what the patch says.
        (f.root / 'head' / PATH).write_text(PROOF_EDIT_CLEAN.replace('norm_num', 'omega'))
        self.reject(f, contains='does not reproduce')
        g = Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN)
        (g.root / 'base' / PATH).write_text(BASE_FILE.replace('helper h', 'helper  h'))
        self.reject(g, contains='does not apply')

    def test_missing_contents_rejected(self):
        f = Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN)
        with self.assertRaises(am.Reject):
            am.classify(f.entries, None, None)
        (f.root / 'head' / PATH).unlink()
        self.reject(f, contains='missing')

    def test_unterminated_comment_rejected(self):
        new = PROOF_EDIT_CLEAN.replace('  -- shorter proof', '  /- open comment')
        self.reject(Fixture().lean(PATH, BASE_FILE, new))

    def test_comment_and_string_handling(self):
        lines = am.split_lines(am.strip_comments(
            'a /- x /- nested -/ def -/ b\n"-- not a comment" -- def\nc \'"\' d\n'))
        self.assertEqual(lines, ['a   b', '"-- not a comment" ', 'c \'"\' d'])


EVIDENCE_HEAD = 'a' * 40
EVIDENCE_BASE = 'b' * 40


def evidence():
    pr = dict(number=7, state='open', draft=False, merged=False, title='ex: shorten',
              user=dict(login='TomHutchcroft'), changed_files=1,
              head=dict(sha=EVIDENCE_HEAD, ref='x', repo=dict(full_name='o/perclib')),
              base=dict(sha=EVIDENCE_BASE, ref='main', repo=dict(full_name='o/perclib')))
    run = dict(id=99, workflow_id=5, event='pull_request', status='completed',
               conclusion='success', head_sha=EVIDENCE_HEAD,
               pull_requests=[dict(number=7, head=dict(sha=EVIDENCE_HEAD),
                                   base=dict(sha=EVIDENCE_BASE))])
    jobs = dict(jobs=[dict(name='gate', conclusion='success', head_sha=EVIDENCE_HEAD),
                      dict(name='kernel-replay', conclusion='skipped')])
    branch = dict(name='main', protected=True, commit=dict(sha=EVIDENCE_BASE))
    compare = dict(behind_by=0, ahead_by=2, merge_base_commit=dict(sha=EVIDENCE_BASE))
    workflow = dict(id=5, path='.github/workflows/ci.yml')
    return dict(run=run, jobs=jobs, pr=pr, branch=branch, compare=compare, workflow=workflow)


class EvidenceTests(unittest.TestCase):
    authors = {'tomhutchcroft'}

    def check(self, ev):
        return am.check_evidence(ev['run'], ev['jobs'], ev['pr'], ev['branch'],
                                 ev['compare'], ev['workflow'], self.authors, 'main')

    def test_green_accepted(self):
        self.assertEqual(self.check(evidence()), (7, EVIDENCE_HEAD, EVIDENCE_BASE))

    def test_each_failure_rejected(self):
        def set_(path, value):
            def mutate(ev):
                d = ev
                for key in path[:-1]:
                    d = d[key]
                d[path[-1]] = value
            return mutate
        cases = {
            'author not listed': set_(('pr', 'user', 'login'), 'someone'),
            'draft': set_(('pr', 'draft'), True),
            'closed': set_(('pr', 'state'), 'closed'),
            'other base branch': set_(('pr', 'base', 'ref'), 'dev'),
            'fork': set_(('pr', 'head', 'repo', 'full_name'), 'fork/perclib'),
            'other workflow': set_(('run', 'workflow_id'), 6),
            'push event': set_(('run', 'event'), 'push'),
            'run failed': set_(('run', 'conclusion'), 'failure'),
            'stale head': set_(('run', 'head_sha'), 'c' * 40),
            'stale run head in PR entry': lambda ev: ev['run']['pull_requests'][0].update(
                head=dict(sha='c' * 40)),
            'base bound differently': lambda ev: ev['run']['pull_requests'][0].update(
                base=dict(sha='c' * 40)),
            'run for another PR': lambda ev: ev['run']['pull_requests'][0].update(number=8),
            'run for two PRs': lambda ev: ev['run']['pull_requests'].append(
                dict(number=8, head=dict(sha=EVIDENCE_HEAD), base=dict(sha=EVIDENCE_BASE))),
            'gate skipped': lambda ev: ev['jobs']['jobs'][0].update(conclusion='skipped'),
            'gate missing': lambda ev: ev['jobs'].update(jobs=[]),
            'two gates': lambda ev: ev['jobs']['jobs'].append(
                dict(name='gate', conclusion='success')),
            'base moved': set_(('branch', 'commit', 'sha'), 'c' * 40),
            'unprotected': set_(('branch', 'protected'), False),
            'head behind base': set_(('compare', 'behind_by'), 1),
            'malformed sha': set_(('pr', 'head', 'sha'), 'main'),
        }
        for name, mutate in cases.items():
            with self.subTest(case=name):
                ev = evidence()
                mutate(ev)
                with self.assertRaises(am.Reject):
                    self.check(ev)


class CommandLineTests(unittest.TestCase):
    def run_main(self, argv, stdin):
        old = sys.stdin
        sys.stdin = io.StringIO(stdin)
        out = io.StringIO()
        try:
            with redirect_stdout(out):
                code = am.main(argv)
        finally:
            sys.stdin = old
        return code, out.getvalue()

    def test_decide_end_to_end(self):
        f = Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN)
        ev = evidence()
        files = {}
        for key, value in ev.items():
            files[key] = f.root / f'{key}.json'
            files[key].write_text(json.dumps(value))
        authors = f.root / 'authors'
        authors.write_text('# Tom adds collaborators.\ntomhutchcroft\n')
        output = f.root / 'out'
        argv = ['decide', '--run', str(files['run']), '--jobs', str(files['jobs']),
                '--pr', str(files['pr']), '--branch', str(files['branch']),
                '--compare', str(files['compare']), '--ci-workflow', str(files['workflow']),
                '--authors', str(authors), '--default-branch', 'main',
                '--base-dir', str(f.root / 'base'), '--head-dir', str(f.root / 'head'),
                '--github-output', str(output)]
        stdin = '\n'.join(json.dumps(e) for e in f.entries) + '\n'
        code, text = self.run_main(argv, stdin)
        self.assertEqual(code, 0, text)
        self.assertIn('merge=true', output.read_text())
        self.assertIn(f'head={EVIDENCE_HEAD}', output.read_text())
        # Listing shorter than changed_files: rejected.
        ev['pr']['changed_files'] = 2
        files['pr'].write_text(json.dumps(ev['pr']))
        output.unlink()
        code, text = self.run_main(argv, stdin)
        self.assertEqual(code, 1)
        self.assertFalse(output.exists())
        # Malformed authors file: rejected.
        ev['pr']['changed_files'] = 1
        files['pr'].write_text(json.dumps(ev['pr']))
        authors.write_text('tomhutchcroft; rm -rf /\n')
        self.assertEqual(self.run_main(argv, stdin)[0], 1)

    def test_plan(self):
        other = 'PercLib/Other.lean'
        f = Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN).lean(other, BASE_FILE, NEW_LEMMA)
        pr = f.root / 'pr.json'
        pr.write_text(json.dumps(dict(title='x')))
        code, text = self.run_main(['plan', '--pr', str(pr)], json.dumps(f.entries))
        self.assertEqual(code, 0)
        self.assertEqual(text.split(), ['base', PATH, 'head', PATH, 'base', other, 'head', other])
        bad = f.entries + [dict(filename='scripts/x.py', status='modified', patch='')]
        self.assertEqual(self.run_main(['plan', '--pr', str(pr)], json.dumps(bad))[0], 1)

    def test_paginated_listing(self):
        f = Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN).lean(
            'PercLib/Other.lean', BASE_FILE, NEW_LEMMA)
        pages = json.dumps(f.entries[:1], indent=2) + json.dumps(f.entries[1:])
        self.assertEqual(len(am.read_files(io.StringIO(pages))), 2)
        lines = '\n'.join(json.dumps(e) for e in f.entries)
        self.assertEqual(len(am.read_files(io.StringIO(lines))), 2)

    def test_garbage_input_rejected(self):
        self.assertEqual(self.run_main(['classify'], 'not json')[0], 1)
        self.assertEqual(self.run_main(['classify'], '[]')[0], 1)


if __name__ == '__main__':
    unittest.main()
