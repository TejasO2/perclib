#!/usr/bin/env bash
# Merge finished work branches onto the integration branch as one gated batch, the
# procedure of docs/COORDINATOR.md section 1. Usage, from the repository root:
#
#   scripts/integrate.sh BASE BRANCH...
#
# BASE is passed to scripts/gate.sh (the integration tip the batch is merged onto).
# The script refuses (exit 2) unless the current branch is the integration branch
# ($INTEGRATE_BRANCH, default claude/zen-lovelace-rvlcw2), the tracked tree is clean and
# no scripts/gate.sh is running. It records the tip, then merges each BRANCH in order
# with `git merge --no-ff`; the message of the n-th branch is $MSG_<n> (default
# "Merge <branch>") followed by a blank line and $INTEGRATE_TRAILER (the attribution
# lines). A conflict only in import lines of PercLib.lean is resolved by keeping every
# `public import` line once, sorted; any other conflict aborts that merge and the branch
# is skipped. Modules missing from the import closure (scripts/check_import_closure.py)
# get `public import` lines in sorted position, committed. Then scripts/gate.sh BASE runs
# once, output to a log file. On failure the branch is reset to the recorded tip (local
# only), the last merged branch is dropped and the rest re-merged and re-gated, until the
# gate passes or no branch is left. Nothing is ever pushed.
# Exit 0 if the gate passed, 1 if not, 2 on refusal or bad usage.
set -uo pipefail

ROOT=PercLib
INTEGRATION=${INTEGRATE_BRANCH:-claude/zen-lovelace-rvlcw2}
GATE_PATTERN=${INTEGRATE_GATE_PATTERN:-scripts/gate.sh}
LOG_DIR=${INTEGRATE_LOG_DIR:-.lake/integrate}

die() { echo "integrate: $*" >&2; exit 2; }

[ $# -ge 2 ] || die "usage: scripts/integrate.sh BASE BRANCH..."
base=$1; shift
branches=("$@")

cd "$(git rev-parse --show-toplevel 2>/dev/null)" || die "not in a git repository"
[ "$(git symbolic-ref --short -q HEAD)" == "$INTEGRATION" ] \
  || die "not on $INTEGRATION"
[ -z "$(git status --porcelain --untracked-files=no)" ] || die "tracked tree is dirty"
pgrep -f "$GATE_PATTERN" >/dev/null && die "another $GATE_PATTERN is running"
git rev-parse -q --verify "$base^{commit}" >/dev/null || die "unknown BASE $base"
tip=$(git rev-parse HEAD)

# Python helpers on $ROOT.lean: `resolve` rewrites conflict hunks that contain only
# `public import` lines (exit 1 if any hunk has anything else); `insert MOD...` adds
# import lines in sorted position.
imports_py() {
  python3 - "$ROOT.lean" "$@" <<'EOF'
import re, sys
path, cmd, mods = sys.argv[1], sys.argv[2], sys.argv[3:]
lines = open(path, encoding="utf-8").read().splitlines(keepends=True)
is_imp = lambda l: re.fullmatch(r"public import \S+\s*", l) is not None
def norm(l):
    return l.rstrip() + "\n"
if cmd == "resolve":
    out, i, n = [], 0, len(lines)
    while i < n:
        if not lines[i].startswith("<<<<<<< "):
            out.append(lines[i]); i += 1; continue
        j, body = i + 1, []
        while j < n and not lines[j].startswith(">>>>>>> "):
            if not (lines[j].startswith("=======") or lines[j].startswith("||||||| ")):
                body.append(lines[j])
            j += 1
        if j == n or not all(is_imp(l) or not l.strip() for l in body):
            sys.exit(1)
        out.extend(sorted({norm(l) for l in body if l.strip()}))
        i = j + 1
    # every maximal run of import lines: each line once, sorted
    res, k = [], 0
    while k < len(out):
        if is_imp(out[k]):
            run = []
            while k < len(out) and is_imp(out[k]):
                run.append(norm(out[k])); k += 1
            res.extend(sorted(set(run)))
        else:
            res.append(out[k]); k += 1
    lines = res
elif cmd == "insert":
    for mod in mods:
        new = f"public import {mod}\n"
        if new in lines:
            continue
        idx = [k for k, l in enumerate(lines) if is_imp(l)]
        if not idx:
            sys.exit("no public import line to insert after")
        pos = next((k for k in idx if norm(lines[k]) > new), idx[-1] + 1)
        if pos == len(lines) and not lines[-1].endswith("\n"):
            lines[-1] += "\n"
        lines.insert(pos, new)
open(path, "w", encoding="utf-8").write("".join(lines))
EOF
}

message_for() {  # $1: 1-based index, $2: branch
  local var="MSG_$1"
  printf '%s\n' "${!var:-Merge $2}"
  [ -n "${INTEGRATE_TRAILER:-}" ] && printf '\n%s\n' "$INTEGRATE_TRAILER"
}

declare -A skipped=()   # branch -> reason
skip_order=()
merged=()

merge_one() {  # $1: index, $2: branch; returns 0 if merged
  local n=$1 b=$2 msg unmerged
  if ! git rev-parse -q --verify "$b^{commit}" >/dev/null; then
    skipped[$b]="no such branch"; skip_order+=("$b"); return 1
  fi
  msg=$(message_for "$n" "$b")
  git merge --no-ff -q -m "$msg" "$b" >/dev/null 2>&1 && return 0
  unmerged=$(git diff --name-only --diff-filter=U)
  if [ "$unmerged" == "$ROOT.lean" ] && imports_py resolve; then
    git add "$ROOT.lean" && git commit -q -m "$msg" >/dev/null && return 0
  fi
  git merge --abort 2>/dev/null || git reset -q --hard HEAD
  if [ -z "$unmerged" ]; then
    skipped[$b]="merge failed"
  else
    skipped[$b]="conflict in $(echo "$unmerged" | head -3 | paste -sd, -)"
  fi
  skip_order+=("$b")
  return 1
}

close_imports() {  # add missing modules of the import closure; commit them
  local missing
  missing=$(python3 scripts/check_import_closure.py "$ROOT" 2>/dev/null \
    | sed -n "s|^error: \(.*\)\.lean is not in the import closure of .*|\1|p" | tr / .)
  [ -n "$missing" ] || return 0
  # shellcheck disable=SC2086
  imports_py insert $missing || return 1
  git add "$ROOT.lean"
  git commit -q -m "$ROOT.lean: import $(echo $missing | wc -w) module(s) missing from the closure${INTEGRATE_TRAILER:+

$INTEGRATE_TRAILER}" >/dev/null
  added_imports=$(echo $missing | wc -w)
}

mkdir -p "$LOG_DIR"
todo=("${branches[@]}")
attempt=0 status=1 gate_line="gate not run" log="" added_imports=0
while :; do
  merged=() added_imports=0
  git reset -q --hard "$tip"
  for b in "${todo[@]}"; do
    for k in "${!branches[@]}"; do [ "${branches[$k]}" == "$b" ] && n=$((k + 1)); done
    merge_one "$n" "$b" && merged+=("$b")
  done
  if [ ${#merged[@]} -eq 0 ]; then
    git reset -q --hard "$tip"
    gate_line="gate not run: no branch left to merge"
    break
  fi
  close_imports
  attempt=$((attempt + 1))
  log="$LOG_DIR/gate-$(date +%Y%m%d-%H%M%S)-$attempt.log"
  echo "integrate: gate attempt $attempt on ${#merged[@]} branch(es), log $log"
  if scripts/gate.sh "$base" >"$log" 2>&1; then
    status=0
    gate_line=$(grep -E '^== gate passed' "$log" | tail -1)
    [ -n "$gate_line" ] || gate_line="gate exit 0"
    break
  fi
  gate_line="gate FAILED (attempt $attempt): $(tail -1 "$log" | cut -c1-120)"
  last=${merged[-1]}
  skipped[$last]="dropped after gate failure (log $log)"; skip_order+=("$last")
  todo=()
  for b in "${merged[@]}"; do [ "$b" == "$last" ] || todo+=("$b"); done
  git reset -q --hard "$tip"
  [ ${#todo[@]} -gt 0 ] || { gate_line="$gate_line; no branch left"; break; }
done

echo "== integrate summary (tip before batch: ${tip:0:12}, now: $(git rev-parse --short=12 HEAD))"
extra=""; [ "$added_imports" -gt 0 ] && extra="; closure imports added: $added_imports"
echo "merged (${#merged[@]}): ${merged[*]:-none}$extra"
echo "skipped (${#skip_order[@]}):"
shown=0
for b in "${skip_order[@]}"; do
  [ $shown -lt 14 ] || { echo "  ... and $(( ${#skip_order[@]} - shown )) more"; break; }
  echo "  $b: ${skipped[$b]}"; shown=$((shown + 1))
done
echo "gate: $gate_line"
echo "log: ${log:-none}"
[ $status -eq 0 ] && echo "nothing pushed; push only after review" || true
exit $status
