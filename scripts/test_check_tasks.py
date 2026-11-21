#!/usr/bin/env python3
"""Tests for scripts/check_tasks.py on small temporary trees, and a run on this repository."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest

from check_tasks import check, main

REPO = Path(__file__).resolve().parent.parent

SECTIONS_OK = """
## Goal
Prove wiki assertion **AAAA** (article `art-one`).

## Target
The statement.

## Owned files
- `PercLib/Area/File.lean` (append only).
- New `PercLib/Area/Tags/New.lean` (the tagged statement only).
- New `PercLib/Area/Two.lean` and
  `PercLib/Area/Three.lean` (theorems only).

## Allowed inputs
`PercLib/Area/{File,Other}.lean`, `Other.lean`, `PercLib/Area/*`, `main`, `Nat.succ`, mathlib.

## Stop condition
Done.

## Hand-off
A pull request.
"""


def task(task_id, body=SECTIONS_OK, difficulty='easy', kind='interface', labels='[]',
         id_line=None):
    id_line = f'id: {task_id}' if id_line is None else id_line
    return (f'---\n{id_line}\ntitle: Title of {task_id}\ndifficulty: {difficulty}\n'
            f'kind: {kind}\nlabels: {labels}\n---\n\n# Title\n{body}')


class BoardTest(unittest.TestCase):
    def setUp(self):
        self._dir = tempfile.TemporaryDirectory()
        self.root = Path(self._dir.name)
        for d in ('open', 'claimed', 'done', 'areas'):
            (self.root / 'tasks' / d).mkdir(parents=True)
        self.write('tasks/README.md', '| Area | Owner | Map |\n|---|---|---|\n'
                   '| Big area | Someone | [`areas/big.md`](areas/big.md) |\n')
        self.write('PercLib/Area/File.lean', '')
        self.write('PercLib/Area/Other.lean', '@[simp, tag "BBBB"] theorem t : True := trivial\n')
        self.write('wiki/articles/art-one.md',
                   '<a id="tag-AAAA" data-assertion="x"></a>\n<a id="tag-BBBB"></a>\n')
        self.write('wiki/articles/taken.md', '<a id="tag-CCCC" data-assertion="x"></a>\n')
        self.write('tasks/areas/big.md',
                   '# Map\n\nProse naming [other](../../wiki/articles/art-one.md).\n\n'
                   '| Article | Tags |\n|---|---|\n'
                   '| [taken](../../wiki/articles/taken.md) | `CCCC` |\n')

    def tearDown(self):
        self._dir.cleanup()

    def write(self, rel, text):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding='utf-8')

    def assertClean(self):
        self.assertEqual(check(self.root), ([], []))

    def test_valid_board_is_clean(self):
        self.write('tasks/open/good.md', task('good', labels='[good-first-task]'))
        self.write('tasks/claimed/short.md', task('short', body='Being done.', kind='proof-only'))
        self.write('tasks/done/old.md', task('old', body='Done.', labels='\n  - x'))
        self.assertClean()
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(main(['--root', str(self.root)]), 0)

    def test_rule1_front_matter_and_sections(self):
        self.write('tasks/open/a.md', task('a', id_line='id: other', difficulty='trivial',
                                           kind='lemma', labels='good-first-task'))
        self.write('tasks/open/b.md', task('b', body=SECTIONS_OK.replace('## Hand-off', '## X')))
        self.write('tasks/claimed/c.md', '# No front matter\n')
        self.write('tasks/done/d.md', task('d', body='Short stub, no sections.'))
        errors, _ = check(self.root)
        self.assertTrue(all(': rule 1: ' in e for e in errors), errors)
        joined = '\n'.join(errors)
        for needle in ("tasks/open/a.md: rule 1: id 'other' differs",
                       "tasks/open/a.md: rule 1: difficulty 'trivial'",
                       "tasks/open/a.md: rule 1: kind 'lemma'",
                       'tasks/open/a.md: rule 1: labels missing or not a list',
                       'tasks/open/b.md: rule 1: missing section "Hand-off"',
                       'tasks/claimed/c.md: rule 1: no front-matter block'):
            self.assertIn(needle, joined)
        self.assertNotIn('tasks/done/d.md', joined)
        with contextlib.redirect_stdout(io.StringIO()) as out:
            self.assertEqual(main(['--root', str(self.root)]), 1)
        self.assertEqual(len(out.getvalue().splitlines()), len(errors))

    def test_rule2_duplicate_id(self):
        self.write('tasks/open/dup.md', task('dup'))
        self.write('tasks/done/dup.md', task('dup', body='Done.'))
        self.assertEqual(check(self.root)[0], ["tasks: rule 2: id 'dup' is in open, done"])

    def test_rule3_paths(self):
        body = (SECTIONS_OK
                .replace('`PercLib/Area/File.lean` (append only)',
                         '`PercLib/Area/Missing.lean` (append only)')
                .replace('{File,Other}', '{File,Gone}')
                .replace('`PercLib/Area/*`', '`PercLib/Nowhere/*`'))
        self.write('tasks/open/p.md', task('p', body=body))
        errors, _ = check(self.root)
        self.assertEqual(errors, [
            'tasks/open/p.md: rule 3: path `PercLib/Area/Missing.lean` under "Owned files" '
            'does not exist and is not marked new',
            'tasks/open/p.md: rule 3: path `PercLib/Area/{File,Gone}.lean` under "Allowed '
            'inputs" does not exist and is not marked new',
            'tasks/open/p.md: rule 3: path `PercLib/Nowhere/*` under "Allowed inputs" '
            'does not exist and is not marked new'])

    def test_rule4_tags(self):
        body = SECTIONS_OK.replace('**AAAA**', '**AAAA**, **BBBB** and **ZZZZ**')
        self.write('tasks/open/t.md', task('t', body=body))
        errors, warnings = check(self.root)
        self.assertEqual(errors, ['tasks/open/t.md: rule 4: tag ZZZZ has no anchor tag-ZZZZ '
                                  'under wiki/articles/'])
        self.assertEqual(warnings, ['tasks/open/t.md: rule 4: tag BBBB is already attached '
                                    'in Lean: possibly done'])
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(main(['--root', str(self.root)]), 1)
        # A task that says it re-states the tag is not reported; a warning alone exits 0.
        body = SECTIONS_OK.replace('**AAAA**', '**BBBB**')
        self.write('tasks/open/t.md', task('t', body=body))
        self.assertEqual(check(self.root), ([], ['tasks/open/t.md: rule 4: tag BBBB is '
                                                 'already attached in Lean: possibly done']))
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(main(['--root', str(self.root)]), 0)
        self.write('tasks/open/t.md', task('t', body=body.replace(
            'The statement.', 'Re-state it with an extra clause.')))
        self.assertClean()

    def test_rule5_areas_taken(self):
        body = SECTIONS_OK.replace('**AAAA** (article `art-one`)', '**CCCC**')
        self.write('tasks/open/a.md', task('a', body=body))
        self.write('tasks/open/b.md', task('b', body=SECTIONS_OK.replace(
            'The statement.', 'See `wiki/articles/taken.md`.')))
        expected = ['tasks/open/{}.md: rule 5: targets article(s) taken of the taken area '
                    'big (tasks/areas/big.md)'.format(x) for x in 'ab']
        self.assertEqual(check(self.root), (expected, []))
        # Naming the area as a shared prerequisite lifts the restriction.
        self.write('tasks/open/a.md', task('a', body=body.replace(
            'The statement.', 'A shared prerequisite of the Big area.')))
        self.assertEqual(check(self.root), (expected[1:], []))
        # Articles mentioned only outside Goal and Target (or outside the map's tables) are
        # not targets.
        self.write('tasks/open/b.md', task('b', body=SECTIONS_OK.replace(
            'mathlib.', 'mathlib, `wiki/articles/taken.md`.')))
        self.assertClean()


class RealBoardTest(unittest.TestCase):
    def test_real_repository(self):
        errors, warnings = check(REPO)
        print(f'\ncheck_tasks on {REPO}: {len(errors)} error(s), {len(warnings)} warning(s)')
        for line in errors:
            print(f'  error: {line}')
        for line in warnings:
            print(f'  warning: {line}')


if __name__ == '__main__':
    unittest.main()
