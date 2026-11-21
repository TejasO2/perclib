#!/usr/bin/env python3
"""Unit tests of the forbidden-construct scan (`check_forbidden.py`). Standard library only."""
import unittest
from check_forbidden import check_file

REL = 'PercLib/Area/F.lean'


def flagged(text, rel=REL):
    return bool(check_file(rel, text))


class ForbiddenScanTests(unittest.TestCase):
    def test_audit_probe_lines(self):
        # The three probe lines that passed the scan before the fix.
        for line in ['theorem a : True := trivial #eval! IO.FS.writeFile "p" "hi"',
                     'theorem a : True := let «x--» := 0; trivial #eval 1',
                     'theorem a : True := let «x--» := 0; trivial axiom bad : False']:
            with self.subTest(line=line):
                self.assertTrue(flagged(line))

    def test_eval_variants(self):
        for cmd in ['#eval', '#eval!', '#eval?', '#evalFoo']:
            with self.subTest(cmd=cmd):
                self.assertTrue(flagged(f'theorem a : True := trivial\n{cmd} 1\n'))
                self.assertTrue(flagged(f'theorem a : True := trivial {cmd} 1\n'))

    def test_guillemets(self):
        for text in ['theorem a : True := let «y/-» := 0; trivial axiom bad : False',
                     'theorem a : True := let «y\"» := 0; trivial axiom bad : False',
                     'theorem a : True := let x.«y--».z := 0; trivial #eval 1',
                     'theorem «sorry» : True := trivial',
                     'theorem a : True := let «x := 0; trivial']:  # unterminated «
            with self.subTest(text=text):
                self.assertTrue(flagged(text))

    def test_char_literals(self):
        # `'"'` and `'«'` are character literals; neither opens a string or identifier.
        for text in ["def c : Char := '\"'\naxiom bad : False\ndef d : Char := '\"'\n",
                     "def c : Char := '«'\naxiom bad : False\ndef d : Char := '»'\n",
                     "def c : Nat := 2'\"'\naxiom bad : False\ndef d : Char := '\"'\n"]:
            with self.subTest(text=text):
                self.assertTrue(flagged(text))
        # After an identifier, `'` is part of it: `x'"…"` is `x'` followed by a string.
        self.assertFalse(flagged('def x\' : Nat := 1\ndef c := x\'" axiom "\n'))

    def test_interpolated_strings_refused(self):
        for text in ['def t : String := s!"{ "a" ++ toString (by exact (sorry : Nat)) }"',
                     'def t : String := s! "{1}"', 'def t : String := "{"']:
            with self.subTest(text=text):
                self.assertTrue(flagged(text))
        self.assertFalse(flagged('def t : String := "no braces \\" here"'))

    def test_simprocs(self):
        for text in ['simproc reduceFoo (Foo _) := fun e => return .continue',
                     'dsimproc reduceFoo (Foo _) := fun e => return .continue',
                     'simproc_decl reduceFoo (Foo _) := fun e => return .continue',
                     'attribute [simproc] reduceFoo']:
            with self.subTest(text=text):
                self.assertTrue(flagged(text))

    def test_code_registering_attributes(self):
        for text in ['@[norm_num _ + _] def evalAdd : NormNumExt := sorryFree',
                     '@[positivity _ * _] def evalMul : PositivityExt := x',
                     '@[delab app.Foo] def delabFoo : Delab := x',
                     '@[app_unexpander Foo] def unexpandFoo : Unexpander := x',
                     '@[simp, scoped norm_num Nat.succ _] def f : Nat := 0',
                     '@[Mathlib.Meta.Positivity.«positivity» _] def f : Nat := 0',
                     'attribute [local norm_num Nat.succ _] evalSucc',
                     'attribute [positivity Real.exp _] evalExp',
                     '@[aesop safe (rule_sets := [Foo]), norm_num _] def f : Nat := 0']:
            with self.subTest(text=text):
                self.assertTrue(flagged(text))

    def test_tactics_with_attribute_names_pass(self):
        ok = '''module
public import Mathlib.Tactic
/-! # Ordinary proofs -/
@[simp] theorem two_pos' : (0 : ℝ) < 2 := by norm_num
theorem sq_nonneg' (x : ℝ) : 0 ≤ x ^ 2 := by positivity
@[simp, grind =] theorem f_eq (x : ℕ) : x + 0 = x := by
  norm_num [Nat.add_zero]
theorem g (x : ℝ) (h : 0 < x) : 0 < x * 2 := by
  have h' : (0 : ℝ) < 2 := by norm_num
  nlinarith [h, h']
attribute [simp] two_pos'
attribute [local instance] Classical.propDecidable in
theorem k : True := by simp only [ite_true]; trivial
theorem chars : 'A' ≤ 'Z' ∧ ('\\'' : Char) = '\\'' := by decide
theorem names (h₁ : 1 = 1) (hα' : True) : True := by norm_num at h₁ ⊢
-- a comment mentioning sorry, #eval!, @[norm_num] and «unterminated
/- a block comment: axiom, @[positivity], "unbalanced quote -/
'''
        self.assertEqual(check_file(REL, ok), [])

    def test_existing_rules_kept(self):
        for text in ['theorem a : True := by sorry', 'theorem a : True := by native_decide',
                     'set_option maxHeartbeats 0 in\ntheorem a : True := trivial',
                     'set_option linter.unusedVariables false',
                     'unsafe def f : Nat := 0', '@[implemented_by g] def f : Nat := 0',
                     'set_option «debug».skipKernelTC true']:
            with self.subTest(text=text):
                self.assertTrue(flagged(text))
        self.assertFalse(flagged('set_option maxRecDepth 2000 in\ntheorem a : True := trivial'))
        self.assertFalse(flagged('syntax (name := tag) "tag " str : attr\ninitialize x : Nat ← pure 0',
                                 'PercLib/Meta/Tag.lean'))


if __name__ == '__main__':
    unittest.main()
