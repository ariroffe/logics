import unittest

from logics.classes.predicate import PredicateFormula as Formula
from logics.utils.parsers.predicate_parser import classical_predicate_parser as parser
from logics.instances.predicate.natural_deduction import predicate_classical_natural_deduction_system as nd_system
from logics.classes.predicate.proof_theories.natural_deduction import PredicateNaturalDeductionStep, PredicateNaturalDeductionRule

class TestNaturalDeduction(unittest.TestCase):
    def setUp(self):
        pass

    def test_substitute_rule(self):
        # Existential intro (unary)
        deriv = parser.parse_derivation("""
            P(a); premise; []; []
            ∃x (P(x)); I∃; [0]; []
        """, natural_deduction=True)
        rule = nd_system.rules['I∃']
        new_rule = nd_system.substitute_rule(deriv, 1, rule)
        # New rule should be Pα / ∃x Px
        self.assertEqual(new_rule, PredicateNaturalDeductionRule([
            '(...)',
            PredicateNaturalDeductionStep(Formula(['P', 'α']), open_suppositions=[]),
            '(...)',
            PredicateNaturalDeductionStep(Formula(['∃', 'x', ['P', 'x']]), 'I∃', [0], open_suppositions=[])
        ]))

        # Existential intro (binary)
        deriv = parser.parse_derivation("""
            R(b, b); premise; []; []
            ∃x (R(x, x)); I∃; [0]; []
        """, natural_deduction=True)
        rule = nd_system.rules['I∃']
        new_rule = nd_system.substitute_rule(deriv, 1, rule)
        # New rule should be Rαα / ∃x Rxx
        self.assertEqual(new_rule, PredicateNaturalDeductionRule([
            '(...)',
            PredicateNaturalDeductionStep(Formula(['R', 'α', 'α']), open_suppositions=[]),
            '(...)',
            PredicateNaturalDeductionStep(Formula(['∃', 'x', ['R', 'x', 'x']]), 'I∃', [0], open_suppositions=[])
        ]))

        # Universal intro
        deriv = parser.parse_derivation("""
            R(b, a); premise; []; []
            ∀y (R(y, a)); I∃; [0]; []
        """, natural_deduction=True)
        rule = nd_system.rules['I∀']
        new_rule = nd_system.substitute_rule(deriv, 1, rule)
        # New rule should be Rαa / ∀y Rya
        self.assertEqual(new_rule, PredicateNaturalDeductionRule([
            '(...)',
            PredicateNaturalDeductionStep(Formula(['R', 'α', 'a']), open_suppositions=[]),
            '(...)',
            PredicateNaturalDeductionStep(Formula(['∀', 'y', ['R', 'y', 'a']]), 'I∀', [0], open_suppositions=[])
        ]))

    def test_is_correct_application(self):
        # Existential intro (unary)
        deriv = parser.parse_derivation("""
                P(a); premise; []; []
                ∃x (P(x)); I∃; [0]; []
            """, natural_deduction=True)
        self.assertTrue(nd_system.is_correct_application(deriv, 1, nd_system.rules['I∃']))

        # Existential intro (binary)
        deriv = parser.parse_derivation("""
                R(a, b); premise; []; []
                ∃y (R(a, y)); I∃; [0]; []
            """, natural_deduction=True)
        self.assertTrue(nd_system.is_correct_application(deriv, 1, nd_system.rules['I∃']))

        deriv = parser.parse_derivation("""
                R(a, b); premise; []; []
                ∃x (R(x, b)); I∃; [0]; []
            """, natural_deduction=True)
        self.assertTrue(nd_system.is_correct_application(deriv, 1, nd_system.rules['I∃']))

        deriv = parser.parse_derivation("""
                R(a, a); premise; []; []
                ∃x (R(x, x)); I∃; [0]; []
            """, natural_deduction=True)
        self.assertTrue(nd_system.is_correct_application(deriv, 1, nd_system.rules['I∃']))

        deriv = parser.parse_derivation("""
                R(a, b); premise; []; []
                ∃y (R(a, x)); I∃; [0]; []
            """, natural_deduction=True)
        self.assertFalse(nd_system.is_correct_application(deriv, 1, nd_system.rules['I∃']))
