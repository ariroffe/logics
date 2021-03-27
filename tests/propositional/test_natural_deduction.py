import unittest

from logics.classes.propositional import Inference, Formula
from logics.classes.propositional.proof_theories import NaturalDeductionStep, NaturalDeductionRule
from logics.utils.parsers import classical_parser
from logics.instances.propositional.natural_deduction import classical_natural_deduction_system as nd_system


class TestClassicalNaturalDeductionSystem(unittest.TestCase):
    def test_natural_deduction_rule(self):
        """Test overriding of index and len methods in NaturalDeductionRule"""
        rule = NaturalDeductionRule([
            '(...)',
            NaturalDeductionStep(Formula(['→', ['A'], ['B']])),
            '(...)',
            NaturalDeductionStep(Formula(['B']), 'E→', [0, 1])
        ])
        self.assertEqual(rule.index(NaturalDeductionStep(Formula(['B']), 'E→', [0, 1])), 1)
        self.assertEqual(len(rule), 2)

    def test_nd_system(self):
        """Test the method that tells if a step is a correct application of a rule"""

        # A correct derivation
        deriv = classical_parser.parse_derivation(
            """p; premise
            (p → q); premise
            q; E→; [1, 0]; []
            p ∧ q; I∧; [0, 2]; []""",
            natural_deduction=True)

        # Check is application of the correct rule, and a different rule
        self.assertTrue(nd_system.is_correct_application(deriv, 2, nd_system.rules['E→']))
        self.assertFalse(nd_system.is_correct_application(deriv, 2, nd_system.rules['E∧2']))
        self.assertTrue(nd_system.is_correct_application(deriv, 3, nd_system.rules['I∧']))
        self.assertFalse(nd_system.is_correct_application(deriv, 3, nd_system.rules['E→']))

        # Check is correct derivation of the correct and an incorrect inference
        i = Inference([Formula(['p']), Formula(['→', ['p'], ['q']])],
                      [Formula(['∧', ['p'], ['q']])])
        self.assertTrue(nd_system.is_correct_derivation(deriv, i))
        i2 = Inference([Formula(['p']), Formula(['→', ['p'], ['q']])],
                      [Formula(['∧', ['q'], ['p']])])
        self.assertFalse(nd_system.is_correct_derivation(deriv, i2))

        # Repeating steps should not alter the outcome (should print a warning)
        # deriv2_0 = classical_parser.parse_derivation(
        #     """p; supposition; []; [0]
        #     p; repetition; [0, 0]; [0]""",
        #     natural_deduction=True)
        # self.assertTrue(nd_system.is_correct_application(deriv2_0, 1, nd_system.rules['repetition']))

        # Test step in the future
        deriv2_1 = classical_parser.parse_derivation(
            """p; supposition; []; [0]
            p; repetition; [1]; [0]""",
            natural_deduction=True)
        deriv2_2 = classical_parser.parse_derivation(
            """p; supposition; []; [0]
            p; repetition; [2]; [0]""",
            natural_deduction=True)
        self.assertFalse(nd_system.is_correct_application(deriv2_1, 1, nd_system.rules['repetition']))
        self.assertFalse(nd_system.is_correct_application(deriv2_2, 1, nd_system.rules['repetition']))

        # -------------------------------------------------
        # Test incorrect use of suppositions

        # Using a step in a closed supposition
        deriv3_1 = classical_parser.parse_derivation(
            """p; supposition; []; [0]
            p; repetition; [0]; [0]
            (p → p); I→; [0, 1]; []
            p; E→; [2, 0]; []""",
            natural_deduction=True)
        # Check correct application of rep and I→
        self.assertTrue(nd_system.is_correct_application(deriv3_1, 1, nd_system.rules['repetition']))
        self.assertTrue(nd_system.is_correct_application(deriv3_1, 2, nd_system.rules['I→']))
        self.assertFalse(nd_system.is_correct_application(deriv3_1, 3, nd_system.rules['E→']))

        # Closing a supposition with a rule that does not close
        deriv3_2 = classical_parser.parse_derivation('''
            p; premise
            p; supposition; []; [1]
            p; repetition; [0]; [1]
            (p ∨ q); I∨1; [0]; []''',
            natural_deduction=True)
        self.assertFalse(nd_system.is_correct_application(deriv3_2, 3, nd_system.rules['I∨1']))

        # Closing two suppositions at once
        deriv3_3 = classical_parser.parse_derivation(
            """p; supposition; []; [0]
            p; supposition; [0]; [0, 1]
            (p → p); I→; [0, 1]; []""",
            natural_deduction=True)
        self.assertFalse(nd_system.is_correct_application(deriv3_3, 2, nd_system.rules['I→']))

        # Not closing a supposition with a rule that does close
        deriv3_4 = classical_parser.parse_derivation(
            """p; supposition; []; [0]
            p; repetition; [0]; [0]
            (p → p); I→; [0, 1]; [0]""",
            natural_deduction=True)
        self.assertFalse(nd_system.is_correct_application(deriv3_4, 2, nd_system.rules['I→']))

        # Incorrect opening of suppositions
        deriv3_5 = classical_parser.parse_derivation(
            """p; supposition; []; []""",
            natural_deduction=True)
        self.assertFalse(nd_system.is_correct_derivation(deriv3_5, None))
        deriv3_6 = classical_parser.parse_derivation(
            """p; premise; []; []
            q; supposition; []; [0]""",
            natural_deduction=True)
        self.assertFalse(nd_system.is_correct_derivation(deriv3_6, None))

        # -------------------------------------------------
        # A correct derivation using all the rules

        deriv4 = classical_parser.parse_derivation(
            """q; premise; []; []
            ~q; supposition; []; [1]
            ~q; repetition; [1]; [1]
            (q ∧ ~q); I∧; [0, 2]; [1]
            q; E∧1; [3]; [1]
            ⊥; E~; [1, 4]; [1]
            p; EFSQ; [5]; [1]
            ⊥; repetition; [5]; [1]
            ~~q; I~; [1, 7]; []
            q; ~~; [8]; []
            q; supposition; []; [10]
            q; repetition; [10]; [10]
            (q → q); I→; [10, 11]; []
            q; E→; [12, 9]; []
            (q ∨ p); I∨1; [13]; []
            (p → q); premise; []; []
            q; E∨; [14, 12, 15]; []
            """, natural_deduction=True)
        i3 = Inference([Formula(['q']), Formula(['→', ['p'], ['q']])],
                       [Formula(['q'])])
        self.assertTrue(nd_system.is_correct_derivation(deriv4, i3))

    def test_rule_order(self):
        # i1 is conjunction introduction
        i1 = Inference([Formula(['p']), Formula(['q'])],
                      [Formula(['∧', ['p'], ['q']])])

        # First derivation: standard one
        deriv1_1 = classical_parser.parse_derivation(
            """p; premise; []; []
            q; premise; []; []
            (p ∧ q); I∧; [0, 1]; []""",
            natural_deduction=True)
        self.assertTrue(nd_system.is_correct_derivation(deriv1_1, i1))

        # Second derivation: reverse on_steps order
        deriv1_2 = classical_parser.parse_derivation(
            """p; premise; []; []
            q; premise; []; []
            (p ∧ q); I∧; [1, 0]; []""",
            natural_deduction=True)
        self.assertFalse(nd_system.is_correct_derivation(deriv1_2, i1))

        i2 = Inference([Formula(['p']), Formula(['q'])],
                       [Formula(['∧', ['q'], ['p']])])

        # Third derivation: reverse the conjuncts
        deriv2_1 = classical_parser.parse_derivation(
            """p; premise; []; []
            q; premise; []; []
            (q ∧ p); I∧; [1, 0]; []""",
            natural_deduction=True)
        self.assertTrue(nd_system.is_correct_derivation(deriv2_1, i2))

        # Fourth derivation: reverse the conjuncts and the on_steps
        deriv2_2 = classical_parser.parse_derivation(
            """p; premise; []; []
            q; premise; []; []
            (q ∧ p); I∧; [0, 1]; []""",
            natural_deduction=True)
        self.assertFalse(nd_system.is_correct_derivation(deriv2_2, i2))


if __name__ == '__main__':
    unittest.main()
