import unittest

from logics.classes.propositional import Inference, Formula
from logics.utils.parsers import classical_parser
from logics.instances.propositional.axiom_systems import classical_logic_axiom_system


class TestClassicalAxiomSystem(unittest.TestCase):
    def test_axioms_as_derivations(self):
        i1 = Inference([], [Formula(['→', ['p'], ['→', ['p'], ['p']]])])
        deriv1 = classical_parser.parse_derivation("""p → (p → p); ax1""")
        self.assertTrue(classical_logic_axiom_system.is_correct_derivation(deriv1, i1))

        i2 = Inference([], [Formula(['→', ['p'], ['→', ['q'], ['p']]])])
        deriv2 = classical_parser.parse_derivation("""p → (q → p); ax1""")
        self.assertTrue(classical_logic_axiom_system.is_correct_derivation(deriv2, i2))

        i3 = Inference([], [Formula(['→', ['p'], ['→', ['→', ['p'], ['p']], ['p']]])])
        deriv3 = classical_parser.parse_derivation("""p → ((p → p) → p); ax1""")
        self.assertTrue(classical_logic_axiom_system.is_correct_derivation(deriv3, i3))

        i4 = Inference([], [Formula(['→', ['p'], ['→', ['p'], ['q']]])])
        deriv4 = classical_parser.parse_derivation("""p → (p → q); ax1""")
        self.assertFalse(classical_logic_axiom_system.is_correct_derivation(deriv4, i4))

        correct, error_list = classical_logic_axiom_system.is_correct_derivation(deriv4, i4, return_error_list=True)
        self.assertEqual(error_list[0], "Step 0: ['→', ['p'], ['→', ['p'], ['q']]] was marked as ax1, "
                                        "but is not an instance of that axiom")

    def test_complex_derivations(self):
        # Demostration of / p → p
        deriv = classical_parser.parse_derivation("""p → ((p → p) → p); ax1
        (p → ((p → p) → p)) → ((p → (p → p)) → (p → p)); ax2
        p → (p → p); ax1
        ((p → (p → p)) → (p → p)); mp; [0,1]
        p → p; mp; [2,3]""")
        i = Inference([], [Formula(['→', ['p'], ['p']])])
        self.assertTrue(classical_logic_axiom_system.is_correct_derivation(deriv, i))

        # Use 'axiom' instead of the name of the specific axiom
        deriv2 = classical_parser.parse_derivation("""p → ((p → p) → p); axiom
                (p → ((p → p) → p)) → ((p → (p → p)) → (p → p)); axiom
                p → (p → p); axiom
                ((p → (p → p)) → (p → p)); mp; [0,1]
                p → p; mp; [2,3]""")
        self.assertTrue(classical_logic_axiom_system.is_correct_derivation(deriv2, i))

        # An incorrect derivation
        deriv3 = classical_parser.parse_derivation("""p → ((p → p) → p); axiom
                        (p → ((p → p) → p)) → ((p → (p → p)) → (p → p)); axiom
                        p → p; mp; [0,1]""")
        self.assertFalse(classical_logic_axiom_system.is_correct_derivation(deriv3, i))

        correct, error_list = classical_logic_axiom_system.is_correct_derivation(deriv3, i, return_error_list=True)
        self.assertEqual(error_list[0], "Step 2: ['→', ['p'], ['p']] was marked as mp, "
                                        "but it is not a correct application of that rule")


if __name__ == '__main__':
    unittest.main()
