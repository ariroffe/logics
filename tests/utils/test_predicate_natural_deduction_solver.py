import unittest

from logics.classes.predicate import PredicateFormula

from logics.utils.parsers.predicate_parser import classical_predicate_parser as parser
from logics.utils.solvers.first_order_natural_deduction import (
    Derivation,
    NaturalDeductionStep,
    first_order_natural_deduction_solver as solver,
    universal_intro_heuristic,
    existential_elim_heuristic,
)


class TestPredicateNaturalDeductionSolver(unittest.TestCase):
    def setUp(self):
        pass

    def test_get_formulae_to_add(self):
        subst_dict = {'χ': 'x', 'A': PredicateFormula(['P', 'x'])}
        fs = solver._get_formulae_to_add(PredicateFormula(['[α/χ]A']), subst_dict)
        self.assertEqual(fs, [
            PredicateFormula(['P', 'a']),
            PredicateFormula(['P', 'b']),
            PredicateFormula(['P', 'c']),
            PredicateFormula(['P', 'd']),
            PredicateFormula(['P', 'e'])
        ])

        subst_dict = {'χ': 'x', 'A': PredicateFormula(['R', 'x', 'a'])}
        fs = solver._get_formulae_to_add(PredicateFormula(['[α/χ]A']), subst_dict)
        self.assertEqual(fs, [
            PredicateFormula(['R', 'a', 'a']),
            PredicateFormula(['R', 'b', 'a']),
            PredicateFormula(['R', 'c', 'a']),
            PredicateFormula(['R', 'd', 'a']),
            PredicateFormula(['R', 'e', 'a'])
        ])

        subst_dict = {'χ': 'x', 'A': PredicateFormula(['R', 'x', 'x'])}
        fs = solver._get_formulae_to_add(PredicateFormula(['[α/χ]A']), subst_dict)
        self.assertEqual(fs, [
            PredicateFormula(['R', 'a', 'a']),
            PredicateFormula(['R', 'b', 'b']),
            PredicateFormula(['R', 'c', 'c']),
            PredicateFormula(['R', 'd', 'd']),
            PredicateFormula(['R', 'e', 'e'])
        ])

    def test_apply_simplification_rules(self):
        deriv = parser.parse_derivation("""
            ∀x (P(x)); premise; []; []
        """, natural_deduction=True)
        new_deriv = solver._apply_simplification_rules(deriv, goal=PredicateFormula(['R', 'a', 'b']))
        solution = parser.parse_derivation("""
            ∀x (P(x)); premise; []; []
            P(a); E∀; [0]; []
            P(b); E∀; [0]; []
            P(c); E∀; [0]; []
            P(d); E∀; [0]; []
            P(e); E∀; [0]; []
        """, natural_deduction=True)
        self.assertEqual(new_deriv, solution)

        deriv = parser.parse_derivation("""
            ∀x (R(x, x)); premise; []; []
        """, natural_deduction=True)
        new_deriv = solver._apply_simplification_rules(deriv, goal=PredicateFormula(['R', 'a', 'b']))
        solution = parser.parse_derivation("""
            ∀x (R(x, x)); premise; []; []
            R(a, a); E∀; [0]; []
            R(b, b); E∀; [0]; []
            R(c, c); E∀; [0]; []
            R(d, d); E∀; [0]; []
            R(e, e); E∀; [0]; []
        """, natural_deduction=True)
        self.assertEqual(new_deriv, solution)

        deriv = parser.parse_derivation("""
            ∀x (R(x, a)); premise; []; []
        """, natural_deduction=True)
        new_deriv = solver._apply_simplification_rules(deriv, goal=PredicateFormula(['R', 'a', 'b']))
        solution = parser.parse_derivation("""
            ∀x (R(x, a)); premise; []; []
            R(a, a); E∀; [0]; []
            R(b, a); E∀; [0]; []
            R(c, a); E∀; [0]; []
            R(d, a); E∀; [0]; []
            R(e, a); E∀; [0]; []
        """, natural_deduction=True)
        self.assertEqual(new_deriv, solution)

    def test_get_arbitrary_constant(self):
        deriv = parser.parse_derivation("""
            P(a); premise; []; []
            P(b); premise; []; []
            ~∀x (P(x)); premise; []; []
            ~∀x (P(x) ∧ P(c)); premise; []; []
            ~∃x (P(d)) ∧ P(e); premise; []; []
        """, natural_deduction=True)
        self.assertEqual(solver.get_arbitrary_constant(solver.language, deriv[:0]), 'a')
        self.assertEqual(solver.get_arbitrary_constant(solver.language, deriv[:1]), 'b')
        self.assertEqual(solver.get_arbitrary_constant(solver.language, deriv[:2]), 'c')
        self.assertEqual(solver.get_arbitrary_constant(solver.language, deriv[:-1]), 'd')
        self.assertIs(solver.get_arbitrary_constant(solver.language, deriv), None)

    def test_replace_derived_rules(self):
        # NegUniv
        deriv = parser.parse_derivation("""
                ~∀x (P(x)); premise; []; []
                ∃x (~P(x)); NegUniv; [0]; []
            """, natural_deduction=True)
        new_deriv = solver._replace_derived_rules(deriv, solver.derived_rules_derivations)
        solution = parser.parse_derivation("""
            ~∀x (P(x)); premise; []; []
            ~∃x (~P(x)); supposition; []; [1]
            ~P(a); supposition; []; [1, 2]
            ∃x (~P(x)); I∃; [2]; [1, 2]
            ⊥; E~; [1, 3]; [1, 2]
            ~~P(a); I~; [2, 4]; [1]
            P(a); DN; [5]; [1]
            ∀x (P(x)); I∀; [6]; [1]
            ⊥; E~; [1, 3]; [1]
            ~~∃x (~P(x)); I~; [1, 8]; []
            ∃x (~P(x)); DN; [9]; []
        """, natural_deduction=True)
        self.assertEqual(new_deriv, solution)

        # NegExist (unary predicate)
        deriv = parser.parse_derivation("""
                ~∃x (P(x)); premise; []; []
                ∀x (~P(x)); NegExist; [0]; []
            """, natural_deduction=True)
        new_deriv = solver._replace_derived_rules(deriv, solver.derived_rules_derivations)
        solution = parser.parse_derivation("""
            ~∃x (P(x)); premise; []; []
            P(a); supposition; []; [1]
            ∃x (P(x)); I∃; [1]; [1]
            ⊥; E~; [0, 2]; [1]
            ~P(a); I~; [1, 3]; []
            ∀x (~P(x)); I∀; [4]; []
        """, natural_deduction=True)
        self.assertEqual(new_deriv, solution)

        # NegExist (binary predicate)
        deriv = parser.parse_derivation("""
            ~∃x (R(x, a)); premise; []; []
            ∀x (~R(x, a)); NegExist; [0]; []
        """, natural_deduction=True)
        new_deriv = solver._replace_derived_rules(deriv, solver.derived_rules_derivations)
        solution = parser.parse_derivation("""
            ~∃x (R(x, a)); premise; []; []
            R(b, a); supposition; []; [1]
            ∃x (R(x, a)); I∃; [1]; [1]
            ⊥; E~; [0, 2]; [1]
            ~R(b, a); I~; [1, 3]; []
            ∀x (~R(x, a)); I∀; [4]; []
        """, natural_deduction=True)
        self.assertEqual(new_deriv, solution)

    def test_existential_intro_heuristic(self):
        inf = parser.parse('P(a) / ∃x (P(x))')
        derivation = Derivation([NaturalDeductionStep(content=p, justification='premise') for p in inf.premises])
        derivation = solver._solve_derivation(derivation, inf.conclusion)
        deriv = parser.parse_derivation("""
            P(a); premise; []; []
            ∃x (P(x)); I∃; [0]; []
        """, natural_deduction=True)
        self.assertEqual(derivation, deriv)

    def test_universal_intro_heuristic(self):
        # is_arbitary_ct method
        deriv = parser.parse_derivation("""
            R(a, a); premise; []; []
            R(b, b); ~~; [0]; []
        """, natural_deduction=True)
        self.assertFalse(universal_intro_heuristic._is_arbitrary_constant('a', parser.parse('R(c,x)'), deriv))
        self.assertTrue(universal_intro_heuristic._is_arbitrary_constant('b', parser.parse('R(c,x)'), deriv))
        self.assertFalse(universal_intro_heuristic._is_arbitrary_constant('c', parser.parse('R(c,x)'), deriv))
        self.assertTrue(universal_intro_heuristic._is_arbitrary_constant('d', parser.parse('R(c,x)'), deriv))

        # Test with an inference
        inf = parser.parse('∀x (P(x)), P(a) / ∀y (P(y))')
        derivation = Derivation([NaturalDeductionStep(content=p, justification='premise') for p in inf.premises])
        derivation = solver._solve_derivation(derivation, inf.conclusion)
        deriv = parser.parse_derivation("""
            ∀x (P(x)); premise; []; []
            P(a); premise; []; []
            P(b); E∀; [0]; []
            P(c); E∀; [0]; []
            P(d); E∀; [0]; []
            P(e); E∀; [0]; []
            ∀y (P(y)); I∀; [2]; []
        """, natural_deduction=True)
        self.assertEqual(derivation, deriv)

    def test_existential_elim_heuristic(self):
        # get_first_untried_existential_idx method
        deriv = parser.parse_derivation("""
            ∃x (P(x)); premise; []; []
            P(a); supposition; []; [1]
            ∃y (P(y)); ~~; []; [1]
            ∃y (P(y)); I∃; []; []
        """, natural_deduction=True)
        self.assertEqual(existential_elim_heuristic.get_first_untried_existential_idx(deriv, []), 0)
        self.assertEqual(existential_elim_heuristic.get_first_untried_existential_idx(deriv, [0]), 3)
        self.assertEqual(existential_elim_heuristic.get_first_untried_existential_idx(deriv, [0, 3]), None)

        # Test with an inference
        inf = parser.parse('∃x (P(x)), P(a) / ∃y (P(y))')
        derivation = Derivation([NaturalDeductionStep(content=p, justification='premise') for p in inf.premises])
        derivation = solver._solve_derivation(derivation, inf.conclusion)
        deriv = parser.parse_derivation("""
            ∃x (P(x)); premise; []; []
            P(a); premise; []; []
            P(b); supposition; []; [2]
            ∃y (P(y)); I∃; [1]; [2]
            P(b) → ∃y (P(y)); I→; [2, 3]; [] 
            ∃y (P(y)); E∃; [0, 4]; []
        """, natural_deduction=True)
        self.assertEqual(derivation, deriv)
