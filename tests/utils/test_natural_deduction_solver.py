import unittest

from logics.classes.exceptions import SolverError
from logics.utils.parsers import classical_parser
from logics.classes.propositional.proof_theories import Derivation, NaturalDeductionStep
from logics.utils.solvers import classical_natural_deduction_solver as solver, classical_natural_deduction_solver2 as solver2
from logics.utils.formula_generators.generators_biased import random_formula_generator
from logics.instances.propositional.languages import classical_infinite_language_with_sent_constants_nobiconditional \
    as cl_language
from logics.instances.propositional.languages import classical_infinite_language_nobiconditional
from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics
from logics.instances.propositional.natural_deduction import classical_natural_deduction_system as nd_system
from logics.instances.propositional.natural_deduction import classical_natural_deduction_system2 as nd_system2


class TestNaturalDeductionSolver(unittest.TestCase):
    def setUp(self):
        # Elimination rules (2nd function)
        self.conjunction_elimination = classical_parser.parse('p ∧ q / p')
        self.conditional_elimination = classical_parser.parse('p, p → q / q')
        self.modus_tollens = classical_parser.parse('~q, p → q / ~p')
        self.disjunction_elimination = classical_parser.parse('p ∨ q, p → r, q → r / r')
        self.double_negation = classical_parser.parse('~~p / p')
        self.de_morgan = classical_parser.parse('~(p ∨ q) / ~p ∧ ~q')
        self.de_morgan2 = classical_parser.parse('~(p ∧ q) / ~p ∨ ~q')
        self.conditional_negation = classical_parser.parse('~(p → q) / p')
        self.conditional_negation2 = classical_parser.parse('~(p → q) / ~q')
        self.negation_elimination = classical_parser.parse('p, ~p / ⊥')
        self.disjunctive_syllogism = classical_parser.parse('p ∨ q, ~p / q')
        self.disjunctive_syllogism2 = classical_parser.parse('p ∨ q, ~q / p')
        self.disjunctive_syllogism3 = classical_parser.parse('p ∨ ~q, q / p')

        self.derived_rules = [self.de_morgan2, self.de_morgan, self.conditional_negation, self.conditional_negation2,
                              self.modus_tollens, self.disjunctive_syllogism, self.disjunctive_syllogism2,
                              self.disjunctive_syllogism3]

    def test_is_in_closed_supposition(self):
        self.assertFalse(solver._is_in_closed_supposition([], []))
        self.assertFalse(solver._is_in_closed_supposition([1], [1]))
        self.assertFalse(solver._is_in_closed_supposition([1], [1,2]))
        self.assertTrue(solver._is_in_closed_supposition([1, 2], [1]))
        self.assertTrue(solver._is_in_closed_supposition([1], []))

    def test_get_step_of_formula(self):
        deriv = classical_parser.parse_derivation("""
            ⊥; premise; []; []
            p; supposition; []; [1]
            p; premise; []; []
            (p ∧ q); I∧; [1, 0]; []
        """, natural_deduction=True)
        step = solver._get_step_of_formula(classical_parser.parse('⊥'), deriv, deriv[-1].open_suppositions)
        self.assertEqual(step, 0)

        step = solver._get_step_of_formula(classical_parser.parse('p'), deriv, deriv[-1].open_suppositions)
        self.assertEqual(step, 2)

        step = solver._get_step_of_formula(classical_parser.parse('p'), deriv, [1])
        self.assertEqual(step, 1)

        step = solver._get_step_of_formula(classical_parser.parse('q'), deriv, deriv[-1].open_suppositions)
        self.assertIs(step, None)

        step = solver._get_step_of_formula(classical_parser.parse('p ∧ q'), deriv, deriv[-1].open_suppositions)
        self.assertEqual(step, 3)

    def test_solver_heuristics_repetition(self):
        # Should repeat q inside the conditional
        inf = classical_parser.parse('p, q / p → q')
        deriv = Derivation([NaturalDeductionStep(content=p, justification='premise') for p in inf.premises])
        deriv = solver._solve_derivation(deriv, inf.conclusion)
        solution = classical_parser.parse_derivation("""
            p; premise; []; []
            q; premise; []; []
            p; supposition; []; [2]
            q; repetition; [1]; [2]
            p → q; I→; [2, 3]; []
        """, natural_deduction=True)
        self.assertEqual(deriv, solution)

        # Should get the second conjunct from the premises
        inf = classical_parser.parse('(p ∧ p), q / p ∧ q')
        deriv = Derivation([NaturalDeductionStep(content=p, justification='premise') for p in inf.premises])
        deriv = solver._solve_derivation(deriv, inf.conclusion)
        solution = classical_parser.parse_derivation("""
            p ∧ p; premise; []; []
            q; premise; []; []
            p; E∧1; [0]; []
            p ∧ q; I∧; [2, 1]; []
        """, natural_deduction=True)
        self.assertEqual(deriv, solution)

    def test_not_use_closed_sups(self):
        inf = classical_parser.parse('/(p → p) ∧ (p ∨ ~p)')
        deriv = Derivation([NaturalDeductionStep(content=p, justification='premise') for p in inf.premises])
        deriv = solver._solve_derivation(deriv, inf.conclusion)
        # steps 0 and 1 are a supposition and a repetition, 3 is a conditional intro
        # See that 0 and 1 are not used again after that
        for step in deriv[3:]:
            self.assertNotIn(0, step.on_steps)
            self.assertNotIn(1, step.on_steps)

    def test_solver_noclean(self):
        # Rules in the first function
        efsq = classical_parser.parse('⊥ / p')
        conjunction_introduction = classical_parser.parse('p1 ∧ p2, p3 ∧ p4 / p2 ∧ p3')
        disjunction_introduction = classical_parser.parse('p / p ∨ q')
        reductio = classical_parser.parse('p → (q ∧ ~q) / ~p')
        repetitions1 = classical_parser.parse('p / p ∧ p')
        repetitions2 = classical_parser.parse('/ p → p')

        inferences = [efsq, conjunction_introduction, disjunction_introduction, reductio, repetitions1, repetitions2]
        inferences.extend(self.derived_rules)

        for inference in inferences:
            derivation = Derivation([NaturalDeductionStep(content=p, justification='premise') for p in inference.premises])
            try:
                derivation = solver._solve_derivation(derivation, inference.conclusion)
                # print(classical_parser.unparse(inference))
                # derivation.print_derivation(classical_parser)
                # print('')
            except SolverError:
                self.fail(f"SolverError for inference '{classical_parser.unparse(inference)}'")

        conj = classical_parser.parse('p, q, r / (q → p) ∧ (r → p)')
        try:
            derivation = Derivation([NaturalDeductionStep(content=p, justification='premise') for p in conj.premises])
            derivation = solver._solve_derivation(derivation, conj.conclusion)
            # derivation.print_derivation(classical_parser)
        except SolverError:
            self.fail(f"SolverError for inference 'p, q, r / (q → p) ∧ (r → p)'")

    def test_delete_unused_steps(self):
        inference = classical_parser.parse('((p ∧ q) ∧ (q ∧ r)) / r')
        derivation = Derivation([NaturalDeductionStep(content=p, justification='premise') for p in inference.premises])
        derivation = solver._solve_derivation(derivation, inference.conclusion)
        # print(derivation)
        # print(solver._get_used_steps(derivation, inference))

        used_steps = solver._get_used_steps(derivation, inference)
        derivation = solver._delete_unused_steps(derivation, used_steps)
        # print(derivation)

    def test_replace_derived_rules(self):
        for inf in self.derived_rules:
            derivation = Derivation([NaturalDeductionStep(content=p, justification='premise') for p in inf.premises])
            derivation = solver._solve_derivation(derivation, inf.conclusion)
            # print('ORIGINAL\n', derivation)

            derivation = solver._replace_derived_rules(derivation, solver.derived_rules_derivations)
            # print('REPLACED\n', derivation)
            # print('\n')

            derivation2 = Derivation([NaturalDeductionStep(content=p, justification='premise') for p in inf.premises])
            derivation2 = solver2._solve_derivation(derivation2, inf.conclusion)
            # print('ORIGINAL\n', derivation2)

            derivation2 = solver2._replace_derived_rules(derivation, solver2.derived_rules_derivations)
            # print('REPLACED\n', derivation2)
            # print('\n')

    def test_with_generator(self):
        # Test with valid arguments and see that they are solved correctly
        unsolved = 0
        for _ in range(1000):
            inf = random_formula_generator.random_valid_inference(num_premises=2, num_conclusions=1,
                                                                  max_depth=3, atomics=['p', 'q', 'r'],
                                                                  language=cl_language,
                                                                  validity_apparatus=classical_mvl_semantics)
            could_solve = False
            try:
                derivation = solver.solve(inf)
                could_solve = True
            except SolverError:
                # warnings.warn(f'Could not solve the derivation of {classical_parser.unparse(inf)}', SolverWarning)
                unsolved += 1
            except Exception as e:
                print(classical_parser.unparse(inf))
                raise e

            if could_solve:
                try:
                    self.assertTrue(nd_system.is_correct_derivation(derivation, inf))
                except Exception as e:
                    print(classical_parser.unparse(inf))
                    print(derivation)
                    correct, error_list = nd_system.is_correct_derivation(derivation, inf, return_error_list=True)
                    print(error_list)
                    raise e

        # print(f'ND solver unsolved inferences = {unsolved}/1000')

        # Test with invalid arguments and see that they raise SolverError
        not_found_invalid = 0
        for _ in range(100):
            invalid = False
            for x in range(100):
                inf = random_formula_generator.random_inference(num_premises=2, num_conclusions=1, max_depth=3,
                                                                atomics=['p', 'q', 'r'], language=cl_language)
                if not classical_mvl_semantics.is_valid(inf):
                    invalid = True
                if invalid:
                    break
                if x == 99:
                    not_found_invalid += 1

            self.assertRaises(SolverError, solver.solve, inf)

        # print(f'Could not find invalid inference in {not_found_invalid} cases')

    def test_alt_solver(self):
        # Test with valid arguments and see that they are solved correctly
        unsolved = 0
        for _ in range(1000):
            # No Falsum in the generator
            inf = random_formula_generator.random_valid_inference(num_premises=2, num_conclusions=1,
                                                                  max_depth=3, atomics=['p', 'q', 'r'],
                                                                  language=classical_infinite_language_nobiconditional,
                                                                  validity_apparatus=classical_mvl_semantics)
            could_solve = False
            try:
                derivation = solver2.solve(inf)
                could_solve = True
            except SolverError:
                # warnings.warn(f'Could not solve the derivation of {classical_parser.unparse(inf)}', SolverWarning)
                unsolved += 1
            except Exception as e:
                print("Could not solve inference:")
                print(classical_parser.unparse(inf))
                raise e

            if could_solve:
                try:
                    self.assertTrue(nd_system2.is_correct_derivation(derivation, inf))
                except Exception as e:
                    print("Solution to the following inference is incorrect:")
                    print(classical_parser.unparse(inf))
                    print(derivation)
                    correct, error_list = nd_system2.is_correct_derivation(derivation, inf, return_error_list=True)
                    print(error_list)
                    raise e

        # print(f'ND solver unsolved inferences = {unsolved}/1000')

        # Test with invalid arguments and see that they raise SolverError
        not_found_invalid = 0
        for _ in range(100):
            invalid = False
            for x in range(100):
                inf = random_formula_generator.random_inference(num_premises=2, num_conclusions=1, max_depth=3,
                                                                atomics=['p', 'q', 'r'], language=cl_language)
                if not classical_mvl_semantics.is_valid(inf):
                    invalid = True
                if invalid:
                    break
                if x == 99:
                    not_found_invalid += 1

            self.assertRaises(SolverError, solver2.solve, inf)

        # print(f'Could not find invalid inference in {not_found_invalid} cases')

if __name__ == '__main__':
    unittest.main()
