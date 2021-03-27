import unittest

from logics.classes.exceptions import SolverError
from logics.utils.parsers import classical_parser
from logics.utils.solvers import classical_natural_deduction_solver
from logics.utils.formula_generators.generators_biased import random_formula_generator
from logics.instances.propositional.languages import classical_infinite_language_with_sent_constants_nobiconditional \
    as cl_language
from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics
from logics.instances.propositional.natural_deduction import classical_natural_deduction_system as nd_system


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

    def test_solver_noclean(self):
        # Rules in the first function
        efsq = classical_parser.parse('⊥ / p')
        conjunction_introduction = classical_parser.parse('p1 ∧ p2, p3 ∧ p4 / p2 ∧ p3')
        conditional_introduction = classical_parser.parse('p, q / p → q')
        disjunction_introduction = classical_parser.parse('p / p ∨ q')
        reductio = classical_parser.parse('p → (q ∧ ~q) / ~p')
        repetitions1 = classical_parser.parse('p / p ∧ p')
        repetitions2 = classical_parser.parse('/ p → p')

        inferences = [efsq, conjunction_introduction, conditional_introduction, disjunction_introduction, reductio,
                      repetitions1, repetitions2]
        inferences.extend(self.derived_rules)

        for inference in inferences:
            derivation = classical_natural_deduction_solver._solve_derivation(inference)
            # print(derivation)
            # print('\n')

        conjunction_steps = classical_parser.parse('p, q, r / (q → p) ∧ (r → p)')
        derivation = classical_natural_deduction_solver._solve_derivation(conjunction_steps)
        # print(derivation)

    def test_delete_unused_steps(self):
        inference = classical_parser.parse('((p ∧ q) ∧ (q ∧ r)) / r')
        derivation = classical_natural_deduction_solver._solve_derivation(inference)
        # print(derivation)
        # print(solver._get_used_steps(derivation, inference))

        used_steps = classical_natural_deduction_solver._get_used_steps(derivation, inference)
        derivation = classical_natural_deduction_solver._delete_unused_steps(derivation, used_steps)
        # print(derivation)

    def test_replace_derived_rules(self):
        for inference in self.derived_rules:
            derivation = classical_natural_deduction_solver._solve_derivation(inference)
            # print('ORIGNAL\n', derivation)

            derivation = classical_natural_deduction_solver._replace_derived_rules(derivation)
            # print('REPLACED\n', derivation)
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
                derivation = classical_natural_deduction_solver.solve(inf)
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

            self.assertRaises(SolverError, classical_natural_deduction_solver.solve, inf)

        # print(f'Could not find invalid inference in {not_found_invalid} cases')


if __name__ == '__main__':
    unittest.main()
