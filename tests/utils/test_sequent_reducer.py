import unittest

from logics.utils.parsers import classical_parser
from logics.classes.exceptions import SolverError
from logics.utils.formula_generators.generators_biased import random_formula_generator
from logics.instances.propositional.languages import classical_infinite_language_noconditional as cl_language
from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics
from logics.instances.propositional.sequents import LKminEA
from logics.utils.solvers.sequents import LKminEA_sequent_reducer


class TestSequentReducer(unittest.TestCase):
    def test_LKminEA(self):
        sequent = classical_parser.parse('A ==> A')
        tree = LKminEA_sequent_reducer.reduce(sequent, LKminEA)
        # tree.print_tree(classical_parser)
        self.assertTrue(LKminEA.is_correct_tree(tree))

        sequent = classical_parser.parse('B, A ==> A, C')
        tree = LKminEA_sequent_reducer.reduce(sequent, LKminEA)
        # tree.print_tree(classical_parser)
        self.assertTrue(LKminEA.is_correct_tree(tree))

        sequent = classical_parser.parse('Gamma, A ==> A, Delta')
        tree = LKminEA_sequent_reducer.reduce(sequent, LKminEA)
        # tree.print_tree(classical_parser)
        self.assertTrue(LKminEA.is_correct_tree(tree))

        sequent = classical_parser.parse('Gamma ==> A or not A, Delta')
        tree = LKminEA_sequent_reducer.reduce(sequent, LKminEA)
        # tree.print_tree(classical_parser)
        self.assertTrue(LKminEA.is_correct_tree(tree))

        # Check that we can derive the additive left conjunction rule (we have the multiplicative one in LKminEA)
        premise = classical_parser.parse('Gamma, A, Delta ==> Pi')
        sequent = classical_parser.parse('Gamma, A & B, Delta ==> Pi')
        tree = LKminEA_sequent_reducer.reduce(sequent, LKminEA, premises=[premise])
        # tree.print_tree(classical_parser)
        self.assertTrue(LKminEA.is_correct_tree(tree, premises=[premise]))

        # Check that we can derive everything if we add the empty sequent as premise
        premise = classical_parser.parse(' ==> ')
        sequent = classical_parser.parse('Gamma ==> Delta')
        tree = LKminEA_sequent_reducer.reduce(sequent, LKminEA, premises=[premise])
        # tree.print_tree(classical_parser)
        self.assertTrue(LKminEA.is_correct_tree(tree, premises=[premise]))

    def test_with_generator(self):
        # Test with valid arguments
        for _ in range(1000):
            inf = random_formula_generator.random_valid_inference(num_premises=2, num_conclusions=1,
                                                                    max_depth=3, atomics=['p', 'q'],
                                                                    language=cl_language,
                                                                    validity_apparatus=classical_mvl_semantics)

            sequent = LKminEA.transform_inference_into_sequent(inf)
            # print('\nSEQUENT TO REDUCE:', classical_parser.unparse(context_seq))
            try:
                tree2 = LKminEA_sequent_reducer.reduce(sequent, LKminEA)
                # tree2.print_tree(classical_parser)
                self.assertTrue(LKminEA.is_correct_tree(tree2))
            except SolverError:
                classical_parser.unparse(sequent)

        # Test with invalid arguments
        for _ in range(100):
            inf = random_formula_generator.random_invalid_inference(num_premises=2, num_conclusions=1,
                                                                      max_depth=3, atomics=['p', 'q'],
                                                                      language=cl_language,
                                                                      validity_apparatus=classical_mvl_semantics)

            sequent = LKminEA.transform_inference_into_sequent(inf)
            # print('\nSEQUENT TO REDUCE:', classical_parser.unparse(context_seq))
            self.assertRaises(SolverError, LKminEA_sequent_reducer.reduce, sequent, LKminEA)


if __name__ == '__main__':
    unittest.main()
