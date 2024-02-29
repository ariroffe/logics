import unittest

from logics.instances.propositional.languages import classical_infinite_language_with_sent_constants as cl_language
from logics.instances.predicate.languages import classical_predicate_language as pred_lang
from logics.utils.formula_generators.generators_biased import random_formula_generator, random_predicate_formula_generator
from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics


class TestBiasedGenerators(unittest.TestCase):
    def test_depth(self):
        # Test that it returns formulae of the desired depth
        atomics = ['p', 'q']
        for depth in range(1, 6):
            for x in range(20):
                f1 = random_formula_generator._exact_depth_some_atomics(depth, atomics, cl_language)
                self.assertEqual(f1.depth, depth)

                f2 = random_formula_generator._upto_depth_some_atomics(depth, atomics, cl_language)
                self.assertLessEqual(f2.depth, depth)

                # f3 = g_EA_biased(depth, atomics, cl_language)
                f3 = random_formula_generator._exact_depth_all_atomics(depth, atomics, cl_language)
                self.assertEqual(f3.depth, depth)
                for atomic in atomics:
                    self.assertIn(atomic, str(f3))

                inf = random_formula_generator.random_inference(num_premises=2, num_conclusions=2, max_depth=depth,
                                                                atomics=atomics, language=cl_language)
                for premise in inf.premises:
                    self.assertLessEqual(premise.depth, depth)
                for conclusion in inf.conclusions:
                    self.assertLessEqual(conclusion.depth, depth)

    def test_generate_metainference(self):
        for level in range(1, 4):
            for _ in range(10):
                inf = random_formula_generator.random_inference(num_premises=2, num_conclusions=2, max_depth=2,
                                                                atomics=['p', 'q'], language=cl_language, level=level)
                self.assertEqual(inf.level, level)

    def test_generate_validities(self):
        for x in range(20):
            # Tautology (formula)
            tautology = random_formula_generator.random_tautology(depth=3, atomics=['p', 'q'], language=cl_language,
                                                                  validity_apparatus=classical_mvl_semantics,
                                                                  exact_depth=False)
            self.assertTrue(classical_mvl_semantics.is_tautology(tautology))

            # Inference
            valid_inf = random_formula_generator.random_valid_inference(num_premises=2, num_conclusions=1,
                                                                        max_depth=2, atomics=['p', 'q'],
                                                                        language=cl_language, level=1,
                                                                        validity_apparatus=classical_mvl_semantics)
            self.assertTrue(classical_mvl_semantics.is_valid(valid_inf))

            # Metainference
            valid_metainf = random_formula_generator.random_valid_inference(num_premises=2, num_conclusions=2,
                                                                              max_depth=2, atomics=['p', 'q'],
                                                                              language=cl_language, level=2,
                                                                              validity_apparatus=classical_mvl_semantics)
            self.assertTrue(classical_mvl_semantics.is_valid(valid_metainf))

    def test_predicate_generator(self):
        for depth in range(0, 6):
            for x in range(50):
                f = random_predicate_formula_generator.random_formula(
                    depth=depth, predicates=['P', 'R'], predicate_arities=pred_lang.predicate_letters,
                    max_predicate_arity=2, ind_constants=['a', 'b'],
                    variables=['x', 'y'], language=pred_lang
                )
                self.assertEqual(f.depth, depth)
                self.assertEqual(f.free_variables(pred_lang), set())
                self.assertTrue(f.is_closed(pred_lang))


if __name__ == '__main__':
    unittest.main()
