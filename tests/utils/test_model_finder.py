import unittest

from logics.utils.parsers import classical_predicate_parser
from logics.utils.solvers.model_finder import classical_model_finder
from logics.utils.formula_generators.generators_biased import random_predicate_formula_generator
from logics.classes.predicate.semantics import Model
from logics.classes.exceptions import SolverError
from logics.instances.predicate.model_semantics import classical_model_semantics


class TestModelFinder(unittest.TestCase):
    def test_get_initial_model(self):
        f = classical_predicate_parser.parse("forall x (P(a) or R(x, b))")
        ind_cts = sorted(list(f.individual_constants_inside(classical_model_semantics.language)))
        preds = f.predicates_inside()
        m = classical_model_finder._get_initial_model(ind_cts, preds)
        self.assertEqual(m, Model({'domain': {'1', '2'}, 'a': '1', 'b': '2', 'P': set(), 'R': set()}))

        # With no ind constants should return a domain with 1 element
        f = classical_predicate_parser.parse("forall x (P(x) or R(x, x))")
        ind_cts = f.individual_constants_inside(classical_model_semantics.language)  # empty
        preds = f.predicates_inside()
        m = classical_model_finder._get_initial_model(ind_cts, preds)
        self.assertEqual(m, Model({'domain': {'1'}, 'P': set(), 'R': set()}))

    def test_with_examples(self):
        examples = [
            'P(a)',
            'R(a,b)',
            '∃x P(x)',
            '∀x P(x)',
            '∀x (P(x) ∨ ~P(x))',
            '∀x R(x,x)',
            '∃x ∃y R(x,y)',
            '∃x ∀y R(x,y)',
            '∀x ∃y R(x,y)',
            '∃x (P(x) ∧ ~R(x,a))',
            '~∃x ~P(x) ∧ ~∀x ~R(a,x)',
            '∃x ∀y R(x,y) → ∀x ∃y R(x,y)',
            'Q(a) ∧ (∃x P(x) ∧ ∃x (P(x) → ~Q(x)))',
        ]

        for example in examples:
            formula = classical_predicate_parser.parse(example)
            model = classical_model_finder.find_model(formula, "1", classical_model_semantics)
            valuation = classical_model_semantics.valuation(formula, model)
            self.assertEqual(valuation, "1")

    def test_with_generator(self):
        lang = classical_model_semantics.language
        for depth in range(0, 4):
            for _ in range(10):
                formula = random_predicate_formula_generator.random_formula(depth=depth,
                                                                            predicates=['P', 'R'],
                                                                            predicate_arities=lang.predicate_letters,
                                                                            max_predicate_arity=2,
                                                                            ind_constants=['a', 'b'],
                                                                            variables=['x', 'y'],
                                                                            language=lang)
                for value in ("0", "1"):
                    try:
                        model = classical_model_finder.find_model(formula, value, classical_model_semantics)
                    except SolverError:
                        # print(f"Could not find model for formula {classical_predicate_parser.unparse(formula)} and value {value}")
                        continue
                    except Exception as e:
                        print(f"Problem with formula {classical_predicate_parser.unparse(formula)} and value {value}")
                        raise e
                    valuation = classical_model_semantics.valuation(formula, model)
                    self.assertEqual(valuation, value)