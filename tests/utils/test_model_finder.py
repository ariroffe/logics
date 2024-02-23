import unittest

from logics.utils.parsers import classical_predicate_parser
from logics.utils.solvers.model_finder import classical_model_finder
from logics.classes.predicate.semantics import Model
from logics.instances.predicate.model_semantics import classical_model_semantics as logic


class TestModelFinder(unittest.TestCase):
    def test_get_initial_model(self):
        f = classical_predicate_parser.parse("forall x (P(a) or R(x, b))")
        ind_cts = sorted(list(f.individual_constants_inside(logic.language)))
        preds = f.predicates_inside()
        m = classical_model_finder._get_initial_model(ind_cts, preds)
        self.assertEqual(m, Model({'domain': {'1', '2'}, 'a': '1', 'b': '2', 'P': set(), 'R': set()}))

        # With no ind constants should return a domain with 1 element
        f = classical_predicate_parser.parse("forall x (P(x) or R(x, x))")
        ind_cts = f.individual_constants_inside(logic.language)  # empty
        preds = f.predicates_inside()
        m = classical_model_finder._get_initial_model(ind_cts, preds)
        self.assertEqual(m, Model({'domain': {'1'}, 'P': set(), 'R': set()}))
