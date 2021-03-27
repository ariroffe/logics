import unittest
from copy import deepcopy

from logics.classes.predicate import PredicateFormula
from logics.classes.predicate.semantics import Model
from logics.instances.predicate.model_subclasses import ArithmeticModel, RealNumberArithmeticModel
from logics.instances.predicate.model_semantics import classical_model_semantics, classical_functional_model_semantics,\
    arithmetic_model_semantics, realnumber_arithmetic_model_semantics, arithmetic_truth_model_semantics
from logics.utils.parsers.predicate_parser import arithmetic_truth_parser


class TestModelSemantics(unittest.TestCase):
    def setUp(self):
        self.model1 = Model({
            'domain': {1, 2},
            'a': 1,
            'b': 2,
            'P': {1},
            'Q': {},
            'R': {(1,1), (1,2)},
        })

        self.model2 = deepcopy(self.model1)
        self.model2['f'] = {((1,), 2), ((2,), 1)}
        self.model2['g'] = {((1, 1), 1), ((1, 2), 2), ((2, 1), 1), ((2, 2), 2)}

        # I leave the domains empty since I won't test non-bounded quantification
        # If you want to assign a domain, for natural number arithmetic, I would recommend using itertools.count(0)
        self.arithmetic_model = ArithmeticModel({})
        self.realnumber_arithmetic_model = RealNumberArithmeticModel({})

    def test_denotation(self):
        self.assertEqual(self.model1.denotation('a'), 1)
        self.assertEqual(self.model1.denotation('b'), 2)
        self.assertEqual(self.model1.denotation('P'), {1})
        self.assertEqual(self.model2.denotation(('f', 'a')), 2)
        self.assertEqual(self.model2.denotation(('f', 'b')), 1)
        self.assertEqual(self.model2.denotation(('f', ('f', 'a'))), 1)
        self.assertEqual(self.model2.denotation(('g', ('f', 'a'), ('f', 'b'))), 1)
        self.assertEqual(self.model2.denotation(('g', ('g', 'b', 'a'), ('f', 'a'))), 2)

    def test_fixed_denotation(self):
        self.assertEqual(self.arithmetic_model.denotation('0'), 0)
        self.assertEqual(self.realnumber_arithmetic_model.denotation('3'), 3)
        self.assertEqual(self.arithmetic_model.denotation(('s', '0')), 1)
        self.assertEqual(self.arithmetic_model.denotation(('+', ('s', '0'), ('s', '0'))), 2)
        self.assertEqual(self.realnumber_arithmetic_model.denotation(('**', ('/', '9', '3'), '2')), 9)

    def test_valuation(self):
        # Atomic
        self.assertEqual(classical_model_semantics.valuation(PredicateFormula(['P', 'a']), self.model1), '1')
        self.assertEqual(classical_model_semantics.valuation(PredicateFormula(['P', 'b']), self.model1), '0')
        self.assertEqual(classical_model_semantics.valuation(PredicateFormula(['Q', 'a']), self.model1), '0')
        self.assertEqual(classical_model_semantics.valuation(PredicateFormula(['Q', 'b']), self.model1), '0')
        self.assertEqual(classical_model_semantics.valuation(PredicateFormula(['R', 'a', 'a']), self.model1), '1')
        self.assertEqual(classical_model_semantics.valuation(PredicateFormula(['R', 'a', 'b']), self.model1), '1')
        self.assertEqual(classical_model_semantics.valuation(PredicateFormula(['R', 'b', 'a']), self.model1), '0')
        self.assertEqual(classical_model_semantics.valuation(PredicateFormula(['R', 'b', 'b']), self.model1), '0')
        self.assertEqual(classical_functional_model_semantics.valuation(PredicateFormula(['P', ('f', 'a')]),
                                                                        self.model2), '0')

        # Molecular
        f = PredicateFormula(['∧', ['P', 'a'], ['P', 'b']])
        self.assertEqual(classical_model_semantics.valuation(f, self.model1), '0')
        f = PredicateFormula(['∧', ['P', 'a'], ['~', ['P', 'b']]])
        self.assertEqual(classical_model_semantics.valuation(f, self.model1), '1')
        f = PredicateFormula(['∨', ['P', 'a'], ['P', 'b']])
        self.assertEqual(classical_model_semantics.valuation(f, self.model1), '1')
        f = PredicateFormula(['∨', ['P', 'b'], ['~', ['P', 'a']]])
        self.assertEqual(classical_model_semantics.valuation(f, self.model1), '0')

        # Quantified
        f = PredicateFormula(['∀', 'x', ['P', 'x']])
        self.assertEqual(classical_model_semantics.valuation(f, self.model1), '0')
        f = PredicateFormula(['∃', 'x', ['P', 'x']])
        self.assertEqual(classical_model_semantics.valuation(f, self.model1), '1')
        f = PredicateFormula(['∃', 'x', '∈', 'P', ['P', 'x']])
        self.assertEqual(classical_model_semantics.valuation(f, self.model1), '1')
        f = PredicateFormula(['∃', 'x', '∈', 'Q',['P', 'x']])
        self.assertEqual(classical_model_semantics.valuation(f, self.model1), '0')

    def test_fixed_predicates(self):
        f = PredicateFormula(['=', ('+', ('s', '0'), ('s', '0')), ('s', ('s', '0'))])  # 1 + 1 = 2
        self.assertEqual(arithmetic_model_semantics.valuation(f, self.arithmetic_model), '1')
        f = PredicateFormula(['=', ('+', ('s', '0'), ('s', '0')), ('s', '0')])  # 1 + 1 = 1
        self.assertEqual(arithmetic_model_semantics.valuation(f, self.arithmetic_model), '0')
        f = PredicateFormula(['>', ('+', ('s', '0'), ('s', '0')), ('s', '0')])  # 1 + 1 > 1
        self.assertEqual(arithmetic_model_semantics.valuation(f, self.arithmetic_model), '1')
        f = PredicateFormula(['=', ('/', '1', '2'), '0.5'])  # 1 / 2 = 0.5
        self.assertEqual(realnumber_arithmetic_model_semantics.valuation(f, self.realnumber_arithmetic_model), '1')

    def test_truth_predicate(self):
        f = arithmetic_truth_parser.parse('Tr(⌜0=0⌝)')
        self.assertEqual(arithmetic_truth_model_semantics.valuation(f, self.arithmetic_model), '1')
        f = arithmetic_truth_parser.parse('Tr(⌜0=s(0)⌝)')
        self.assertEqual(arithmetic_truth_model_semantics.valuation(f, self.arithmetic_model), '0')
        f = arithmetic_truth_parser.parse('Tr(⌜Tr(⌜0=0⌝)⌝)')
        self.assertEqual(arithmetic_truth_model_semantics.valuation(f, self.arithmetic_model), '1')

        # Liar sentence (disable this test to run discover from the console)
        # Evaluating the liar sentence should raise RecursionError
        # self.assertRaises(RecursionError, arithmetic_truth_model_semantics.valuation,
        #                   arithmetic_truth_model_semantics.liar_sentence, self.arithmetic_model)
        # Right now it is giving us a stack overflow instead of this...

    def test_second_order_quantification(self):
        # Quantification range
        self.assertEqual(list(self.model1.predicate_variable_quantification_range(1)), [set(), {1}, {2}, {1, 2}])
        for x in self.model1.predicate_variable_quantification_range(2):
            self.assertIn(x,
                          [set(), {(1, 1)}, {(1, 2)}, {(2, 1)}, {(2, 2)},
                           {(1, 1), (1, 2)}, {(1, 1), (2, 1)}, {(1, 1), (2, 2)},
                           {(1, 2), (2, 1)}, {(1, 2), (2, 2)},
                           {(2, 1), (2, 2)},
                           {(1, 1), (1, 2), (2, 1)}, {(1, 1), (1, 2), (2, 2)},
                           {(1, 1), (2, 1), (2, 2)}, {(1, 2), (2, 1), (2, 2)},
                           {(1, 1), (1, 2), (2, 1), (2, 2)}])

        # Valuations
        f = PredicateFormula(['∀', 'X', ['X', 'a']])
        self.assertEqual(classical_model_semantics.valuation(f, self.model1), '0')
        f = PredicateFormula(['∃', 'X1', ['X1', 'a']])
        self.assertEqual(classical_model_semantics.valuation(f, self.model1), '1')
        f = PredicateFormula(['∀', 'X', ['∃', 'x', ['X', 'x']]])
        self.assertEqual(classical_model_semantics.valuation(f, self.model1), '0')  # Beause the empty set is in X


if __name__ == '__main__':
    unittest.main()
