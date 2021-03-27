import unittest

from logics.classes.predicate import InfinitePredicateLanguage, PredicateFormula
from logics.instances.predicate.languages import classical_infinite_predicate_language as cl_language
from logics.instances.predicate.languages import real_number_arithmetic_language as arithmetic


class TestLanguageFormulaClasses(unittest.TestCase):
    def setUp(self):
        individual_constants = ['a', 'b']
        variables = ['x']
        quantifiers = ['∀']
        metavariables = ['A', 'B']
        constant_arity_dict = {'~': 1, '∧': 2}
        predicate_letters = {'P': 1, 'R': 2, 'S': 3}
        predicate_variables = {'X': 1}
        sentential_constants = ['⊥', '⊤']
        function_symbols = {'f': 1, 'g': 2}
        self.function_language = InfinitePredicateLanguage(individual_constants=individual_constants,
                                                           variables=variables,
                                                           quantifiers=quantifiers,
                                                           metavariables=metavariables,
                                                           constant_arity_dict=constant_arity_dict,
                                                           predicate_letters=predicate_letters,
                                                           predicate_variables=predicate_variables,
                                                           sentential_constants=sentential_constants,
                                                           function_symbols=function_symbols,
                                                           allow_predicates_as_terms=True)
        # Some formulae
        # Atomic
        self.a1 = PredicateFormula(['P', 'x'])
        self.a2 = PredicateFormula(['P', 'a'])
        self.a3 = PredicateFormula(['P', 'a', 'b'])
        self.a4 = PredicateFormula(['P', ('f', 'a')])
        self.a5 = PredicateFormula(['P', ('f', ('g', 'a', 'a'))])
        self.a6 = PredicateFormula(['P', ('f', ('g', 'a'))])
        self.a7 = PredicateFormula(['X', ('f', ('g', 'x', 'x'))])

        # Molecular
        self.m1 = PredicateFormula(['∧', self.a7, ['~', self.a2]])
        self.m2 = PredicateFormula(['∀', 'x', ['P', 'x']])
        self.m3 = PredicateFormula(['∀', 'a', self.m1])
        self.m4 = PredicateFormula(['∀', ('f', 'x'), self.m1])
        self.m5 = PredicateFormula(['∀', 'x', self.a7])
        self.m6 = PredicateFormula(['∀', 'x', ['∀', 'X', ['P', 'x']]])
        self.m7 = PredicateFormula(['∀', 'x', '∈', ('f', 'x'), self.a1])
        self.m8 = PredicateFormula(['∀', 'x', '∈', 'P', self.a1])

    def test_constants(self):
        self.assertEqual(cl_language.constants(), {'~', '∧', '∨', '→', '↔'})
        self.assertEqual(cl_language.constants(1), {'~'})
        self.assertEqual(cl_language.constants(2), {'∧', '∨', '→', '↔'})
        self.assertEqual(cl_language.quantifiers, ['∀', '∃'])
        self.assertEqual(cl_language.predicates(), {'P', 'Q', 'R', 'S'})
        self.assertEqual(cl_language.predicates(1), {'P', 'Q'})

    def test_arity(self):
        self.assertEqual(cl_language.arity('~'), 1)
        self.assertEqual(cl_language.arity('∧'), 2)
        self.assertEqual(cl_language.arity('P'), 1)
        self.assertEqual(self.function_language.arity('f'), 1)

    def test_is_well_formed(self):
        self.assertTrue(self.function_language.is_well_formed(self.a1))
        self.assertTrue(self.function_language.is_well_formed(self.a2))
        self.assertTrue(self.function_language.is_well_formed(self.a4))
        self.assertTrue(self.function_language.is_well_formed(self.a5))
        self.assertTrue(self.function_language.is_well_formed(self.a7))
        self.assertTrue(self.function_language.is_well_formed(PredicateFormula(['~', ['P', 'x1']])))
        self.assertTrue(self.function_language.is_well_formed(PredicateFormula(['~', ['X2', 'x1']])))
        self.assertFalse(self.function_language.is_well_formed(self.a3))
        self.assertFalse(self.function_language.is_well_formed(self.a6))
        self.assertFalse(self.function_language.is_well_formed(PredicateFormula(['~', '~', ['P', 'x']])))

        self.assertTrue(self.function_language.is_well_formed(self.m1))
        self.assertTrue(self.function_language.is_well_formed(self.m2))
        self.assertTrue(self.function_language.is_well_formed(self.m5))
        self.assertTrue(self.function_language.is_well_formed(self.m6))
        self.assertTrue(self.function_language.is_well_formed(self.m7))
        self.assertTrue(self.function_language.is_well_formed(self.m8))
        self.assertFalse(self.function_language.is_well_formed(self.m3))
        self.assertFalse(self.function_language.is_well_formed(self.m4))
        self.assertTrue(cl_language.is_well_formed(self.m6))
        self.assertFalse(cl_language.is_well_formed(self.m8))

    def test_free_variables(self):
        self.assertEqual(self.a1.free_variables(self.function_language), {'x'})
        self.assertTrue(self.a1.is_open(self.function_language))
        self.assertFalse(self.a1.is_closed(self.function_language))

        self.assertEqual(self.a2.free_variables(self.function_language), set())
        self.assertEqual(self.m2.free_variables(self.function_language), set())
        self.assertFalse(self.m2.is_open(self.function_language))
        self.assertTrue(self.m2.is_closed(self.function_language))

        self.assertEqual(PredicateFormula(['∀', 'x', ['X', 'x']]).free_variables(self.function_language), {'X'})
        self.assertEqual(PredicateFormula(['∀', 'X', ['X', 'a']]).free_variables(self.function_language), set())
        self.assertEqual(PredicateFormula(['∀', 'x', '∈', 'x', ['P', 'a']]).free_variables(self.function_language),
                         {'x'})
        self.assertEqual(PredicateFormula(['∀', 'x', '∈', 'a', ['P', 'x']]).free_variables(self.function_language),
                         set())

    def test_some_base_formula_methods(self):
        self.assertFalse(PredicateFormula(['P', 'x']).is_schematic(cl_language))
        self.assertTrue(PredicateFormula(['∧', ['P', 'x'], ['A']]).is_schematic(cl_language))
        self.assertEqual(PredicateFormula(['∧', ['P', 'x'], ['A']]).main_symbol, '∧')
        self.assertEqual(PredicateFormula(['∃', 'x', ['∀', 'X', ['X', 'x']]]).depth, 2)
        subf = [
            PredicateFormula(['X', 'x']),
            PredicateFormula(['∀', 'X', ['X', 'x']]),
            PredicateFormula(['∃', 'x', ['∀', 'X', ['X', 'x']]])
        ]
        self.assertEqual(PredicateFormula(['∃', 'x', ['∀', 'X', ['X', 'x']]]).subformulae, subf)

    def test_base_substitute_instantiate(self):
        # Substitute
        f1 = PredicateFormula(['∧', ['P', 'x'], ['A']])
        f2 = PredicateFormula(['∧', ['Q', 'x'], ['A']])
        f3 = f1.substitute(PredicateFormula(['P', 'x']), PredicateFormula(['Q', 'x']))
        self.assertEqual(f2, f3)

        # Instantiate
        f4 = PredicateFormula(['∧', ['P', 'x'], ['P', 'a']])
        f5 = f1.instantiate(cl_language, {'A': PredicateFormula(['P', 'a'])})
        self.assertEqual(f4, f5)

        # Schematic substitute
        f1 = PredicateFormula(['∧', ['P', 'x'], ['Q', 'x']])
        f2 = PredicateFormula(['∧', ['Q', 'x'], ['P', 'x']])
        f3 = f1.schematic_substitute(cl_language,
                                     PredicateFormula(['∧', ['A'], ['B']]),
                                     PredicateFormula(['∧', ['B'], ['A']]))
        self.assertEqual(f2, f3)

    def test_vsubstitute(self):
        self.assertEqual(self.a1.vsubstitute('x', 'a'), PredicateFormula(['P', 'a']))
        self.assertEqual(self.a1.vsubstitute('y', 'a'), self.a1)
        self.assertEqual(self.a2.vsubstitute('x', 'b'), self.a2)
        self.assertEqual(self.m2.vsubstitute('x', 'a'), self.m2)
        self.assertEqual(PredicateFormula(['X', 'a']).vsubstitute('X', 'P'), PredicateFormula(['P', 'a']))
        self.assertEqual(PredicateFormula(['∀', 'X', ['X', 'a']]).vsubstitute('X', 'P'),
                         PredicateFormula(['∀', 'X', ['X', 'a']]))
        self.assertEqual(PredicateFormula(['∀', 'x', '∈', 'x', ['P', 'a']]).vsubstitute('x', 'b'),
                         PredicateFormula(['∀', 'x', '∈', 'b', ['P', 'a']]))
        self.assertEqual(PredicateFormula(['∀', 'x', '∈', ('f', 'x'), ['P', 'x']]).vsubstitute('x', 'b'),
                         PredicateFormula(['∀', 'x', '∈', ('f', 'b'), ['P', 'x']]))
        self.assertEqual(PredicateFormula(['∀', 'X', ['∀', 'x', ['X', 'y']]]).vsubstitute('y', ('f', 'x')),
                         PredicateFormula(['∀', 'X', ['∀', 'x', ['X', ('f', 'x')]]]))

    def test_is_instance_of(self):
        A = PredicateFormula(['A'])
        B = PredicateFormula(['B'])

        # Atomic metavariables
        self.assertTrue(self.a2.is_instance_of(A, self.function_language))
        instance, subst_dict = self.a1.is_instance_of(A, self.function_language, return_subst_dict=True)
        self.assertTrue(instance)
        self.assertEqual(subst_dict['A'], self.a1)

        # Molecular (connective) schemas
        self.assertTrue(self.m1.is_instance_of(PredicateFormula(['∧', A, ['~', B]]), self.function_language))
        self.assertFalse(self.m1.is_instance_of(PredicateFormula(['∧', A, ['~', A]]), self.function_language))

        # Quantified schemas
        self.assertTrue(self.m2.is_instance_of(PredicateFormula(['∀', 'x', ['A']]), self.function_language))
        self.assertFalse(self.m2.is_instance_of(PredicateFormula(['∀', 'x', ['∧', A, B]]), self.function_language))
        self.assertTrue(self.m6.is_instance_of(PredicateFormula(['∀', 'x', ['∀', 'X', ['A']]]), self.function_language))
        instance, subst_dict = self.m6.is_instance_of(PredicateFormula(['∀', 'x', ['A']]), self.function_language,
                                                      return_subst_dict=True)
        self.assertTrue(instance)
        self.assertEqual(subst_dict['A'], ['∀', 'X', ['P', 'x']])

    def test_arithmetic_language(self):
        self.assertTrue(arithmetic._is_term_well_formed('1'))
        self.assertTrue(arithmetic._is_term_well_formed('-1'))  # Should we change this?
        self.assertFalse(arithmetic._is_term_well_formed('a'))
        self.assertTrue(arithmetic._is_term_well_formed(('+', '1', ('*', '2', '32324'))))
        self.assertTrue(arithmetic.is_well_formed(PredicateFormula(['=', ('+', '1', '1'), '2'])))


if __name__ == '__main__':
    unittest.main()
