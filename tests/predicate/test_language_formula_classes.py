import unittest

from logics.utils.parsers.predicate_parser import classical_predicate_parser as parser
from logics.classes.predicate import InfinitePredicateLanguage, PredicateFormula
from logics.instances.predicate.languages import (
    classical_infinite_predicate_language as cl_language,
    classical_predicate_language as finite_lang
)
from logics.instances.predicate.languages import real_number_arithmetic_language as arithmetic


class TestLanguageFormulaClasses(unittest.TestCase):
    def setUp(self):
        individual_constants = ['a', 'b']
        variables = ['x']
        individual_metavariables = ['α', 'β']
        variable_metavariables = ['χ', 'ψ']
        quantifiers = ['∀', '∃']
        metavariables = ['A', 'B']
        constant_arity_dict = {'~': 1, '∧': 2}
        predicate_letters = {'P': 1, 'R': 2, 'S': 3}
        predicate_variables = {'X': 1}
        sentential_constants = ['⊥', '⊤']
        function_symbols = {'f': 1, 'g': 2}
        self.function_language = InfinitePredicateLanguage(individual_constants=individual_constants,
                                                           variables=variables,
                                                           individual_metavariables=individual_metavariables,
                                                           variable_metavariables=variable_metavariables,
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
        self.assertEqual(cl_language.predicates(), {'P', 'Q', 'R', 'S', 'M', 'N', 'T'})
        self.assertEqual(cl_language.predicates(1), {'P', 'Q', 'M', 'N'})

    def test_arity(self):
        self.assertEqual(cl_language.arity('~'), 1)
        self.assertEqual(cl_language.arity('∧'), 2)
        self.assertEqual(cl_language.arity('P'), 1)
        self.assertEqual(cl_language.arity('W'), 1)  # predicate variable
        self.assertEqual(self.function_language.arity('f'), 1)

    def test_individual_and_variable_metavariables(self):
        # is_valid_predicate
        self.assertTrue(cl_language._is_valid_predicate('P'))   # predicate
        self.assertTrue(cl_language._is_valid_predicate('W'))   # predicate variable
        self.assertFalse(cl_language._is_valid_predicate('Φ'))
        self.assertFalse(cl_language._is_valid_predicate('A'))  # formula metavariable

        # is_valid_individual_constant
        self.assertTrue(cl_language.is_valid_individual_constant('a'))   # ind constant
        self.assertTrue(cl_language.is_valid_individual_constant('α'))   # ind metavariable
        self.assertFalse(cl_language.is_valid_individual_constant('x'))  # ind variable

        # is_valid_variable
        self.assertTrue(cl_language._is_valid_variable('x'))   # ind variable
        self.assertTrue(cl_language._is_valid_variable('x1'))  # ind variable
        self.assertTrue(cl_language._is_valid_variable('X'))   # pred variable
        self.assertTrue(cl_language._is_valid_variable('X1'))  # pred variable
        self.assertFalse(cl_language._is_valid_variable('Φ'))
        self.assertFalse(cl_language._is_valid_variable('α'))  # ind metavariable
        self.assertTrue(cl_language._is_valid_variable('χ'))   # var metavariable
        self.assertFalse(cl_language._is_valid_variable('χ1'))  # these do not admit digits at the end
        self.assertFalse(cl_language._is_valid_variable('a'))  # ind constant
        self.assertFalse(cl_language._is_valid_variable('A'))  # formula metavariable

        # is metavariable string
        self.assertTrue(cl_language.is_metavariable_string('A'))   # formula metavariable
        self.assertTrue(cl_language.is_metavariable_string('α'))   # ind metavariable
        self.assertTrue(cl_language.is_metavariable_string('χ'))   # var metavariable
        self.assertFalse(cl_language.is_metavariable_string('P'))  # common predicate
        self.assertFalse(cl_language.is_metavariable_string('a'))  # common ind constant

    def test_contains_string(self):
        f = parser.parse("forall x P(x) and ~R(a, f(b))")
        self.assertTrue(f.contains_string('R'))
        self.assertTrue(f.contains_string('a'))
        self.assertTrue(f.contains_string('x'))
        self.assertFalse(f.contains_string('c'))
        self.assertFalse(f.contains_string('y'))
        self.assertTrue(f.contains_string('f'))

    def test_predicates_inside(self):
        self.assertEqual(parser.parse("P(a)").predicates_inside(), {'P': 1})
        self.assertEqual(PredicateFormula(["P", "a", "b"]).predicates_inside(), {'P': 2})  # not respecting lang
        self.assertEqual(parser.parse("R(a,f(b))").predicates_inside(), {'R': 2})
        self.assertEqual(parser.parse("forall x P(x)").predicates_inside(), {'P': 1})
        f = parser.parse("forall x (P(x) or P(c)) and ~R(a, f(b))")
        self.assertEqual(f.predicates_inside(), {'P': 1, 'R': 2})

    def test_individual_constants_inside(self):
        self.assertEqual(parser.parse("P(a)").individual_constants_inside(cl_language), {'a'})
        self.assertEqual(parser.parse("R(a,b)").individual_constants_inside(cl_language), {'a', 'b'})
        self.assertEqual(parser.parse("R(x,b)").individual_constants_inside(cl_language), {'b'})
        self.assertEqual(parser.parse("R(a,f(b))").individual_constants_inside(self.function_language), {'a', 'b'})
        self.assertEqual(parser.parse("forall x P(x)").individual_constants_inside(self.function_language), set())
        f = parser.parse("forall x (P(x) or P(c)) and ~R(a, f(b))")
        self.assertEqual(f.individual_constants_inside(cl_language), {'a', 'b', 'c'})

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

        # formulae with individual and variable metavariables
        self.assertTrue(cl_language.is_well_formed(PredicateFormula(['P', 'α'])))
        self.assertTrue(cl_language.is_well_formed(PredicateFormula(['P', 'χ'])))
        self.assertFalse(cl_language.is_well_formed(PredicateFormula(['α', 'α'])))
        self.assertFalse(cl_language.is_well_formed(PredicateFormula(['χ', 'χ'])))
        self.assertFalse(cl_language.is_well_formed(PredicateFormula(['R', 'α'])))  # binary
        self.assertTrue(cl_language.is_well_formed(PredicateFormula(['R', 'α', 'a'])))
        self.assertTrue(cl_language.is_well_formed(PredicateFormula(['R', 'α', 'β'])))
        self.assertTrue(cl_language.is_well_formed(PredicateFormula(['R', 'α', 'χ'])))
        self.assertTrue(cl_language.is_well_formed(PredicateFormula(['∀', 'x', ['P', 'α']])))
        self.assertFalse(cl_language.is_well_formed(PredicateFormula(['∀', 'α', ['P', 'α']])))
        self.assertTrue(cl_language.is_well_formed(PredicateFormula(['∀', 'χ', ['P', 'α']])))
        self.assertTrue(cl_language.is_well_formed(PredicateFormula(['∀', 'χ', ['P', 'χ']])))
        self.assertTrue(cl_language.is_well_formed(PredicateFormula(['∀', 'χ', '∈', 'a', ['P', 'χ']])))
        self.assertTrue(cl_language.is_well_formed(PredicateFormula(['∀', 'χ', '∈', 'α', ['P', 'χ']])))

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

        # Check that ind metavariables are not registered as free variables
        self.assertEqual(PredicateFormula(['P', 'α']).free_variables(self.function_language), set())
        self.assertEqual(PredicateFormula(['P', ('f', 'α')]).free_variables(self.function_language), set())

        # Check that variable metavariables are
        self.assertEqual(PredicateFormula(['P', 'χ']).free_variables(self.function_language), {'χ'})
        self.assertEqual(PredicateFormula(['∀', 'χ', ['P', 'χ']]).free_variables(self.function_language), set())

        # We were getting incorrect results with some formulae, e.g. this:
        f = parser.parse("∃x P(x) → P(x)")
        self.assertEqual(f.free_variables(finite_lang), {'x'})

    def test_some_base_formula_methods(self):
        self.assertEqual(PredicateFormula(['∧', ['P', 'x'], ['A']]).main_symbol, '∧')
        self.assertEqual(PredicateFormula(['∃', 'x', ['∀', 'X', ['X', 'x']]]).depth, 2)
        subf = [
            PredicateFormula(['X', 'x']),
            PredicateFormula(['∀', 'X', ['X', 'x']]),
            PredicateFormula(['∃', 'x', ['∀', 'X', ['X', 'x']]])
        ]
        self.assertEqual(PredicateFormula(['∃', 'x', ['∀', 'X', ['X', 'x']]]).subformulae, subf)

    def test_is_schematic(self):
        self.assertFalse(PredicateFormula._is_schematic_term('a', cl_language))
        self.assertTrue(PredicateFormula._is_schematic_term('α', cl_language))
        self.assertTrue(PredicateFormula._is_schematic_term('χ', cl_language))
        self.assertFalse(PredicateFormula._is_schematic_term(('f', 'a'), self.function_language))
        self.assertFalse(PredicateFormula._is_schematic_term(('f', ('g', 'a')), self.function_language))
        self.assertTrue(PredicateFormula._is_schematic_term(('f', 'α'), self.function_language))
        self.assertTrue(PredicateFormula._is_schematic_term(('f', 'χ'), self.function_language))
        self.assertTrue(PredicateFormula._is_schematic_term(('f', ('g', 'α')), self.function_language))

        self.assertFalse(PredicateFormula(['P', 'x']).is_schematic(cl_language))
        self.assertTrue(PredicateFormula(['P', 'α']).is_schematic(cl_language))
        self.assertTrue(PredicateFormula(['∧', ['P', 'x'], ['A']]).is_schematic(cl_language))
        self.assertTrue(PredicateFormula(['P', ('f', 'α')]).is_schematic(self.function_language))
        self.assertTrue(PredicateFormula(['∀', 'χ', ['P', 'a']]).is_schematic(self.function_language))
        self.assertTrue(PredicateFormula(['∃', 'χ', ['~', ['A']]]).is_schematic(self.function_language))

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

        # var metavariables
        self.assertEqual(PredicateFormula(['P', 'χ']).vsubstitute('χ', 'a'), PredicateFormula(['P', 'a']))
        f = PredicateFormula(['∀', 'χ', ['P', 'χ']])
        self.assertEqual(f.vsubstitute('χ', 'a'), f)

    def test_instantiate(self):
        # Terms
        f = PredicateFormula(['P', 'a'])
        self.assertEqual(f._term_instantiate('a', cl_language, {'α': 'b'}), 'a')
        self.assertEqual(f._term_instantiate('α', cl_language, {'α': 'b'}), 'b')
        self.assertEqual(f._term_instantiate(('f', 'α', 'a'), cl_language, {'α': 'b'}), ('f', 'b', 'a'))
        self.assertEqual(f._term_instantiate(('f', ('g', 'α'), 'a'), cl_language, {'α': 'b'}), ('f', ('g', 'b'), 'a'))

        # Atomics
        inst = PredicateFormula(['P', 'a'])._atomic_instantiate(cl_language, {'α': 'b'})
        self.assertEqual(inst, PredicateFormula(['P', 'a']))

        inst = PredicateFormula(['P', 'α'])._atomic_instantiate(cl_language, {'α': 'b'})
        self.assertEqual(inst, PredicateFormula(['P', 'b']))

        inst = PredicateFormula(['P', ('f', 'α')])._atomic_instantiate(cl_language, {'α': 'b'})
        self.assertEqual(inst, PredicateFormula(['P', ('f', 'b')]))

        # Quantified
        inst = PredicateFormula(['∀', 'x', ['P', 'x']]).instantiate(cl_language, {'x': 'y'})
        self.assertEqual(inst, PredicateFormula(['∀', 'x', ['P', 'x']]))  # Should remain the same, x not a mv

        inst = PredicateFormula(['∀', 'χ', ['P', 'χ']]).instantiate(cl_language, {'χ': 'x'})
        self.assertEqual(inst, PredicateFormula(['∀', 'x', ['P', 'x']]))

        # Sentential mvs
        subst_dict = {"A": PredicateFormula(['P', 'a'])}
        self.assertEqual(PredicateFormula(['A']).instantiate(cl_language, subst_dict), PredicateFormula(['P', 'a']))

        # Formulae of the form [α/χ]A
        subst_dict = {'A': PredicateFormula(['R', 'x', 'b']), 'χ': 'x', 'α':'a'}
        inst = PredicateFormula(['[α/χ]A']).instantiate(cl_language, subst_dict)
        self.assertEqual(inst, PredicateFormula(['R', 'a', 'b']))

        inst = PredicateFormula(['~', ['[α/χ]A']]).instantiate(cl_language, subst_dict)
        self.assertEqual(inst, PredicateFormula(['~', ['R', 'a', 'b']]))

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

        # Individual and variable metavariables
        m = PredicateFormula(['P', 'α'])
        self.assertTrue(PredicateFormula(['P', 'a']).is_instance_of(m, self.function_language))
        self.assertTrue(PredicateFormula(['P', 'b']).is_instance_of(m, self.function_language))

        m = PredicateFormula(['∧', ['P', 'α'], ['R', 'b', 'α']])
        f1 = PredicateFormula(['∧', ['P', 'a'], ['R', 'b', 'a']])
        f2 = PredicateFormula(['∧', ['P', 'α'], ['R', 'b', 'c']])
        self.assertTrue(f1.is_instance_of(m, self.function_language))
        self.assertFalse(f2.is_instance_of(m, self.function_language))
        inst, subst_dict = f1.is_instance_of(m, self.function_language, return_subst_dict=True)
        self.assertEqual(subst_dict, {'α': 'a'})

        m = PredicateFormula(['P', 'χ'])
        self.assertFalse(PredicateFormula(['P', 'a']).is_instance_of(m, self.function_language))
        self.assertTrue(PredicateFormula(['P', 'x']).is_instance_of(m, self.function_language))
        self.assertFalse(PredicateFormula(['R', 'a', 'b']).is_instance_of(m, self.function_language))
        self.assertTrue(PredicateFormula(['P', 'χ']).is_instance_of(m, self.function_language))

        m = PredicateFormula(['∀', 'χ', ['P', 'χ']])
        self.assertTrue(PredicateFormula(['∀', 'x', ['P', 'x']]).is_instance_of(m, self.function_language))
        self.assertFalse(PredicateFormula(['∀', 'x', ['P', 'y']]).is_instance_of(m, self.function_language))
        self.assertFalse(PredicateFormula(['∀', 'x', ['P', 'a']]).is_instance_of(m, self.function_language))

        m = PredicateFormula(['∀', 'χ', ['A']])
        instance, subst_dict = PredicateFormula(['∀', 'x', ['P', 'x']]).is_instance_of(m, self.function_language,
                                                                                       return_subst_dict=True)
        self.assertTrue(instance)
        self.assertEqual(subst_dict, {'χ': 'x', 'A': PredicateFormula(['P', 'x'])})

        m = PredicateFormula(['P', ('f', 'α', ('f' ,'α'))])
        f1 = PredicateFormula(['P', ('f', 'a', ('f', 'a'))])
        self.assertTrue(f1.is_instance_of(m, self.function_language))
        self.assertFalse(PredicateFormula(['P', ('f', 'a', ('f', 'b'))]).is_instance_of(m, self.function_language))
        inst, subst_dict = f1.is_instance_of(m, self.function_language, return_subst_dict=True)
        self.assertEqual(subst_dict, {'α': 'a'})
        self.assertTrue(PredicateFormula(['∃', 'x', ['~', ['P', 'x']]])
                        .is_instance_of(PredicateFormula(['∃', 'χ', ['~', ['A']]]), cl_language))


    def test_arithmetic_language(self):
        self.assertTrue(arithmetic._is_term_well_formed('1'))
        self.assertTrue(arithmetic._is_term_well_formed('-1'))  # Should we change this?
        self.assertFalse(arithmetic._is_term_well_formed('a'))
        self.assertTrue(arithmetic._is_term_well_formed(('+', '1', ('*', '2', '32324'))))
        self.assertTrue(arithmetic.is_well_formed(PredicateFormula(['=', ('+', '1', '1'), '2'])))


if __name__ == '__main__':
    unittest.main()
