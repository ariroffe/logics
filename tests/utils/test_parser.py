import unittest
import warnings

from logics.utils.parsers import classical_parser, modal_parser, LFI_parser
from logics.instances.predicate.languages import arithmetic_truth_language
from logics.utils.parsers.predicate_parser import classical_predicate_parser, \
    arithmetic_parser, realnumber_arithmetic_parser, arithmetic_truth_parser
from logics.classes.propositional import Formula, Inference
from logics.classes.predicate import PredicateFormula
from logics.classes.propositional.proof_theories import DerivationStep, Derivation, Sequent
from logics.classes.exceptions import LevelsWarning, NotWellFormed
from logics.utils.parsers.parser_utils import separate_arguments, get_main_constant


class TestPropositionalParser(unittest.TestCase):
    def setUp(self):
        self.p = Formula(['p'])
        self.q = Formula(['q'])

    def test_parser_utils(self):
        self.assertEqual(separate_arguments('(x,y,z)', ','), ['x', 'y', 'z'])
        self.assertEqual(separate_arguments('(x,(y1,y2),z)', ','), ['x', '(y1,y2)', 'z'])
        infix_cts = ['∧', '∨', '→', '↔']
        self.assertEqual(get_main_constant('~q', infix_cts), (None, None))  # Only recognizes binary constants
        self.assertEqual(get_main_constant('(p→q)', infix_cts), ('→', 2))
        self.assertEqual(get_main_constant('(p→(q→p))', infix_cts), ('→', 2))
        self.assertEqual(get_main_constant('((p→q)→p)', infix_cts), ('→', 6))
        self.assertRaises(NotWellFormed, get_main_constant, '(p→q→p)', infix_cts)

    def test_prepare_to_parse(self):
        self.assertEqual(classical_parser._prepare_to_parse('p'), 'p')
        self.assertEqual(classical_parser._prepare_to_parse('p and q'), 'p∧q')
        self.assertEqual(classical_parser._prepare_to_parse('/'), '/1]')
        self.assertEqual(classical_parser._prepare_to_parse('p/q'), 'p/1]q')
        self.assertEqual(classical_parser._prepare_to_parse('p//q'), 'p/2]q')
        self.assertEqual(classical_parser._prepare_to_parse('p/q//p/p'), 'p/1]q/2]p/1]p')
        self.assertEqual(classical_parser._prepare_to_parse('p / q & p // q'), 'p/1]q∧p/2]q')
        self.assertEqual(classical_parser._prepare_to_parse('/q // q/'), '/1]q/2]q/1]')

    def test_parse_formula(self):
        """Tests both parse and unparse formulae"""
        # Atomic
        p = classical_parser.parse('p')
        self.assertEqual(p, self.p)
        self.assertEqual(classical_parser.unparse(p), 'p')
        # Atomic with metavariable
        A = classical_parser.parse('A')
        self.assertEqual(A, Formula(['A']))

        # Unary
        not_q = classical_parser.parse('~q')
        self.assertEqual(not_q, Formula(['~', self.q]))
        self.assertEqual(classical_parser.unparse(not_q), '~q')
        self.assertEqual(classical_parser.parse('not q'), Formula(['~', self.q]))

        # Binary
        f1 = Formula(['→', self.q, self.p])
        q_then_p = classical_parser.parse('(q → p)')
        self.assertEqual(q_then_p, f1)
        self.assertEqual(classical_parser.unparse(q_then_p), 'q → p')
        self.assertEqual(classical_parser.parse('(q then p)'), f1)
        self.assertEqual(classical_parser.parse('q then p'), f1)
        self.assertEqual(classical_parser.parse('→(q, p)'), f1)

        f1b = Formula(['∧', self.q, self.p])
        self.assertEqual(classical_parser.parse('(q and p)'), f1b)
        self.assertEqual(classical_parser.parse('(q & p)'), f1b)
        self.assertEqual(classical_parser.parse('(q ^ p)'), f1b)

        # Complex
        f2 = Formula(['∨', ['~', f1], ['~', self.p]])
        complex_formula = classical_parser.parse('~(q → p) or ~p')
        self.assertEqual(complex_formula, f2)
        self.assertEqual(classical_parser.unparse(complex_formula), '~(q → p) ∨ ~p')

        # Not well-formed
        self.assertRaises(NotWellFormed, classical_parser.parse, 'pq')
        self.assertRaises(NotWellFormed, classical_parser.parse, '(p)')
        self.assertRaises(NotWellFormed, classical_parser.parse, 'p~p')
        self.assertRaises(NotWellFormed, classical_parser.parse, '(p or q or p)')

    def test_other_parsers(self):
        # Modal parser
        f_native = Formula(['□', self.p])
        f_parsed = modal_parser.parse('□p')
        f_parsed2 = modal_parser.parse('box p')
        f_parsed3 = modal_parser.parse('nec p')
        self.assertEqual(f_native, f_parsed)
        self.assertEqual(f_native, f_parsed2)
        self.assertEqual(f_native, f_parsed3)
        self.assertEqual(modal_parser.unparse(f_native), '□p')

        # LFI parser
        f_native = Formula(['∘', self.p])
        f_parsed = LFI_parser.parse('∘p')
        f_parsed2 = LFI_parser.parse('°p')
        f_parsed3 = LFI_parser.parse('circ p')
        self.assertEqual(f_native, f_parsed)
        self.assertEqual(f_native, f_parsed2)
        self.assertEqual(f_native, f_parsed3)
        self.assertEqual(LFI_parser.unparse(f_native), '∘p')

    def test_parse_inference(self):
        # Regular inferences
        p_p = Inference([self.p], [self.p])
        self.assertEqual(classical_parser.parse('(p / p)'), p_p)
        self.assertEqual(classical_parser.parse('p / p'), p_p)
        self.assertEqual(classical_parser.parse('p, p / p'), Inference([self.p, self.p], [self.p]))
        self.assertEqual(classical_parser.parse('p, p / p, p'), Inference([self.p, self.p], [self.p, self.p]))
        self.assertEqual(classical_parser.parse('(p or ~q) / p, not q'),
                         Inference([Formula(['∨', self.p, ['~', self.q]])], [self.p, Formula(['~', self.q])]))

        # Inferences with empty premises or empty conclusions
        self.assertEqual(classical_parser.parse('/ p'), Inference([], [self.p]))
        self.assertEqual(classical_parser.parse('p /'), Inference([self.p], []))
        empty_inference = Inference([], [])
        self.assertEqual(classical_parser.parse('/'), empty_inference)
        empty_metainference = Inference([], [], level=2)
        self.assertEqual(classical_parser.parse('//'), empty_metainference)
        self.assertEqual(classical_parser.parse('//').level, empty_metainference.level)
        self.assertEqual(classical_parser.parse('(//) ///'), Inference([empty_metainference], [], level=3))

        # Metainferences
        self.assertEqual(classical_parser.parse('(p/p) // (p/p)'), Inference([p_p], [p_p]))
        self.assertEqual(classical_parser.parse('(/) // (/)'), Inference([empty_inference], [empty_inference]))
        self.assertEqual(classical_parser.parse('// (p/p)'), Inference([], [p_p]))
        self.assertEqual(classical_parser.parse('(p/p), (p/p) //'), Inference([p_p, p_p], []))

        # Non-well-formed strings
        # Missing parentheses
        self.assertRaises(NotWellFormed, classical_parser.parse, 'p / p // p / p')

        # Metainferences with incorrect levels
        with warnings.catch_warnings(record=True) as w:
            classical_parser.parse('p // (p / p)')
            assert len(w) == 1
            assert issubclass(w[-1].category, LevelsWarning)
        self.assertRaises(NotWellFormed, classical_parser.parse, 'p // p // p')

        # Test unparse
        self.assertEqual(classical_parser.unparse(classical_parser.parse('/')), '/')
        self.assertEqual(classical_parser.unparse(classical_parser.parse('p/')), 'p /')
        self.assertEqual(classical_parser.unparse(classical_parser.parse('/p')), '/ p')
        self.assertEqual(classical_parser.unparse(classical_parser.parse('p / p')), 'p / p')
        self.assertEqual(classical_parser.unparse(classical_parser.parse('p,p / p,p')), 'p, p / p, p')

        self.assertEqual(classical_parser.unparse(classical_parser.parse('//')), '//')
        self.assertEqual(classical_parser.unparse(classical_parser.parse('// (p/p)')), '// (p / p)')
        self.assertEqual(classical_parser.unparse(classical_parser.parse('(p/p) // (p/p)')), '(p / p) // (p / p)')

    def test_parse_derivation(self):
        # test step
        step1 = classical_parser._parse_derivation_step('p → ((p → p) → p); ax1')
        step2 = DerivationStep(Formula(['→', ['p'], ['→', ['→', ['p'], ['p']], ['p']]]), 'ax1', [])
        self.assertEqual(step1, step2)
        step3 = classical_parser._parse_derivation_step('((p → (p → p)) → (p → p)); mp; [1,2]')
        step4 = DerivationStep(Formula(['→', ['→', ['p'], ['→', ['p'], ['p']]], ['→', ['p'], ['p']]]), 'mp', [1, 2])
        self.assertEqual(step3, step4)

        deriv1 = classical_parser.parse_derivation(
            """p → ((p → p) → p); ax1
            ((p → (p → p)) → (p → p)); mp; [1,2]""")
        deriv2 = Derivation([step1, step3])
        self.assertEqual(deriv1, deriv2)

    def test_parse_sequents(self):
        # Two-sided
        s = classical_parser.parse('A ==> A')
        self.assertEqual(s, Sequent([[Formula(['A'])], [Formula(['A'])]]))
        self.assertEqual(classical_parser.unparse(s), 'A ⇒ A')
        # Two-sided with context variables
        s = classical_parser.parse('Gamma, A, Delta ==> A, Delta')
        self.assertEqual(s, Sequent([['Γ', Formula(['A']), 'Δ'], [Formula(['A']), 'Δ']]))
        self.assertEqual(classical_parser.unparse(s), 'Γ, A, Δ ⇒ A, Δ')
        # Three-sided with context variables
        s = classical_parser.parse('Gamma, A | A, Delta | Delta, A')
        self.assertEqual(s, Sequent([['Γ', Formula(['A'])], [Formula(['A']), 'Δ'], ['Δ', Formula(['A'])]]))
        self.assertEqual(classical_parser.unparse(s), 'Γ, A | A, Δ | Δ, A')
        # With at least one empty side
        s = classical_parser.parse('==> A')
        self.assertEqual(s, Sequent([[], [Formula(['A'])]]))
        self.assertEqual(classical_parser.unparse(s), ' ⇒ A')
        s = classical_parser.parse('A ==>')
        self.assertEqual(s, Sequent([[Formula(['A'])], []]))
        self.assertEqual(classical_parser.unparse(s), 'A ⇒ ')
        s = classical_parser.parse('==>')
        self.assertEqual(s, Sequent([[], []]))
        self.assertEqual(classical_parser.unparse(s), ' ⇒ ')


class TestPredicateParser(unittest.TestCase):
    def test_parse_formula(self):
        # Standard predicate formulae
        f = classical_predicate_parser.parse('P(a)')
        self.assertEqual(f, PredicateFormula(['P', 'a']))
        f = classical_predicate_parser.parse('P(x)')
        self.assertEqual(f, PredicateFormula(['P', 'x']))
        f = classical_predicate_parser.parse('P(f(x))')
        self.assertEqual(f, PredicateFormula(['P', ('f', 'x')]))
        f = classical_predicate_parser.parse('P(f(f(x)))')
        self.assertEqual(f, PredicateFormula(['P', ('f', ('f', 'x'))]))
        self.assertRaises(NotWellFormed, classical_predicate_parser.parse, 'Pa')
        f = classical_predicate_parser.parse('~P(a)')
        self.assertEqual(f, PredicateFormula(['~', ['P', 'a']]))
        f = classical_predicate_parser.parse('~~P(a)')
        self.assertEqual(f, PredicateFormula(['~', ['~', ['P', 'a']]]))
        f = classical_predicate_parser.parse('P(a) and R(a,b)')
        self.assertEqual(f, PredicateFormula(['∧', ['P', 'a'], ['R', 'a', 'b']]))
        self.assertRaises(NotWellFormed, classical_predicate_parser.parse, '∀x P(x)')
        f = classical_predicate_parser.parse('∀x (P(x))')
        self.assertEqual(f, PredicateFormula(['∀', 'x', ['P', 'x']]))
        f = classical_predicate_parser.parse('∀x (P(x) and R(x,y))')
        self.assertEqual(f, PredicateFormula(['∀', 'x', ['∧', ['P', 'x'], ['R', 'x', 'y']]]))
        f = classical_predicate_parser.parse('∀x ((P(x) and R(x,y)))')
        self.assertEqual(f, PredicateFormula(['∀', 'x', ['∧', ['P', 'x'], ['R', 'x', 'y']]]))
        f = classical_predicate_parser.parse('∀x ∈ a (P(x))')
        self.assertEqual(f, PredicateFormula(['∀', 'x', '∈', 'a', ['P', 'x']]))
        f = classical_predicate_parser.parse('∀x ∈ f(f(y)) (P(x))')
        self.assertEqual(f, PredicateFormula(['∀', 'x', '∈', ('f', ('f', 'y')), ['P', 'x']]))
        f = classical_predicate_parser.parse('forall X (X(a))')
        self.assertEqual(f, PredicateFormula(['∀', 'X', ['X', 'a']]))

        # Infix language (with arithmetic)
        f = arithmetic_parser.parse('0=0+0')
        self.assertEqual(f, PredicateFormula(['=', '0', ('+', '0', '0')]))
        f = arithmetic_parser.parse('0 = 0 + 0') # Check that spaces do not matter
        self.assertEqual(f, PredicateFormula(['=', '0', ('+', '0', '0')]))
        f = arithmetic_parser.parse('0=s(0)')
        self.assertEqual(f, PredicateFormula(['=', '0', ('s', '0')]))
        f = arithmetic_parser.parse('0=s(0+0)')
        self.assertEqual(f, PredicateFormula(['=', '0', ('s', ('+', '0', '0'))]))
        f = arithmetic_parser.parse('0=s(s(0))+0')
        self.assertEqual(f, PredicateFormula(['=', '0', ('+', ('s', ('s', '0')), '0')]))
        t = arithmetic_parser.parse_term('0+(0+0)')
        self.assertEqual(t, ('+', '0', ('+', '0', '0')))
        t = arithmetic_parser.parse_term('(0+0)+0')
        self.assertEqual(t, ('+', ('+', '0', '0'), '0'))
        f = arithmetic_parser.parse('s(0)*(0+0)>s(s(0))+0')
        pf = PredicateFormula(['>', ('*', ('s', '0'), ('+', '0', '0')), ('+', ('s', ('s', '0')), '0')])
        self.assertEqual(f, pf)
        f = arithmetic_parser.parse('s(0)*(0+0)>s(s(0))+0 and 0=0')
        self.assertEqual(f, PredicateFormula(['∧', pf, ['=', '0', '0']]))
        f = arithmetic_parser.parse('∀x ∈ 0+s(0) (0=0)')
        self.assertEqual(f, PredicateFormula(['∀', 'x', '∈', ('+', '0', ('s', '0')), ['=', '0', '0']]))
        f = realnumber_arithmetic_parser.parse('1 + 1 = 2')
        self.assertEqual(f, PredicateFormula(['=', ('+', '1', '1'), '2']))

    def test_unparse_formula(self):
        f = classical_predicate_parser.parse('P(a) ∧ R(a,b)')
        self.assertEqual(classical_predicate_parser.unparse(f), 'P(a) ∧ R(a, b)')
        f = classical_predicate_parser.parse('P(f(f(x)))')
        self.assertEqual(classical_predicate_parser.unparse(f), 'P(f(f(x)))')
        f = classical_predicate_parser.parse('∀x (P(x) and R(x,y))')
        self.assertEqual(classical_predicate_parser.unparse(f), '∀x (P(x) ∧ R(x, y))')
        f = classical_predicate_parser.parse('∀x ∈ a (P(x))')
        self.assertEqual(classical_predicate_parser.unparse(f), '∀x ∈ a (P(x))')
        f = arithmetic_parser.parse('0 = 0 + 0')
        self.assertEqual(arithmetic_parser.unparse(f), '0 = 0 + 0')
        f = arithmetic_parser.parse('0=0+(0+0)')
        self.assertEqual(arithmetic_parser.unparse(f), '0 = 0 + (0 + 0)')
        f = arithmetic_parser.parse('0=0+s(0+0)')
        self.assertEqual(arithmetic_parser.unparse(f), '0 = 0 + s(0 + 0)')

    def test_godel_encoding_decoding(self):
        # Just encodes and then decodes a bunch of formulae and checks that the decoded is equal to the original
        formulae = ['0=0+0', '0=s(0)', '0=s(s(0))+0', 's(0)*(0+0)>s(s(0))+0', 's(0)*(0+0)>s(s(0))+0∧0=0',
                    '∀x∈0+s(0)(0=0)', '∀x12(0=x12)', '∀X35∀x12X(x12)', 'Tr(quote(0=0))', 'Tr(quote(Tr(quote(0=0))))']
        for f in formulae:
            f_encoded = arithmetic_truth_parser.godel_encode(f)
            f_decoded = arithmetic_truth_parser.godel_decode(f_encoded)
            self.assertEqual(f, f_decoded)

        self.assertEqual(arithmetic_truth_parser._prepare_to_parse('Tr(quote(0=0))'), 'Tr(0490)')
        self.assertEqual(arithmetic_truth_parser.parse('Tr(quote(0=0))'), PredicateFormula(['Tr', '0490']))
        self.assertTrue(arithmetic_truth_language.is_well_formed(arithmetic_truth_parser.parse('Tr(quote(0=0))')))


if __name__ == '__main__':
    unittest.main()
