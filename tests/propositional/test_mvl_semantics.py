import unittest
import time
from copy import deepcopy

from logics.instances.propositional.languages import classical_infinite_language_with_sent_constants as cl_language
from logics.utils.formula_generators.generators_biased import random_formula_generator
from logics.classes.propositional import Formula, Inference
from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics as classical_semantics
from logics.instances.propositional.many_valued_semantics import K3_mvl_semantics as K3, LP_mvl_semantics as LP, \
    ST_mvl_semantics as ST, TS_mvl_semantics as TS, LFI1_mvl_semantics as LFI1
from logics.instances.propositional.many_valued_semantics import classical_logic_up_to_level, empty_logic_up_to_level
from logics.classes.propositional.semantics import MixedMetainferentialSemantics, IntersectionLogic, UnionLogic


class TestMixedManyValuedSemantics(unittest.TestCase):
    def setUp(self):
        self.p = Formula(['p'])
        self.notp = Formula(['~', ['p']])
        self.q = Formula(['q'])
        self.pthenq = Formula(['→', ['p'], ['q']])
        self.pthenp = Formula(['→', ['p'], ['p']])
        self.p1 = Formula(['p1'])
        self.p2 = Formula(['p2'])

        # The names of the variables use _ for comma, __ for /, ___ for ///, and so on
        self.p__p = Inference([self.p], [self.p])  # p / p
        self.p__q = Inference([self.p], [self.q])  # p / q
        self.p_pthenq__q = Inference([self.p, self.pthenq], [self.q])  # p, p → q / q
        self.q_pthenq__p = Inference([self.q, self.pthenq], [self.p])  # q, p → q / p
        self.p1__p2 = Inference([self.p1], [self.p2])  # p1 / p2
        self.explosion = Inference([self.p, self.notp], [self.q])  # p, ~p / q

        self.p__p___p__p = Inference([self.p__p], [self.p__p])  # p / p // p / p
        self.p__p___p__q = Inference([self.p__p], [self.p__q])  # p / p // p / q
        self.p__q___p__p = Inference([self.p__q], [self.p__p])  # p / q // p / p
        self.p__q___p1__p2 = Inference([self.p__q], [self.p1__p2])  # p / q // p1 / p2

        self.transitivity_p1 = Inference([Formula(['p'])], [Formula(['q'])])  # p / q
        self.transitivity_p2 = Inference([Formula(['q'])], [Formula(['r'])])  # q / r
        self.transitivity_c = Inference([Formula(['p'])], [Formula(['r'])])  # p / r
        self.transitivity = Inference([self.transitivity_p1, self.transitivity_p2], [self.transitivity_c])
        # (p / q), (q / r) // (p / r)

        self.mminf = Inference([self.p__p___p__p], [self.p__q___p1__p2])  # p / p // p / p /// p / q // p1 / p2

    # TESTS WITH CLASSICAL LOGIC
    def test_classical_truth_functions(self):
        self.assertEqual(classical_semantics.apply_truth_function('~', '0'), '1')
        self.assertEqual(classical_semantics.apply_truth_function('~', '1'), '0')

        self.assertEqual(classical_semantics.apply_truth_function('∧', '1', '1'), '1')
        self.assertEqual(classical_semantics.apply_truth_function('∧', '1', '0'), '0')
        self.assertEqual(classical_semantics.apply_truth_function('∧', '0', '1'), '0')
        self.assertEqual(classical_semantics.apply_truth_function('∧', '0', '0'), '0')

        # Test using a callable instead of a nested list
        def classical_conjunction(value1, value2):
            return str(min(int(value1), int(value2)))
        classical_semantics2 = classical_semantics
        classical_semantics2.truth_function_dict['∧'] = classical_conjunction

        self.assertEqual(classical_semantics2.apply_truth_function('∧', '1', '1'), '1')
        self.assertEqual(classical_semantics2.apply_truth_function('∧', '1', '0'), '0')
        self.assertEqual(classical_semantics2.apply_truth_function('∧', '0', '1'), '0')
        self.assertEqual(classical_semantics2.apply_truth_function('∧', '0', '0'), '0')

    def test_valuation_method(self):
        self.assertEqual(classical_semantics.valuation(Formula(['p']), {'p': '1'}), '1')
        self.assertEqual(classical_semantics.valuation(Formula(['A']), {'A': '1'}), '1')
        self.assertEqual(classical_semantics.valuation(Formula(['~', ['p']]), {'p': '1'}), '0')
        self.assertEqual(classical_semantics.valuation(Formula(['→', ['p'], ['q']]), {'p': '1', 'q': '0'}), '0')
        self.assertEqual(classical_semantics.valuation(Formula(['⊥'])), '0')

    def test_satisfies(self):
        # Formulae
        self.assertTrue(classical_semantics.satisfies(self.p, {'p': '1'}))
        # Calling satisfies q with q not present in the kwargs should raise KeyError
        self.assertRaises(KeyError, classical_semantics.satisfies, self.q, {'p': '1'})
        self.assertFalse(classical_semantics.satisfies(self.p, {'p': '0'}))
        self.assertFalse(classical_semantics.satisfies(self.pthenq, {'p': '1', 'q':'0'}))

        # Inferences
        self.assertTrue(classical_semantics.satisfies(self.p__p, {'p': '1'}))
        self.assertTrue(classical_semantics.satisfies(self.p__p, {'p': '0'}))
        self.assertTrue(classical_semantics.satisfies(self.p__q, {'p': '1', 'q': '1'}))
        self.assertFalse(classical_semantics.satisfies(self.p__q, {'p': '1', 'q': '0'}))
        self.assertTrue(classical_semantics.satisfies(self.p_pthenq__q, {'p': '1', 'q': '1'}))
        self.assertTrue(classical_semantics.satisfies(self.p_pthenq__q, {'p': '1', 'q': '0'}))
        self.assertFalse(classical_semantics.satisfies(self.q_pthenq__p, {'p': '0', 'q': '1'}))

        # Metainferences
        self.assertTrue(classical_semantics.satisfies(self.p__p___p__p, {'p': '1'}))
        self.assertTrue(classical_semantics.satisfies(self.p__p___p__q, {'p': '1', 'q': '1'}))
        self.assertFalse(classical_semantics.satisfies(self.p__p___p__q, {'p': '1', 'q': '0'}))
        self.assertTrue(classical_semantics.satisfies(self.p__q___p__p, {'p': '1', 'q': '1'}))
        self.assertTrue(classical_semantics.satisfies(self.p__q___p__p, {'p': '1', 'q': '0'}))

    def test_local_validity(self):
        # For formulae
        self.assertTrue(classical_semantics.is_tautology(self.pthenp))
        self.assertTrue(classical_semantics.is_contradiction(Formula(['~', self.pthenp])))
        self.assertFalse(classical_semantics.is_tautology(self.pthenq))
        self.assertFalse(classical_semantics.is_contradiction(self.pthenq))
        self.assertTrue(classical_semantics.is_contingent(self.pthenq))

        # For inferences
        self.assertTrue(classical_semantics.is_locally_valid(self.p__p))
        self.assertFalse(classical_semantics.is_locally_valid(self.p__q))
        self.assertTrue(classical_semantics.is_locally_valid(self.p_pthenq__q))
        self.assertFalse(classical_semantics.is_locally_valid(self.q_pthenq__p))
        # Test inferences of level 1 with only sentential constants
        self.assertTrue(classical_semantics.is_valid(Inference([Formula(['⊤'])], [Formula(['⊤'])])))
        self.assertFalse(classical_semantics.is_valid(Inference([Formula(['⊤'])], [Formula(['⊥'])])))

        # For metainferences
        self.assertTrue(classical_semantics.is_locally_valid(self.p__p___p__p))
        self.assertFalse(classical_semantics.is_locally_valid(self.p__p___p__q))
        self.assertTrue(classical_semantics.is_locally_valid(self.p__q___p__p))
        # This one should be locally invalid and globally valid
        self.assertFalse(classical_semantics.is_locally_valid(self.p__q___p1__p2))

    def test_global_validity(self):
        # For level 1 inferences it should behave in the same way as above
        self.assertTrue(classical_semantics.is_globally_valid(self.p__p___p__p))
        self.assertFalse(classical_semantics.is_globally_valid(self.p__p___p__q))
        self.assertTrue(classical_semantics.is_globally_valid(self.p__q___p__p))
        # This one should be locally invalid and globally valid
        self.assertTrue(classical_semantics.is_globally_valid(self.p__q___p1__p2))

        # Global validity all the way down
        self.assertTrue(classical_semantics.is_globally_valid3(Inference([self.pthenp], [self.pthenp])))
        self.assertTrue(classical_semantics.is_globally_valid3(Inference([self.p], [self.q])))
        self.assertFalse(classical_semantics.is_globally_valid3(Inference([self.pthenp], [self.p])))

        # Lastly mm5 should be globally valid 1 and globally invalid 2
        self.assertTrue(classical_semantics.is_globally_valid(self.mminf))
        self.assertFalse(classical_semantics.is_globally_valid2(self.mminf))

    def test_truth_table_method(self):
        f = Formula(['→', self.pthenq, self.pthenp])
        truth_table = classical_semantics.truth_table(f)[1]
        correct_answer = [['1', '1', '1', '1', '1'],
                          ['1', '0', '0', '1', '1'],
                          ['0', '1', '1', '1', '1'],
                          ['0', '0', '1', '1', '1']]
        for x in truth_table:
            # Evaluate like this because the order of the rows in the truth table comes out differently for some reason
            self.assertTrue(x in correct_answer)

        # Formula with Bottom
        subformulae, truth_table = classical_semantics.truth_table(Formula(['⊥']))
        self.assertEqual(subformulae, [['⊥']])
        self.assertEqual(truth_table, [['0']])

        # Inference
        i = Inference([self.p], [self.p])
        subformulae, truth_table = classical_semantics.truth_table(i)
        self.assertEqual(subformulae, [self.p])
        self.assertEqual(truth_table, [['1'], ['0']])

        # Metainference
        i = Inference([Inference([self.p], [self.p])], [Inference([self.p], [self.q])])  # p / p // p / q
        subformulae, truth_table = classical_semantics.truth_table(i)
        self.assertEqual(subformulae, [self.p, self.q])
        self.assertEqual(truth_table, [['1', '1'], ['1', '0'], ['0', '1'], ['0', '0']])

    # TESTS WITH OTHER MVLs
    def test_other_mvls(self):
        # Inferences
        # TS has no valid inferences, so it should not satisfy p / p
        identity = self.p__p
        self.assertFalse(TS.is_valid(identity))
        for logic in (K3, LP, ST):
            self.assertTrue(logic.is_valid(identity))

        # K3 has no tautologies
        tautology = self.pthenp
        for logic in (K3, TS):
            self.assertFalse(logic.is_tautology(tautology))  # p → p
            self.assertFalse(logic.is_valid(Inference([], [tautology])))  # / p → p
        for logic in (LP, ST):
            self.assertTrue(logic.is_tautology(tautology))  # p → p
            self.assertTrue(logic.is_valid(Inference([], [tautology])))  # / p → p

        # Modus ponens is invalid in LP and TS, valid in the rest
        modus_ponens = self.p_pthenq__q
        for logic in (LP, TS):
            self.assertFalse(logic.is_valid(modus_ponens))
        for logic in (K3, ST):
            self.assertTrue(logic.is_valid(modus_ponens))

        # Explosion is invalid in LP and LFI1, but valid if we add consistent p
        for logic in (LP, LFI1):
            self.assertFalse(logic.is_valid(self.explosion))
        valid_explosion = Inference([self.p, self.notp, Formula(["◦", ["p"]])], [self.q])  # p, ~p, ◦p / q
        self.assertTrue(LFI1.is_valid(valid_explosion))

        # Metainferences
        # Transitivity as a metainference, (p / q), (q / r) // (p / r), should be invadilid in ST, valid in the rest
        self.assertFalse(ST.is_locally_valid(self.transitivity))
        for logic in (K3, LP, TS):
            self.assertTrue(logic.is_locally_valid(self.transitivity))

        # Same inferences as above but with identity as a metainference
        identity_as_metainf = Inference([], [self.p__p])
        self.assertFalse(TS.is_locally_valid(identity_as_metainf))
        for l in (K3, LP, ST):
            self.assertTrue(l.is_locally_valid(identity_as_metainf))

        # // p / p
        self.assertFalse(K3.is_valid(Inference([], [Inference([], [tautology])])))

    def test_mixed_metainferntial_logics(self):
        # TS / ST should be like classical logic up to level 1
        # ST / TS should be the empty logic up to level 1
        TSST = MixedMetainferentialSemantics([TS, ST])
        STTS = MixedMetainferentialSemantics([ST, TS])

        # p / p // p / p
        self.assertTrue(TSST.is_locally_valid(self.p__p___p__p))
        self.assertFalse(STTS.is_locally_valid(self.p__p___p__p))

        # Transitivity valid in TSST and in classical logic
        self.assertTrue(classical_semantics.is_locally_valid(self.transitivity))
        self.assertTrue(TSST.is_locally_valid(self.transitivity))
        # / p // / q, / q // / r  /// / p // / r, call this meta-transitivity
        meta_transitivity_p1 = Inference([Inference([], [Formula(['p'])])], [Inference([], [Formula(['q'])])])
        meta_transitivity_p2 = Inference([Inference([], [Formula(['q'])])], [Inference([], [Formula(['r'])])])
        meta_transitivity_c = Inference([Inference([], [Formula(['p'])])], [Inference([], [Formula(['r'])])])
        meta_transitivity = Inference([meta_transitivity_p1, meta_transitivity_p2], [meta_transitivity_c])
        self.assertTrue(classical_semantics.is_locally_valid(meta_transitivity))
        self.assertFalse(TSST.is_locally_valid(meta_transitivity))

        # However, it should be valid in [[ST, TS], [TS, ST]]
        STTS_TSST = MixedMetainferentialSemantics([[ST, TS], [TS, ST]])
        self.assertTrue(STTS_TSST.is_locally_valid(meta_transitivity))

        # Global validity
        self.assertTrue(TSST.is_globally_valid(self.p__p___p__p))
        self.assertFalse(STTS.is_globally_valid(self.p__p___p__p))

        # The recursive definitions of classical logic and empty logic up to a given level
        self.assertEqual(classical_logic_up_to_level(1), ST)
        self.assertEqual(empty_logic_up_to_level(1), TS)
        self.assertEqual(classical_logic_up_to_level(2), TSST)
        self.assertEqual(empty_logic_up_to_level(2), STTS)
        self.assertEqual(classical_logic_up_to_level(3), STTS_TSST)

    def test_union_intersection_logics(self):
        U_TS_ST = UnionLogic([TS, ST])  # Should be equally strong to ST
        I_TS_ST = IntersectionLogic([TS, ST])  # Should be equally strong to TS

        identity = self.p__p
        self.assertFalse(I_TS_ST.is_valid(identity))
        self.assertTrue(U_TS_ST.is_valid(identity))

        modus_ponens = self.p_pthenq__q
        self.assertFalse(I_TS_ST.is_valid(modus_ponens))
        self.assertTrue(U_TS_ST.is_valid(modus_ponens))

    def test_valuation_fast_version(self):
        K3b = deepcopy(K3)
        K3b.use_molecular_valuation_fast_version = True
        for _1 in range(8):
            time1 = 0
            time2 = 0
            for _2 in range(250):
                f = random_formula_generator._exact_depth_some_atomics(3, ['p', 'q', 'r'], cl_language)
                truth_value_combinations = K3._get_truth_value_combinations(f)
                for combination in truth_value_combinations:
                    atomic_valuation_dict = K3._get_atomic_valuation_dict(f, combination)
                    start1 = time.time()
                    val1 = K3.valuation(f, atomic_valuation_dict)
                    time1 += time.time() - start1
                    start2 = time.time()
                    val2 = K3b.valuation(f, atomic_valuation_dict)
                    time2 += time.time() - start2
                    self.assertEqual(val1, val2)
            self.assertTrue(time2 < time1)


if __name__ == '__main__':
    unittest.main()
