import unittest
from copy import deepcopy

from logics.classes.propositional import Formula, Inference
from logics.classes.propositional.semantics.mapped_logic import powerset

from logics.instances.propositional.mapped_logic_semantics import \
    two_valued_truth_preservation_from_all_premises_to_some_conclusions_logic   as TrueTrue_AllSome, \
    two_valued_falsity_preservation_from_all_premises_to_some_conclusions_logic as FalseFalseAllSome, \
    two_valued_truth_preservation_from_all_premises_to_all_conclusions_logic    as TrueTrue_AllAlle, \
    two_valued_falsity_preservation_from_all_premises_to_all_conclusions_logic  as FalseFalseAllAll

from logics.instances.propositional.mapped_logic_semantics import \
    three_valued_strict_strict_from_all_premises_to_some_conclusions_logic     as SS, \
    three_valued_strict_tolerant_from_all_premises_to_some_conclusions_logic   as ST, \
    three_valued_tolerant_tolerant_from_all_premises_to_some_conclusions_logic as TT, \
    three_valued_tolerant_strict_from_all_premises_to_some_conclusions_logic   as TS, \
    intersective_mixed_logic_between_ss_and_tt_relations_all_some_logic        as SSintTT


class TestMappingMatrix(unittest.TestCase):
    def setUp(self):
        self.M0 = deepcopy(ST.mapping_constraints)
        self.M1 = deepcopy(ST.mapping_constraints)
        self.M0._fill_matrix(0)
        self.M1._fill_matrix(1)

    def test_powerset(self):
        # Not properly part of the class.
        self.assertEqual(list(powerset(TrueTrue_AllSome.truth_values)), [(), ('1',), ('0',), ('1', '0')])
        self.assertEqual(list(powerset(SS.truth_values)),
                         [(), ('1',), ('i',), ('0',), ('1', 'i'), ('1', '0'), ('i', '0'), ('1', 'i', '0')])

    def test_fill_matrix(self):
        # For two-valued constraints
        self.m = deepcopy(FalseFalseAllAll.mapping_constraints)
        self.m._fill_matrix(0)
        self.assertEqual(self.m.boolean_matrix, [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]])
        self.m._fill_matrix(1)
        self.assertEqual(self.m.boolean_matrix, [[1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]])
        # For three-valued constraints
        self.assertNotEqual(self.M0.boolean_matrix, [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]])
        self.assertEqual(self.M0.boolean_matrix, [ [0, 0, 0, 0, 0, 0, 0, 0],
                                                  [0, 0, 0, 0, 0, 0, 0, 0],
                                                  [0, 0, 0, 0, 0, 0, 0, 0],
                                                  [0, 0, 0, 0, 0, 0, 0, 0],
                                                  [0, 0, 0, 0, 0, 0, 0, 0],
                                                  [0, 0, 0, 0, 0, 0, 0, 0],
                                                  [0, 0, 0, 0, 0, 0, 0, 0],
                                                  [0, 0, 0, 0, 0, 0, 0, 0], ])

    def test_matrix_operations(self):
        # Inclusion
        self.assertTrue(TS.mapping_constraints.is_included_in(ST.mapping_constraints))
        self.assertTrue(TS.mapping_constraints.is_included_in(TS.mapping_constraints))
        self.assertFalse(ST.mapping_constraints.is_included_in(TS.mapping_constraints))
        # Negation
        self.assertEqual(self.M0.matrix_negation().boolean_matrix, self.M1.boolean_matrix)
        self.assertEqual(self.M1.matrix_negation().boolean_matrix, self.M0.boolean_matrix)
        self.assertNotEqual(self.M1.matrix_negation().boolean_matrix, ST.mapping_constraints.boolean_matrix)
        self.assertNotEqual(TT.mapping_constraints.matrix_negation().boolean_matrix,
                            SS.mapping_constraints.boolean_matrix)
        # Conjunction
        self.assertEqual(self.M0.matrix_conjunction(self.M1).boolean_matrix, self.M0.boolean_matrix)
        self.assertEqual(SS.mapping_constraints.matrix_conjunction(TT.mapping_constraints).boolean_matrix,
                         SSintTT.mapping_constraints.boolean_matrix)
        self.assertNotEqual(SS.mapping_constraints.matrix_conjunction(TT.mapping_constraints).boolean_matrix,
                         ST.mapping_constraints.boolean_matrix)
        # Disjunction
        self.assertEqual(self.M1.matrix_disjunction(self.M0).boolean_matrix, self.M1.boolean_matrix)
        self.assertEqual(SS.mapping_constraints.matrix_disjunction(TT.mapping_constraints).boolean_matrix,
                         ST.mapping_constraints.boolean_matrix)
        self.assertNotEqual(SS.mapping_constraints.matrix_disjunction(TT.mapping_constraints).boolean_matrix,
                         TS.mapping_constraints.boolean_matrix)


class TestMappedManyValuedSemantics(unittest.TestCase):
    def setUp(self):
        self.p = Formula(['p'])
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

    # TESTS WITH CLASSICAL LOGIC
    def test_two_valued_truth_functions(self):
        self.assertEqual(TrueTrue_AllSome.apply_truth_function('~', '0'), '1')
        self.assertEqual(TrueTrue_AllSome.apply_truth_function('~', '1'), '0')

        self.assertEqual(TrueTrue_AllSome.apply_truth_function('∧', '1', '1'), '1')
        self.assertEqual(TrueTrue_AllSome.apply_truth_function('∧', '1', '0'), '0')
        self.assertEqual(TrueTrue_AllSome.apply_truth_function('∧', '0', '1'), '0')
        self.assertEqual(TrueTrue_AllSome.apply_truth_function('∧', '0', '0'), '0')

    def test_valuation_method(self):
        self.assertEqual(TrueTrue_AllSome.valuation(Formula(['p']), {'p': '1'}), '1')
        self.assertEqual(TrueTrue_AllSome.valuation(Formula(['A']), {'A': '1'}), '1')
        self.assertEqual(TrueTrue_AllSome.valuation(Formula(['~', ['p']]), {'p': '1'}), '0')
        self.assertEqual(TrueTrue_AllSome.valuation(Formula(['→', ['p'], ['q']]), {'p': '1', 'q': '0'}), '0')
        self.assertEqual(TrueTrue_AllSome.valuation(Formula(['⊥'])), '0')

    def test_satisfies(self):
        # Ensure that TrueTrue_AllSome is mapped defined for empty premises:
        TrueTrue_AllSome.mapping_constraints.boolean_matrix[0] = \
            TrueTrue_AllSome.mapping_constraints.boolean_matrix[2]
        # Formulae
        self.assertTrue(TrueTrue_AllSome.satisfies(self.p, {'p': '1'}))
        # Calling satisfies q with q not present in the kwargs should raise KeyError
        self.assertRaises(KeyError, TrueTrue_AllSome.satisfies, self.q, {'p': '1'})
        self.assertTrue(TrueTrue_AllSome.satisfies(self.p, {'p': '0'}))
        self.assertTrue(TrueTrue_AllSome.satisfies(self.pthenq, {'p': '1', 'q':'0'}))

        # Inferences
        self.assertTrue(TrueTrue_AllSome.satisfies(self.p__p, {'p': '1'}))
        self.assertTrue(TrueTrue_AllSome.satisfies(self.p__p, {'p': '0'}))
        self.assertTrue(TrueTrue_AllSome.satisfies(self.p__q, {'p': '1', 'q': '1'}))
        self.assertFalse(TrueTrue_AllSome.satisfies(self.p__q, {'p': '1', 'q': '0'}))
        self.assertTrue(TrueTrue_AllSome.satisfies(self.p_pthenq__q, {'p': '1', 'q': '1'}))
        self.assertTrue(TrueTrue_AllSome.satisfies(self.p_pthenq__q, {'p': '1', 'q': '0'}))
        self.assertFalse(TrueTrue_AllSome.satisfies(self.q_pthenq__p, {'p': '0', 'q': '1'}))

        # TrueTrue_AllSome instance is not classically defined for empty-premises. Define it classically:
        TrueTrue_AllSome.mapping_constraints.boolean_matrix[0] = \
            TrueTrue_AllSome.mapping_constraints.boolean_matrix[1]
        # Formulae
        self.assertTrue(TrueTrue_AllSome.satisfies(self.p, {'p': '1'}))
        # Calling satisfies q with q not present in the kwargs should raise KeyError
        self.assertRaises(KeyError, TrueTrue_AllSome.satisfies, self.q, {'p': '1'})
        self.assertFalse(TrueTrue_AllSome.satisfies(self.p, {'p': '0'}))
        self.assertFalse(TrueTrue_AllSome.satisfies(self.pthenq, {'p': '1', 'q':'0'}))

        # Inferences
        self.assertTrue(TrueTrue_AllSome.satisfies(self.p__p, {'p': '1'}))
        self.assertTrue(TrueTrue_AllSome.satisfies(self.p__p, {'p': '0'}))
        self.assertTrue(TrueTrue_AllSome.satisfies(self.p__q, {'p': '1', 'q': '1'}))
        self.assertFalse(TrueTrue_AllSome.satisfies(self.p__q, {'p': '1', 'q': '0'}))
        self.assertTrue(TrueTrue_AllSome.satisfies(self.p_pthenq__q, {'p': '1', 'q': '1'}))
        self.assertTrue(TrueTrue_AllSome.satisfies(self.p_pthenq__q, {'p': '1', 'q': '0'}))
        self.assertFalse(TrueTrue_AllSome.satisfies(self.q_pthenq__p, {'p': '0', 'q': '1'}))

    def test_local_validity(self):
        # Ensure that TrueTrue_AllSome is mapped defined for empty premises:
        TrueTrue_AllSome.mapping_constraints.boolean_matrix[0] = \
            TrueTrue_AllSome.mapping_constraints.boolean_matrix[2]
        # For formulae
        self.assertTrue(TrueTrue_AllSome.is_tautology(self.pthenp))
        self.assertFalse(TrueTrue_AllSome.is_contradiction(Formula(['~', self.pthenp])))
        self.assertTrue(TrueTrue_AllSome.is_tautology(self.pthenq))
        self.assertFalse(TrueTrue_AllSome.is_contradiction(self.pthenq))
        self.assertFalse(TrueTrue_AllSome.is_contingent(self.pthenq))

        # For inferences
        self.assertTrue(TrueTrue_AllSome.is_locally_valid(self.p__p))
        self.assertFalse(TrueTrue_AllSome.is_locally_valid(self.p__q))
        self.assertTrue(TrueTrue_AllSome.is_locally_valid(self.p_pthenq__q))
        self.assertFalse(TrueTrue_AllSome.is_locally_valid(self.q_pthenq__p))
        # Test inferences of level 1 with only sentential constants
        self.assertTrue(TrueTrue_AllSome.is_valid(Inference([Formula(['⊤'])], [Formula(['⊤'])])))
        self.assertFalse(TrueTrue_AllSome.is_valid(Inference([Formula(['⊤'])], [Formula(['⊥'])])))

        # TrueTrue_AllSome instance is not classically defined for empty-premises. Define it classically:
        TrueTrue_AllSome.mapping_constraints.boolean_matrix[0] = \
            TrueTrue_AllSome.mapping_constraints.boolean_matrix[1]
        # For formulae
        self.assertTrue(TrueTrue_AllSome.is_tautology(self.pthenp))
        self.assertTrue(TrueTrue_AllSome.is_contradiction(Formula(['~', self.pthenp])))
        self.assertFalse(TrueTrue_AllSome.is_tautology(self.pthenq))
        self.assertFalse(TrueTrue_AllSome.is_contradiction(self.pthenq))
        self.assertTrue(TrueTrue_AllSome.is_contingent(self.pthenq))

        # For inferences
        self.assertTrue(TrueTrue_AllSome.is_locally_valid(self.p__p))
        self.assertFalse(TrueTrue_AllSome.is_locally_valid(self.p__q))
        self.assertTrue(TrueTrue_AllSome.is_locally_valid(self.p_pthenq__q))
        self.assertFalse(TrueTrue_AllSome.is_locally_valid(self.q_pthenq__p))
        # Test inferences of level 1 with only sentential constants
        self.assertTrue(TrueTrue_AllSome.is_valid(Inference([Formula(['⊤'])], [Formula(['⊤'])])))
        self.assertFalse(TrueTrue_AllSome.is_valid(Inference([Formula(['⊤'])], [Formula(['⊥'])])))


if __name__ == '__main__':
    unittest.main()
