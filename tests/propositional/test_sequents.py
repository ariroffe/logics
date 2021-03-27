import unittest

from logics.classes.propositional import Formula
from logics.utils.parsers import classical_parser
from logics.instances.propositional.languages import classical_infinite_language_with_sent_constants_nobiconditional \
    as language
from logics.classes.propositional.proof_theories import SequentNode
from logics.instances.propositional.sequents import LKminEA


class TestTableauxSystem(unittest.TestCase):
    def setUp(self):
        self.A = Formula(['A'])
        self.notA = Formula(['~', ['A']])
        self.B = Formula(['B'])
        self.notB = Formula(['~', ['B']])
        self.C = Formula(['C'])

    def test_main_and_context_formulae(self):
        sequent = classical_parser.parse('Gamma, ~A, Delta, ~B ==> C, Pi, A')
        self.assertEqual(sequent.main_formulae(language), [self.notA, self.notB, self.C, self.A])
        self.assertEqual(sequent.context_formulae(language), ['Γ', 'Δ', 'Π'])

    def test_substitute(self):
        # Substitute method
        seq = classical_parser.parse("Gamma, A ==> B, Delta")

        # Side substitute
        subst = seq.side_substitute(seq.antecedent, language, 'Γ', 'Δ')
        self.assertEqual(subst, ['Δ', Formula(['A'])])

        # Sequent substitute
        # Substituting an element
        ## A context variable
        ### For an element
        subst1 = seq.substitute(language, 'Γ', 'Δ')
        self.assertEqual(subst1, classical_parser.parse("Delta, A ==> B, Delta"))
        self.assertEqual(seq, classical_parser.parse("Gamma, A ==> B, Delta"))  # did not modify it

        subst2 = seq.substitute(language, 'Γ', Formula(['~', ['A']]))
        self.assertEqual(subst2, classical_parser.parse("~A, A ==> B, Delta"))

        ### For a list
        subst3 = seq.substitute(language, 'Γ', [Formula(['C']), Formula(['D'])])
        self.assertEqual(subst3, classical_parser.parse("C, D, A ==> B, Delta"))

        subst4 = seq.substitute(language, 'Γ', ['Γ', Formula(['D'])])
        self.assertEqual(subst4, classical_parser.parse("Γ, D, A ==> B, Delta"))

        ## A formula
        ### For an element
        subst5 = seq.substitute(language, Formula(['A']), Formula(['~', ['C']]))
        self.assertEqual(subst5, classical_parser.parse("Gamma, ~C ==> B, Delta"))

        subst6 = seq.substitute(language, Formula(['A']), 'Δ')
        self.assertEqual(subst6, classical_parser.parse("Gamma, Delta ==> B, Delta"))

        seq2 = classical_parser.parse("Gamma, ~~A ==> B, Delta")
        subst7 = seq2.substitute(language, Formula(['~', ['A']]), Formula(['C']))  # Can substitute subformulae here
        self.assertEqual(subst7, classical_parser.parse("Gamma, ~C ==> B, Delta"))

        subst8 = seq2.substitute(language, Formula(['~',['A']]), 'Δ')  # Should do nothing here
        self.assertEqual(subst8, classical_parser.parse("Gamma, ~~A ==> B, Delta"))

        ### For a list
        subst9 = seq.substitute(language, Formula(['A']), ['Γ', Formula(['D'])])
        self.assertEqual(subst9, classical_parser.parse("Gamma, Gamma, D ==> B, Delta"))

        subst10 = seq2.substitute(language, Formula(['~', ['A']]), ['Γ', Formula(['D'])])  # Should do nothing here
        self.assertEqual(subst10, classical_parser.parse("Gamma, ~~A ==> B, Delta"))

        # --------
        # Substituting a list
        ## For an element
        subst11 = seq.substitute(language, ['Γ', Formula(['A'])], Formula(['D']))
        self.assertEqual(subst11, classical_parser.parse("D ==> B, Delta"))

        ## For another list
        subst12 = seq.substitute(language, ['Γ', Formula(['A'])], ['Δ', Formula(['D'])])
        self.assertEqual(subst12, classical_parser.parse("Delta, D ==> B, Delta"))

    def test_instantiate(self):
        # Instantiate method
        sequent1 = classical_parser.parse('Gamma, A, Delta, ~p ==>')
        sequent2 = classical_parser.parse('Delta, B, Delta, ~p ==>')
        self.assertEqual(sequent1.instantiate(language, {'A': self.B, 'Γ': ['Δ'], 'Δ': ['Δ']}),
                         sequent2)

        sequent1 = classical_parser.parse('Gamma, A, Delta, ~B ==>')
        sequent2 = classical_parser.parse('Delta, B, Delta, ~B ==>')
        self.assertRaises(ValueError, sequent1.instantiate, language, {'A': self.B, 'Γ': ['Δ']})
        self.assertEqual(sequent1.instantiate(language, {'A': self.B, 'Γ': ['Δ'], 'Δ': ['Δ'], 'B': self.B}), sequent2)

        sequent2 = classical_parser.parse('Delta, A, Sigma, B, Delta, ~B ==>')
        self.assertEqual(sequent1.instantiate(language, {'A': self.B, 'Γ': ['Δ', self.A, 'Σ'], 'Δ': ['Δ'],
                                                         'B': self.B}), sequent2)

        sequent1 = classical_parser.parse('Γ ⇒ Δ, A ∨ B, Π, Σ')
        subst_dict = {'Γ': ['Γ', Formula(['q']), Formula(['q']), 'Δ'],
                      'A': Formula(['~', ['∧', ['q'], ['q']]]), 'B': Formula(['q']),
                      'Δ': ['Π'], 'Π': ['Θ'], 'Σ': []}
        sequent2 = classical_parser.parse('Γ, q, q, Δ ⇒ Π, (~(q ∧ q) ∨ q), Θ')
        self.assertEqual(sequent1.instantiate(language, subst_dict), sequent2)

    def test_get_rule_pattern(self):
        # Context variables everywhere
        sequent = classical_parser.parse('Gamma, A, Delta, ~B, Pi ==>')
        self.assertEqual(sequent._get_rule_pattern(sequent[0], language.context_variables),
                         ([self.A, self.notB], True, True, []))

        # No context in the middle
        sequent = classical_parser.parse('Gamma, A, ~B, Pi ==>')
        self.assertEqual(sequent._get_rule_pattern(sequent[0], language.context_variables),
                         ([self.A, self.notB], True, True, [(0, 1)]))

        # No context right
        sequent = classical_parser.parse('Gamma, A, Delta, ~B ==>')
        self.assertEqual(sequent._get_rule_pattern(sequent[0], language.context_variables),
                         ([self.A, self.notB], True, False, []))

        # No context variables at all
        sequent = classical_parser.parse('A, ~B, A ==>')
        self.assertEqual(sequent._get_rule_pattern(sequent[0], language.context_variables),
                         ([self.A, self.notB, self.A], False, False, [(0, 1), (1, 2)]))

    def test_get_possible_indexes(self):
        # Test 1 - Only one possibility
        rule_sequent = classical_parser.parse('Gamma, A ==>')
        instance_sequent = classical_parser.parse('Gamma, A, B ==>')
        pattern, left_context, right_context, together = rule_sequent._get_rule_pattern(rule_sequent[0],
                                                                                        language.context_variables)
        result = instance_sequent._get_possible_indexes(instance_sequent[0], language,
                                                        pattern, left_context, right_context, together,
                                                        possible_subst_dicts=[{}])
        self.assertEqual(result, [((2,), [{'A': self.B}])])

        # Test 2 - Previous restrictions
        # Not possible
        result = instance_sequent._get_possible_indexes(instance_sequent[0], language,
                                                        pattern, left_context, right_context, together,
                                                        possible_subst_dicts=[{'A': self.A}])
        self.assertEqual(result, [])
        # Possible
        result = instance_sequent._get_possible_indexes(instance_sequent[0], language,
                                                        pattern, left_context, right_context, together,
                                                        possible_subst_dicts=[{'A': self.A}, {'A': self.B}])
        self.assertEqual(result, [((2,), [{'A': self.B}])])

        # Test 3 - Two possibilities
        rule_sequent = classical_parser.parse('Gamma, A, Delta ==>')
        instance_sequent = classical_parser.parse('Gamma, A, B ==>')
        pattern, left_context, right_context, together = rule_sequent._get_rule_pattern(rule_sequent[0],
                                                                                        language.context_variables)
        result = instance_sequent._get_possible_indexes(instance_sequent[0], language,
                                                        pattern, left_context, right_context, together,
                                                        possible_subst_dicts=[{}])
        self.assertEqual(result, [((1,), [{'A': self.A}]), ((2,), [{'A': self.B}])])

        # Test 4 - A more complex case
        rule_sequent = classical_parser.parse('Gamma, A, B, Delta, A, Pi ==>')
        instance_sequent = classical_parser.parse('Gamma, A, B, C, Delta, A, B, C ==>')
        pattern, left_context, right_context, together = rule_sequent._get_rule_pattern(rule_sequent[0],
                                                                                        language.context_variables)
        result = instance_sequent._get_possible_indexes(instance_sequent[0], language,
                                                        pattern, left_context, right_context, together,
                                                        possible_subst_dicts=[{}])
        self.assertEqual(result, [((1, 2, 5), [{'A': self.A, 'B': self.B}]), ((2, 3, 6), [{'A': self.B, 'B': self.C}])])

        # Same as above with a substitution dict
        result = instance_sequent._get_possible_indexes(instance_sequent[0], language,
                                                        pattern, left_context, right_context, together,
                                                        possible_subst_dicts=[{'A': self.B}])
        self.assertEqual(result, [((2, 3, 6), [{'A': self.B, 'B': self.C}])])

    def test_get_context_distribs_iterator(self):
        # Does what the comment above says, e.g. if the rule's [Γ, Δ] corresponds to the instance's [Σ, A], returns an
        # iterator that will yield {Γ:[Σ, A], Δ:[]}, {Γ:[Σ], Δ:[A]} and {Γ:[], Δ:[Σ, A]}
        instance_sequent = classical_parser.parse('Gamma, A, B ==>')
        rule_context = ['Γ', 'Δ']

        instance_context = ['Γ']
        possible_dicts = list()
        for possible_dict in instance_sequent._get_context_distribs_iterator(rule_context, instance_context):
            possible_dicts.append(possible_dict)
        self.assertEqual(possible_dicts, [{'Γ': ['Γ'], 'Δ': []},
                                          {'Γ': [], 'Δ': ['Γ']}])

        instance_context = ['Σ', 'A']
        possible_dicts = list()
        for possible_dict in instance_sequent._get_context_distribs_iterator(rule_context, instance_context):
            possible_dicts.append(possible_dict)
        self.assertEqual(possible_dicts, [{'Γ': ['Σ', 'A'], 'Δ': []},
                                          {'Γ': ['Σ'], 'Δ': ['A']},
                                          {'Γ': [], 'Δ': ['Σ', 'A']}])

    def test_get_context_dicts(self):
        # Test 1 - Simple case
        rule_sequent = classical_parser.parse('Gamma, A, Delta ==>')
        instance_sequent = classical_parser.parse('Gamma, A, B ==>')
        pattern, left_context, right_context, together = rule_sequent._get_rule_pattern(rule_sequent[0],
                                                                                        language.context_variables)
        result = instance_sequent._get_possible_indexes(instance_sequent[0], language,
                                                        pattern, left_context, right_context, together,
                                                        possible_subst_dicts=[{}])
        possible_dicts = instance_sequent._get_context_dicts(instance_sequent[0], rule_sequent[0],
                                                             result, language.context_variables)
        self.assertEqual(possible_dicts, [{'A': self.A, 'Γ': ['Γ'], 'Δ': [self.B]},
                                          {'A': self.B, 'Γ': ['Γ', self.A], 'Δ': []}])

        # Test 1b - Same but with an impossible previous dict
        result = instance_sequent._get_possible_indexes(instance_sequent[0], language,
                                                        pattern, left_context, right_context, together,
                                                        possible_subst_dicts=[{'Γ': [self.C]}])
        possible_dicts = instance_sequent._get_context_dicts(instance_sequent[0], rule_sequent[0],
                                                             result, language.context_variables)
        self.assertEqual(possible_dicts, [])

        # Test 1c - Same but with a now possible previous dict (only one of the two possibilities above)
        result = instance_sequent._get_possible_indexes(instance_sequent[0], language,
                                                        pattern, left_context, right_context, together,
                                                        possible_subst_dicts=[{'Γ': [self.C]}, {'Γ': ['Γ']}])
        possible_dicts = instance_sequent._get_context_dicts(instance_sequent[0], rule_sequent[0],
                                                             result, language.context_variables)
        self.assertEqual(possible_dicts, [{'A': self.A, 'Γ': ['Γ'], 'Δ': [self.B]}])

        # Test 2 - More complex case
        rule_sequent = classical_parser.parse('Gamma, A, B, Delta, A, Pi ==>')
        instance_sequent = classical_parser.parse('Gamma, A, B, C, Delta, A, B, C ==>')
        pattern, left_context, right_context, together = rule_sequent._get_rule_pattern(rule_sequent[0],
                                                                                        language.context_variables)
        result = instance_sequent._get_possible_indexes(instance_sequent[0], language,
                                                        pattern, left_context, right_context, together,
                                                        possible_subst_dicts=[{}])
        pos_dicts = instance_sequent._get_context_dicts(instance_sequent[0], rule_sequent[0],
                                                        result, language.context_variables)
        self.assertEqual(pos_dicts, [{'A': self.A, 'B': self.B, 'Γ': ['Γ'], 'Δ': [self.C, 'Δ'], 'Π': [self.B, self.C]},
                                     {'A': self.B, 'B': self.C, 'Γ': ['Γ', self.A], 'Δ': ['Δ', self.A], 'Π': [self.C]}])

        # Test 3 - An even more complex case
        rule_sequent = classical_parser.parse('Gamma, Sigma, A, B, Delta, A, Pi ==>')
        instance_sequent = classical_parser.parse('Gamma, A, B, C, Delta, A, B, C ==>')
        pattern, left_context, right_context, together = rule_sequent._get_rule_pattern(rule_sequent[0],
                                                                                        language.context_variables)
        result = instance_sequent._get_possible_indexes(instance_sequent[0], language,
                                                        pattern, left_context, right_context, together,
                                                        possible_subst_dicts=[{}])
        pos_dicts = instance_sequent._get_context_dicts(instance_sequent[0], rule_sequent[0],
                                                        result, language.context_variables)
        self.assertEqual(pos_dicts,
                         [{'A': self.A, 'B': self.B, 'Γ': ['Γ'], 'Σ': [], 'Δ': [self.C, 'Δ'], 'Π': [self.B, self.C]},
                          {'A': self.A, 'B': self.B, 'Γ': [], 'Σ': ['Γ'], 'Δ': [self.C, 'Δ'], 'Π': [self.B, self.C]},
                          {'A': self.B, 'B': self.C, 'Γ': ['Γ', self.A], 'Σ': [], 'Δ': ['Δ', self.A], 'Π': [self.C]},
                          {'A': self.B, 'B': self.C, 'Γ': ['Γ'], 'Σ': [self.A], 'Δ': ['Δ', self.A], 'Π': [self.C]},
                          {'A': self.B, 'B': self.C, 'Γ': [], 'Σ': ['Γ', self.A], 'Δ': ['Δ', self.A], 'Π': [self.C]},
                          ])

    def test_is_instance_of(self):
        # --- Empty sequent
        sequent1 = classical_parser.parse('==>')
        sequent2 = classical_parser.parse('==>')
        instance = sequent2.is_instance_of(sequent1, language)
        self.assertTrue(instance)

        # --- One side
        sequent1 = classical_parser.parse('Gamma, ~A, Delta, ~B ==>')
        sequent2 = classical_parser.parse('Delta, ~B, Delta, ~C ==>')
        instance = sequent2.is_instance_of(sequent1, language)
        self.assertTrue(instance)
        # Test the dicts of the above case
        instance, possible_dicts = sequent2.is_instance_of(sequent1, language, return_subst_dicts=True)
        self.assertTrue(instance)
        self.assertEqual(possible_dicts, [{'A': self.B, 'B': self.C, 'Γ': ['Δ'], 'Δ': ['Δ']}])

        sequent2 = classical_parser.parse('Gamma, ~A1, Delta, B1 ==>')
        instance = sequent2.is_instance_of(sequent1, language)
        self.assertFalse(instance)

        sequent1 = classical_parser.parse('Gamma, ~A, Delta, ~A ==>')
        sequent2 = classical_parser.parse('Gamma, ~A1, Delta, ~B1 ==>')
        instance = sequent2.is_instance_of(sequent1, language)
        self.assertFalse(instance)

        # --- No right context
        sequent1 = classical_parser.parse('Gamma, ~A ==>')
        sequent2 = classical_parser.parse('Delta, ~A1 ==>')
        instance = sequent2.is_instance_of(sequent1, language)
        self.assertTrue(instance)

        sequent2 = classical_parser.parse('Delta, ~A1, ~A1 ==>')
        instance = sequent2.is_instance_of(sequent1, language)
        self.assertTrue(instance)

        sequent2 = classical_parser.parse('Delta, ~A1, A ==>')
        instance = sequent2.is_instance_of(sequent1, language)
        self.assertFalse(instance)

        # --- Only context
        sequent1 = classical_parser.parse('Gamma ==>')
        sequent2 = classical_parser.parse('Delta ==>')
        instance, possible_dicts = sequent2.is_instance_of(sequent1, language, return_subst_dicts=True)
        self.assertTrue(instance)
        self.assertEqual(possible_dicts, [{'Γ': ['Δ']}])

        sequent2 = classical_parser.parse('Delta, Pi ==>')
        instance, possible_dicts = sequent2.is_instance_of(sequent1, language, return_subst_dicts=True)
        self.assertTrue(instance)
        self.assertEqual(possible_dicts, [{'Γ': ['Δ', 'Π']}])

        sequent1 = classical_parser.parse('Gamma, Delta ==>')
        sequent2 = classical_parser.parse('Delta, Pi ==>')
        instance, possible_dicts = sequent2.is_instance_of(sequent1, language, return_subst_dicts=True)
        self.assertTrue(instance)
        self.assertEqual(possible_dicts,
                         [
                             {'Γ': ['Δ', 'Π'], 'Δ': []},
                             {'Γ': ['Δ'], 'Δ': ['Π']},
                             {'Γ': [], 'Δ': ['Δ', 'Π']}
                         ])

        # --- More than one side
        sequent1 = classical_parser.parse('Gamma, A, Delta ==> Gamma, A, Pi')
        sequent2 = classical_parser.parse('Gamma, ~A1, Delta, B1 ==> Gamma, ~A1, B')
        instance = sequent2.is_instance_of(sequent1, language)
        self.assertTrue(instance)

        sequent3 = classical_parser.parse('Gamma, ~A1, Delta, B1 ==> Delta, ~A1, B')
        instance = sequent3.is_instance_of(sequent1, language)
        self.assertFalse(instance)

        sequent1 = classical_parser.parse('Gamma, A, Delta | Gamma, A, Pi | Delta, ~A')
        sequent2 = classical_parser.parse('Delta, A, B | Delta, A, Gamma | B, ~A')
        instance = sequent2.is_instance_of(sequent1, language)
        self.assertTrue(instance)

        sequent1 = classical_parser.parse('Gamma, A, Delta | Gamma, A, Pi | Delta, ~A')
        sequent2 = classical_parser.parse('Delta, A | Delta, A, Gamma | ~A')
        instance = sequent2.is_instance_of(sequent1, language)
        self.assertTrue(instance)

        sequent1 = classical_parser.parse('Gamma, A, Delta | Gamma, A, Pi | Delta, ~A')
        sequent2 = classical_parser.parse('Delta, A | Delta, A, Gamma | ~B')
        instance = sequent2.is_instance_of(sequent1, language)
        self.assertFalse(instance)

    def test_is_correct_tree(self):
        # A weakening correct tree
        conclusion = SequentNode(content=classical_parser.parse('Gamma, A ==> A, Delta'), justification='WL')
        premise1 = SequentNode(content=classical_parser.parse('A ==> A, Delta'), justification='WR',
                               parent=conclusion)
        SequentNode(content=classical_parser.parse('A ==> A'), justification='identity', parent=premise1)
        self.assertTrue(LKminEA.is_correct_tree(conclusion))

        # A weakening inccorrect tree (rule names reversed)
        conclusion = SequentNode(content=classical_parser.parse('Gamma, A ==> A, Delta'), justification='WR')
        premise1 = SequentNode(content=classical_parser.parse('A ==> A, Delta'), justification='WL',
                               parent=conclusion)
        SequentNode(content=classical_parser.parse('A ==> A'), justification='identity', parent=premise1)
        self.assertFalse(LKminEA.is_correct_tree(conclusion))

    def test_transform_inference_into_sequent(self):
        inf = classical_parser.parse('p / q')
        seq = classical_parser.parse('p ==> q')
        self.assertEqual(LKminEA.transform_inference_into_sequent(inf), seq)

        inf = classical_parser.parse('p, q / r')
        seq = classical_parser.parse('p, q | p, q | r')
        self.assertEqual(LKminEA.transform_inference_into_sequent(inf, sides=3,
                                                                  separate_premises_from_conclusions_at_index=2), seq)

        inf = classical_parser.parse('p, q / r')
        seq = classical_parser.parse('p, q | p, q | r | r')
        self.assertEqual(LKminEA.transform_inference_into_sequent(inf, sides=4,
                                                                  separate_premises_from_conclusions_at_index=2), seq)


if __name__ == '__main__':
    unittest.main()
