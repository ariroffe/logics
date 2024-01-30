import unittest

from logics.classes.propositional.proof_theories.tableaux import TableauxNode, ConstructiveTreeSystem
from logics.classes.propositional import Formula, Inference
from logics.classes.errors import ErrorCode, CorrectionError
from logics.instances.propositional.languages import classical_infinite_language as lang
from logics.instances.propositional.tableaux import classical_tableaux_system, classical_indexed_tableaux_system


class TestTableauxSystem(unittest.TestCase):
    def setUp(self):
        self.n1 = TableauxNode(content=Formula(['~', ['~', ['~', ['~', ['p']]]]]), index=0)
        self.n2 = TableauxNode(content=Formula(['~', ['p']]), index=0, parent=self.n1)
        self.n3 = TableauxNode(content=Formula(['~', ['~', ['p']]]), index=0, justification='R~~', parent=self.n2)
        self.n4 = TableauxNode(content=Formula(['p']), index=0, justification='R~~', parent=self.n3)
        '''
        ~~~~p, 0
        └── ~p, 0
            └── ~~p, 0 (R~~)
                └── p, 0 (R~~)
        '''

        self.n5 = TableauxNode(content=Formula(['∨', ['p'], ['q']]))
        self.n6 = TableauxNode(content=Formula(['~', ['p']]), parent=self.n5)
        self.n7 = TableauxNode(content=Formula(['p']), justification='R∨', parent=self.n6)
        self.n8 = TableauxNode(content=Formula(['q']), justification='R∨', parent=self.n6)
        '''
        (p ∨ q)
        └── ~p
            ├── p (R∨)
            └── q (R∨)
        '''

        self.n9 = TableauxNode(content=Formula(['∧', ['p'], ['q']]))
        self.n10 = TableauxNode(content=Formula(['p']), justification='R∧', parent=self.n9)
        self.n11 = TableauxNode(content=Formula(['q']), justification='R∧', parent=self.n10)
        '''
        (p ∧ q)
        └── p (R∧)
            └── q (R∧)
        '''

    def test_builtin_methods(self):
        self.assertTrue(self.n1.is_root)
        self.assertFalse(self.n2.is_root)
        self.assertTrue(self.n4.is_leaf)
        self.assertFalse(self.n1.is_leaf)
        self.assertEqual(self.n1.children, (self.n2,))
        self.assertEqual(self.n6.children, (self.n7, self.n8))
        self.assertEqual(self.n1.descendants, (self.n2, self.n3, self.n4))
        self.assertEqual(self.n3.root, self.n1)
        self.assertEqual(self.n1.leaves, (self.n4,))
        self.assertEqual(self.n3.path, (self.n1, self.n2, self.n3))
        self.assertEqual(self.n3.depth, 2)
        self.assertEqual(self.n3.height, 1)
        self.assertEqual(self.n1.depth, 0)
        self.assertEqual(self.n1.height, 3)

    def test_child_idx(self):
        self.assertEqual(self.n1.child_index, 0)
        self.assertEqual(self.n2.child_index, 0)
        self.assertEqual(self.n7.child_index, 0)
        self.assertEqual(self.n8.child_index, 1)

    def test_is_closed(self):
        self.assertTrue(classical_tableaux_system.node_is_closed(self.n4))
        self.assertTrue(classical_tableaux_system.node_is_closed(self.n3))
        self.assertFalse(classical_tableaux_system.node_is_closed(self.n2))
        self.assertFalse(classical_tableaux_system.node_is_closed(self.n1))
        self.assertTrue(classical_tableaux_system.tree_is_closed(self.n1))
        self.assertFalse(classical_tableaux_system.tree_is_closed(self.n4))

        self.assertTrue(classical_tableaux_system.node_is_closed(self.n7))
        self.assertFalse(classical_tableaux_system.tree_is_closed(self.n7))
        # Test that the node reattached itself after calling tree_is_closed
        self.assertEqual(self.n7.parent, self.n6)
        self.assertFalse(classical_tableaux_system.node_is_closed(self.n6))
        self.assertFalse(classical_tableaux_system.node_is_closed(self.n8))
        self.assertFalse(classical_tableaux_system.tree_is_closed(self.n5))

        alone = TableauxNode(content=Formula(['p']))
        self.assertFalse(classical_tableaux_system.node_is_closed(alone))
        self.assertFalse(classical_tableaux_system.tree_is_closed(alone))

    def test_get_counterexample(self):
        self.assertIs(classical_tableaux_system.get_counterexample(self.n1), None)
        self.assertEqual(classical_tableaux_system.get_counterexample(self.n5), {'p': '0', 'q': '1'})
        self.assertEqual(classical_tableaux_system.get_counterexample(self.n9), {'p': '1', 'q': '1'})

        n1 = TableauxNode(content=Formula(['∨', ['p'], ['~', ['p']]]))
        n2 = TableauxNode(content=Formula(['p']), parent=n1)
        n3 = TableauxNode(content=Formula(['~', ['q']]), parent=n2)
        n4 = TableauxNode(content=Formula(['~', ['~', ['p']]]), justification='R∨', parent=n3)
        n5 = TableauxNode(content=Formula(['p']), justification='R∨', parent=n4)
        n6 = TableauxNode(content=Formula(['p']), justification='R~~', parent=n5)
        n7 = TableauxNode(content=Formula(['~', ['p']]), justification='R∨', parent=n3)
        '''
        p ∨ ~p
        └── p
            └── ~q
                ├── ~~p (R∨)
                │   └── p (R∨)
                │       └── p (R~~)
                └── ~p (R∨)
        '''
        self.assertEqual(classical_tableaux_system.get_counterexample(n1), {'p': '1', 'q': '0'})

    def test_is_instance_of(self):
        an1 = TableauxNode(content=Formula(['A']))
        an2 = TableauxNode(content=Formula(['~', ['A']]))
        an3 = TableauxNode(content=Formula(['~', ['~', ['A']]]))
        an4 = TableauxNode(content=Formula(['A']), justification='R~~', parent=an3)

        # Node is instance of
        for n in [self.n1, self.n2, self.n3, self.n4, self.n5, self.n6, self.n7, self.n8]:
            self.assertTrue(n.is_instance_of(an1, lang))

            if n in [self.n1, self.n2, self.n3, self.n6]:
                self.assertTrue(n.is_instance_of(an2, lang))
            else:
                self.assertFalse(n.is_instance_of(an2, lang))

            if n in [self.n1, self.n3]:
                self.assertTrue(n.is_instance_of(an3, lang))
            else:
                self.assertFalse(n.is_instance_of(an3, lang))

            if n in [self.n3, self.n4]:
                self.assertTrue(n.is_instance_of(an4, lang))
            else:
                self.assertFalse(n.is_instance_of(an4, lang))

    def test_instantiate(self):
        schema1 = TableauxNode(content=Formula(['∨', ['A'], ['B']]))
        schema_child = TableauxNode(content=Formula(['B']), parent=schema1)
        instance1 = TableauxNode(content=Formula(['∨', ['B'], ['C']]))
        instance_child = TableauxNode(content=Formula(['C']), parent=instance1)

        result1 = schema1.instantiate(lang, {'A': Formula(['B']), 'B': Formula(['C'])}, instantiate_children=True)
        # Must compare content because TableauxNode does not implement an __eq__ method (bc of hashing problems later)
        self.assertEqual(result1.content, instance1.content)
        self.assertEqual(result1.children[0].content, instance_child.content)

        result2 = schema1.instantiate(lang, {'A': Formula(['B']), 'B': Formula(['C'])}, instantiate_children=False)
        # Must compare content because TableauxNode does not implement an __eq__ method (bc of hashing problems later)
        self.assertEqual(result2.content, instance1.content)
        self.assertEqual(result2.children[0].content, schema_child.content)

    def test_is_correct_tree(self):
        # Tests with classical logic
        self.assertTrue(classical_tableaux_system.is_correct_tree(self.n1))
        self.assertTrue(classical_tableaux_system.is_correct_tree(self.n5))
        self.assertTrue(classical_tableaux_system.is_correct_tree(self.n9))

        n1 = TableauxNode(content=Formula(['~', ['~', ['~', ['~', ['p']]]]]), index=0)
        n2 = TableauxNode(content=Formula(['~', ['p']]), index=0, parent=n1)
        n3 = TableauxNode(content=Formula(['~', ['~', ['~', ['p']]]]), index=0, justification='R~~', parent=n2)
        n4 = TableauxNode(content=Formula(['p']), index=0, justification='R~~', parent=n3)
        '''
        ~~~~p, 0
        └── ~p, 0
            └── ~~~p, 0 (R~~)
                └── p, 0 (R~~)
        '''
        self.assertFalse(classical_tableaux_system.is_correct_tree(n1))

        # Incomplete tableaux (missing the negation of the conclusion)
        n1 = TableauxNode(content=Formula(['p']))
        inf = Inference(premises=[Formula(['p'])], conclusions=[Formula(['∨', ['p'], ['q']])])
        self.assertFalse(classical_tableaux_system.is_correct_tree(n1, inference=inf))
        correct, error_list = classical_tableaux_system.is_correct_tree(n1, inference=inf, return_error_list=True)
        self.assertEqual(error_list, [CorrectionError(code=ErrorCode.TBL_CONCLUSION_NOT_PRESENT, index=(),
                                                      description="Conclusion ['∨', ['p'], ['q']] is not present in "
                                                                  "the tree")])

        # Incorrect tableaux (premise node comes after applying a rule)
        n1 = TableauxNode(content=Formula(['~', ['~', ['p']]]))
        n2 = TableauxNode(content=Formula(['p']), justification='R~~', parent=n1)
        n3 = TableauxNode(content=Formula(['q']), parent=n2)
        self.assertFalse(classical_tableaux_system.is_correct_tree(n1))
        correct, error_list = classical_tableaux_system.is_correct_tree(n1, return_error_list=True)
        self.assertEqual(error_list, [CorrectionError(ErrorCode.TBL_PREMISE_NOT_BEGINNING, index=(0, 0, 0),
                                                      description='Premise nodes must be at the beggining of the '
                                                                  'tableaux, before applying any rule and before '
                                                                  'opening any new branch')])

        # Incomplete tableaux (~~p premise node is present only in one branch)
        n1 = TableauxNode(content=Formula(['∨', ['p'], ['~', ['p']]]))
        n2 = TableauxNode(content=Formula(['p']), parent=n1)
        n3 = TableauxNode(content=Formula(['~', ['q']]), parent=n2)
        n4 = TableauxNode(content=Formula(['~', ['~', ['p']]]), parent=n3)
        n5 = TableauxNode(content=Formula(['p']), justification='R∨', parent=n4)
        n6 = TableauxNode(content=Formula(['p']), justification='R~~', parent=n5)
        n7 = TableauxNode(content=Formula(['~', ['p']]), justification='R∨', parent=n3)
        '''
        p ∨ ~p
        └── p
            └── ~q
                ├── ~~p
                │   └── p (R∨)
                │       └── p (R~~)
                └── ~p (R∨)
        '''
        # p ∨ ~p, p, ~~p / q
        inf = Inference(premises=[Formula(['∨', ['p'], ['~', ['p']]]), Formula(['p']), Formula(['~', ['~', ['p']]])],
                        conclusions=[Formula(['q'])])
        self.assertFalse(classical_tableaux_system.is_correct_tree(n1, inference=inf))

        # A premise node that has a sibling (no need for an inference)
        n1 = TableauxNode(content=Formula(['p']))
        n2 = TableauxNode(content=Formula(['~', ['q']]), parent=n1)
        n3 = TableauxNode(content=Formula(['p']), parent=n2)
        n4 = TableauxNode(content=Formula(['p']), parent=n2)
        '''
        p
        └── ~q
            ├── p
            └── p
        '''
        self.assertFalse(classical_tableaux_system.is_correct_tree(n1))
        correct, error_list = classical_tableaux_system.is_correct_tree(n1, return_error_list=True)
        self.assertEqual(error_list, [CorrectionError(code=ErrorCode.TBL_PREMISE_NOT_BEGINNING, index=(0, 0, 0),
                                                      description='Premise nodes must be at the beggining of the '
                                                                  'tableaux, before applying any rule and before '
                                                                  'opening any new branch'),
                                      CorrectionError(code=ErrorCode.TBL_PREMISE_NOT_BEGINNING, index=(0, 0, 1),
                                                      description='Premise nodes must be at the beggining of the '
                                                                  'tableaux, before applying any rule and before '
                                                                  'opening any new branch')])

        # Non-applied rule
        n1 = TableauxNode(content=Formula(['p']))
        n2 = TableauxNode(content=Formula(['~', ['~', ['~', ['p']]]]), parent=n1)
        n3 = TableauxNode(content=Formula(['~', ['q']]), parent=n2)
        """
        p
        └── ~~~p
            └── ~q
        """
        inf = Inference(premises=[Formula(['p']), Formula(['~', ['~', ['~', ['p']]]])],
                        conclusions=[Formula(['q'])])
        self.assertFalse(classical_tableaux_system.is_correct_tree(n1))
        correct, error_list = classical_tableaux_system.is_correct_tree(n1, return_error_list=True)
        self.assertEqual(error_list, [CorrectionError(code=ErrorCode.TBL_RULE_NOT_APPLIED, index=(0, 0),
                                                      description="Rule R~~ was not applied to node "
                                                                  "['~', ['~', ['~', ['p']]]]")])

        # Incorrectly applied rule
        n1 = TableauxNode(content=Formula(['↔', ['p'], ['q']]))
        n2 = TableauxNode(content=Formula(['p']), parent=n1, justification='R↔')
        n3 = TableauxNode(content=Formula(['q']), parent=n2, justification='R↔')
        n4 = TableauxNode(content=Formula(['~', ['p']]), parent=n1, justification='R↔')
        n5 = TableauxNode(content=Formula(['q']), parent=n4, justification='R↔')  # This node is wrong
        """
        p ↔ q
        ├── p
        │   └── q
        └── ~p
            └── q
        """
        self.assertFalse(classical_tableaux_system.is_correct_tree(n1))
        correct, error_list = classical_tableaux_system.is_correct_tree(n1, return_error_list=True)
        self.assertEqual(error_list, [CorrectionError(code=ErrorCode.TBL_RULE_NOT_APPLIED, index=(0,),
                                                      description="Rule R↔ was not applied to node ['↔', ['p'], ['q']]"),
                                      CorrectionError(code=ErrorCode.TBL_RULE_INCORRECTLY_APPLIED, index=(0, 0),
                                                      description="Rule incorrectly applied to node ['p'] (R↔)"),
                                      CorrectionError(code=ErrorCode.TBL_RULE_INCORRECTLY_APPLIED, index=(0, 1),
                                                      description="Rule incorrectly applied to node ['~', ['p']] (R↔)"),
                                      CorrectionError(code=ErrorCode.TBL_RULE_INCORRECTLY_APPLIED, index=(0, 0, 0),
                                                      description="Rule incorrectly applied to node ['q'] (R↔)"),
                                      CorrectionError(code=ErrorCode.TBL_RULE_INCORRECTLY_APPLIED, index=(0, 1, 0),
                                                      description="Rule incorrectly applied to node ['q'] (R↔)")])

        # exit_on_first_error - should return only the first of those
        correct, error_list = classical_tableaux_system.is_correct_tree(n1, return_error_list=True,
                                                                        exit_on_first_error=True)
        self.assertEqual(error_list, [CorrectionError(code=ErrorCode.TBL_RULE_NOT_APPLIED, index=(0,),
                                                      description="Rule R↔ was not applied to node ['↔', ['p'], ['q']]")])

        # More extensive tests (with the random argument generator) are made in tests/utils/test_tableaux_solver

    def test_classical_indexed_tableaux(self):
        # Node is closed
        n1 = TableauxNode(content=Formula(['p']), index=1)
        n2 = TableauxNode(content=Formula(['~', ['p']]), index=1, parent=n1)
        n3 = TableauxNode(content=Formula(['p']), index=0, parent=n2)
        '''
        p, 1
        └── ~p, 1
            └── p, 0
        '''
        self.assertFalse(classical_indexed_tableaux_system.node_is_closed(n1))
        self.assertFalse(classical_indexed_tableaux_system.node_is_closed(n2))
        self.assertTrue(classical_indexed_tableaux_system.node_is_closed(n3))

        n1 = TableauxNode(content=Formula(['~', ['~', ['~', ['p']]]]), index=1)
        n2 = TableauxNode(content=Formula(['~', ['~', ['p']]]), index=0, justification='R~1', parent=n1)
        n3 = TableauxNode(content=Formula(['~', ['p']]), index=1, justification='R~0', parent=n2)
        n4 = TableauxNode(content=Formula(['p']), index=0, justification='R~1', parent=n3)
        '''
        ~~~~p, 1
        └── ~~p, 0 (R~1)
            └── ~p, 1 (R~0)
                └── p, 0 (R~1)
        '''
        correct, error_list = classical_indexed_tableaux_system.is_correct_tree(n1, return_error_list=True)
        self.assertTrue(correct)

    def test_indexed_tableaux_counterexamples(self):
        n1 = TableauxNode(content=Formula(['p']), index=1)
        n2 = TableauxNode(content=Formula(['~', ['p']]), index=1, parent=n1)
        n3 = TableauxNode(content=Formula(['p']), index=0, parent=n2)
        '''
        p, 1
        └── ~p, 1
            └── p, 0
        '''
        self.assertIs(classical_indexed_tableaux_system.get_counterexample(n1), None)

        n1 = TableauxNode(content=Formula(['~', ['~', ['~', ['p']]]]), index=1)
        n2 = TableauxNode(content=Formula(['~', ['~', ['p']]]), index=0, justification='R~1', parent=n1)
        n3 = TableauxNode(content=Formula(['~', ['p']]), index=1, justification='R~0', parent=n2)
        n4 = TableauxNode(content=Formula(['p']), index=0, justification='R~1', parent=n3)
        '''
        ~~~~p, 1
        └── ~~p, 0 (R~1)
            └── ~p, 1 (R~0)
                └── p, 0 (R~1)
        '''
        self.assertEqual(classical_indexed_tableaux_system.get_counterexample(n1), {'p': '0'})

        # More extensive tests (with the random argument generator) are made in tests/utils/test_tableaux_solver


class TestConstructiveTrees(unittest.TestCase):
    def test_constructive_tree_system_rules(self):
        cl_system = ConstructiveTreeSystem(lang)  # lang is classical_infinite_language
        # Negation
        self.assertEqual(cl_system.rules['R~'].content, Formula(['~', ['A1']]))
        self.assertEqual(len(cl_system.rules['R~'].children), 1)
        self.assertEqual(cl_system.rules['R~'].children[0].content, Formula(['A1']))

        # Conjunction
        self.assertEqual(cl_system.rules['R∧'].content, Formula(['∧', ['A1'], ['A2']]))
        self.assertEqual(len(cl_system.rules['R∧'].children), 2)
        self.assertEqual(cl_system.rules['R∧'].children[0].content, Formula(['A1']))
        self.assertEqual(cl_system.rules['R∧'].children[1].content, Formula(['A2']))

        # Further tests are in tests.utils.test_tableaux_solver


if __name__ == '__main__':
    unittest.main()
