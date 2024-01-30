import unittest

from logics.classes.propositional.proof_theories.metainferential_tableaux import (
    MetainferentialTableauxStandard, MetainferentialTableauxNode
)
from logics.classes.propositional import Formula, Inference
from logics.instances.propositional.languages import classical_infinite_language as lang
from logics.instances.propositional.metainferential_tableaux import SK_metainferential_tableaux_system as sk_tableaux
from logics.utils.parsers import classical_parser


class TestMetainferentialTableauxSystem(unittest.TestCase):
    def test_standard_init(self):
        standard = MetainferentialTableauxStandard([[{'1', 'i'}, {'1'}], [{'1', 'i'}, {'1'}]], bar=False)
        self.assertTrue(isinstance(standard, MetainferentialTableauxStandard))  # TS/TS
        self.assertTrue(isinstance(standard.content[0], MetainferentialTableauxStandard))  # TS
        self.assertTrue(isinstance(standard.content[1], MetainferentialTableauxStandard))  # TS
        self.assertTrue(isinstance(standard.content[0].content[0], MetainferentialTableauxStandard))  # T
        self.assertTrue(isinstance(standard.content[0].content[1], MetainferentialTableauxStandard))  # S

        standard = MetainferentialTableauxStandard(['X', 'Y'], bar=True)
        self.assertTrue(isinstance(standard, MetainferentialTableauxStandard))  # -X/Y
        self.assertTrue(isinstance(standard.content[0], MetainferentialTableauxStandard))  # X
        self.assertTrue(isinstance(standard.content[1], MetainferentialTableauxStandard))  # Y

    def test_standard_level(self):
        standard = MetainferentialTableauxStandard([[{'1', 'i'}, {'1'}], [{'1', 'i'}, {'1'}]], bar=False)
        self.assertEqual(standard.level, 2)  # TS/TS
        self.assertEqual(standard.content[0].level, 1)  # TS
        self.assertEqual(standard.content[0].content[0].level, 0)  # T

        standard = MetainferentialTableauxStandard([[{'1', 'i'}, {'1'}], [{'1'}, {'1', 'i'}]])
        self.assertEqual(standard.level, 2)  # TS/ST
        self.assertEqual(standard.content[1].level, 1)  # ST
        self.assertEqual(standard.content[1].content[0].level, 0)  # S

    def test_standard_is_instance_of(self):
        simple_standard = MetainferentialTableauxStandard({'1', 'i'}, bar=False)  # T
        # Index variable
        self.assertTrue(simple_standard.is_instance_of(MetainferentialTableauxStandard('X')))
        # Sets
        self.assertTrue(simple_standard.is_instance_of(MetainferentialTableauxStandard({'1', 'i'})))
        self.assertFalse(simple_standard.is_instance_of(MetainferentialTableauxStandard({'1'})))
        self.assertFalse(simple_standard.is_instance_of(MetainferentialTableauxStandard(['X', 'Y'])))

        complex_standard = MetainferentialTableauxStandard([{'1', 'i'}, {'1'}], bar=False)  # TS
        # Index variables
        self.assertTrue(complex_standard.is_instance_of(MetainferentialTableauxStandard('X')))
        self.assertTrue(complex_standard.is_instance_of(MetainferentialTableauxStandard(['X', 'Y'])))
        self.assertFalse(complex_standard.is_instance_of(MetainferentialTableauxStandard(['X', 'X'])))
        # List
        self.assertTrue(complex_standard.is_instance_of(MetainferentialTableauxStandard([{'1', 'i'}, {'1'}])))
        self.assertFalse(complex_standard.is_instance_of(MetainferentialTableauxStandard([{'1'}, {'1'}])))  # SS
        self.assertFalse(complex_standard.is_instance_of(MetainferentialTableauxStandard([{'1'}, {'1', 'i'}])))  # ST

        complex_standard2 = MetainferentialTableauxStandard([[{'1', 'i'}, {'1'}], [{'1', 'i'}, {'1'}]], bar=False)  # TS/TS
        # Index variables
        self.assertTrue(complex_standard2.is_instance_of(MetainferentialTableauxStandard('X')))
        self.assertTrue(complex_standard2.is_instance_of(MetainferentialTableauxStandard(['X', 'Y'])))
        self.assertTrue(complex_standard2.is_instance_of(MetainferentialTableauxStandard(['X', 'X'])))
        # List
        self.assertTrue(complex_standard2.is_instance_of(MetainferentialTableauxStandard([[{'1', 'i'}, {'1'}],
                                                                                          [{'1', 'i'}, {'1'}]])))
        self.assertFalse(complex_standard2.is_instance_of(MetainferentialTableauxStandard([[{'1', 'i'}, {'1'}],
                                                                                           [{'1'}, {'1'}]])))
        self.assertFalse(complex_standard2.is_instance_of(MetainferentialTableauxStandard([{'1', 'i'}, {'1'}])))

        _, subst_dict = complex_standard2.is_instance_of(MetainferentialTableauxStandard(['X', 'Y']), return_subst_dict=True)
        self.assertEqual(type(subst_dict['X']), MetainferentialTableauxStandard)

        # We do not treat -X as an instance of X, and viceverse
        X = MetainferentialTableauxStandard('X', bar=False)
        Xbar = MetainferentialTableauxStandard('X', bar=True)
        self.assertFalse(Xbar.is_instance_of(X))
        self.assertFalse(X.is_instance_of(Xbar))

    def test_node_is_instance_of(self):
        TS = MetainferentialTableauxStandard([{'1', 'i'}, {'1'}], bar=False)
        ST = MetainferentialTableauxStandard([{'1'}, {'1', 'i'}], bar=False)
        XY = MetainferentialTableauxStandard(['X', 'Y'], bar=False)
        XYbar = MetainferentialTableauxStandard(['X', 'Y'], bar=True)
        # Formula nodes
        node1 = MetainferentialTableauxNode(Formula(['~', ['p']]), index=TS)
        node2 = MetainferentialTableauxNode(Formula(['~', ['p']]), index=ST)
        node3 = MetainferentialTableauxNode(Formula(['p']), index=TS)
        self.assertTrue(node1.is_instance_of(node1, lang))
        self.assertFalse(node1.is_instance_of(node2, lang))
        self.assertFalse(node1.is_instance_of(node3, lang))
        # standard and formula variables
        node4 = MetainferentialTableauxNode(Formula(['~', ['p']]), index=XY)
        node5 = MetainferentialTableauxNode(Formula(['A']), index=XY)
        node5bar = MetainferentialTableauxNode(Formula(['A']), index=XYbar)
        node6 = MetainferentialTableauxNode(Formula(['~', ['~', ['A']]]), index=XY)
        self.assertTrue(node1.is_instance_of(node4, lang))
        self.assertTrue(node1.is_instance_of(node5, lang))
        self.assertFalse(node1.is_instance_of(node5bar, lang))
        self.assertFalse(node1.is_instance_of(node6, lang))

        T = MetainferentialTableauxStandard({'1', 'i'})
        S = MetainferentialTableauxStandard({'1'})
        _, subst_dict = node1.is_instance_of(node5, lang, return_subst_dict=True)
        self.assertEqual(subst_dict, {'A': Formula(['~', ['p']]), 'X': T, 'Y': S})

        # Inference nodes
        node7 = MetainferentialTableauxNode(Inference(premises=[Formula(['p'])], conclusions=[Formula(['p'])]),
                                            index=TS)
        node8 = MetainferentialTableauxNode(Inference(premises=[Formula(['p'])], conclusions=[Formula(['p'])]),
                                            index=ST)
        node9 = MetainferentialTableauxNode(Inference(premises=[Formula(['~', ['p']])], conclusions=[Formula(['p'])]),
                                            index=TS)
        self.assertTrue(node7.is_instance_of(node7, lang))
        self.assertFalse(node7.is_instance_of(node8, lang))
        self.assertFalse(node7.is_instance_of(node9, lang))
        # standard and formula variables
        node10 = MetainferentialTableauxNode(Inference(premises=[Formula(['p'])], conclusions=[Formula(['p'])]),
                                             index=XY)
        node11 = MetainferentialTableauxNode(Inference(premises=[Formula(['A'])], conclusions=[Formula(['A'])]),
                                             index=XY)
        node11bar = MetainferentialTableauxNode(Inference(premises=[Formula(['A'])], conclusions=[Formula(['A'])]),
                                                index=XYbar)
        node12 = MetainferentialTableauxNode(Inference(premises=[Formula(['~', ['A']])], conclusions=[Formula(['A'])]),
                                             index=XY)
        self.assertTrue(node7.is_instance_of(node10, lang))
        self.assertTrue(node7.is_instance_of(node11, lang))
        self.assertFalse(node7.is_instance_of(node11bar, lang))
        self.assertFalse(node7.is_instance_of(node12, lang))

        # Mixing formulae and inferences returns False
        self.assertFalse(node5.is_instance_of(node11, lang))
        self.assertFalse(node11.is_instance_of(node5, lang))

    def test_node_is_closed(self):
        O = MetainferentialTableauxStandard(set())
        T = MetainferentialTableauxStandard({'1', 'i'})
        ST = MetainferentialTableauxStandard([{'1'}, {'1', 'i'}], bar=False)

        formula = Formula(['p'])
        inference = Inference(premises=[Formula(['p'])], conclusions=[Formula(['p'])])

        node1 = MetainferentialTableauxNode(inference, index=ST)
        node2 = MetainferentialTableauxNode(formula, index=T, parent=node1)
        node3 = MetainferentialTableauxNode(formula, index=T, parent=node2)
        node4 = MetainferentialTableauxNode(formula, index=O, parent=node2)
        node5 = MetainferentialTableauxNode(formula, index=T, parent=node4)

        # from logics.utils.parsers import classical_parser
        # node1.print_tree(classical_parser)
        """
        p / p, [{'1'}, {'1', 'i'}]
        └── p, {'1', 'i'}
            ├── p, {'1', 'i'}
            └── p, set()
                └── p, {'1', 'i'}
        """
        self.assertFalse(sk_tableaux.node_is_closed(node1))
        self.assertFalse(sk_tableaux.node_is_closed(node2))
        self.assertFalse(sk_tableaux.node_is_closed(node3))
        self.assertTrue(sk_tableaux.node_is_closed(node4))
        self.assertTrue(sk_tableaux.node_is_closed(node5))

        self.assertFalse(sk_tableaux.tree_is_closed(node1))
        self.assertFalse(sk_tableaux.tree_is_closed(node2))
        self.assertFalse(sk_tableaux.tree_is_closed(node3))
        self.assertTrue(sk_tableaux.tree_is_closed(node4))
        self.assertFalse(sk_tableaux.tree_is_closed(node5))

        # Test the other rule, that a branch closes if the empty inference with no bar appears
        node1 = MetainferentialTableauxNode(inference, index=ST)
        node2 = MetainferentialTableauxNode(Inference(premises=[], conclusions=[]), index=T, parent=node1)
        node3 = MetainferentialTableauxNode(formula, index=T, parent=node2)

        self.assertFalse(sk_tableaux.node_is_closed(node1))
        self.assertTrue(sk_tableaux.node_is_closed(node2))
        self.assertTrue(sk_tableaux.node_is_closed(node3))

    def test_rule_is_applicable(self):
        O = MetainferentialTableauxStandard(set())
        T = MetainferentialTableauxStandard({'1', 'i'})
        S = MetainferentialTableauxStandard({'1'})
        F = MetainferentialTableauxStandard({'0'})
        Sbar = MetainferentialTableauxStandard({'1'}, bar=True)
        ST = MetainferentialTableauxStandard([{'1'}, {'1', 'i'}], bar=False)
        STbar = MetainferentialTableauxStandard([{'1'}, {'1', 'i'}], bar=True)

        formula = Formula(['p'])
        inference = Inference(premises=[Formula(['p'])], conclusions=[Formula(['p'])])

        # -------------------------------
        # Formula nodes
        node1 = MetainferentialTableauxNode(formula, index=S)
        node2 = MetainferentialTableauxNode(formula, index=T)
        node3 = MetainferentialTableauxNode(formula, index=Sbar)
        node4 = MetainferentialTableauxNode(formula, index=ST)
        node5 = MetainferentialTableauxNode(formula, index=STbar)

        self.assertFalse(sk_tableaux.rule_is_applicable(node1, 'inf0'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node2, 'inf1'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node3, 'inf0'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node4, 'inf1'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node5, 'inf0'))

        self.assertFalse(sk_tableaux.rule_is_applicable(node1, 'singleton'))
        self.assertTrue(sk_tableaux.rule_is_applicable(node2, 'singleton'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node3, 'singleton'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node4, 'singleton'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node5, 'singleton'))

        self.assertFalse(sk_tableaux.rule_is_applicable(node1, 'complement'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node2, 'complement'))
        self.assertTrue(sk_tableaux.rule_is_applicable(node3, 'complement'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node4, 'complement'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node5, 'complement'))

        # Intersection rule is False for all because it needs two nodes as premises
        self.assertFalse(sk_tableaux.rule_is_applicable(node1, 'intersection'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node2, 'intersection'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node3, 'intersection'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node4, 'intersection'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node5, 'intersection'))

        # -------------------------------
        # Inference nodes
        node1 = MetainferentialTableauxNode(inference, index=S)
        node2 = MetainferentialTableauxNode(inference, index=T)
        node3 = MetainferentialTableauxNode(inference, index=Sbar)
        node4 = MetainferentialTableauxNode(inference, index=ST)
        node5 = MetainferentialTableauxNode(inference, index=STbar)

        self.assertFalse(sk_tableaux.rule_is_applicable(node1, 'inf0'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node2, 'inf1'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node3, 'inf0'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node4, 'inf0'))
        self.assertTrue(sk_tableaux.rule_is_applicable(node4, 'inf1'))
        self.assertTrue(sk_tableaux.rule_is_applicable(node5, 'inf0'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node5, 'inf1'))

        self.assertFalse(sk_tableaux.rule_is_applicable(node1, 'singleton'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node2, 'singleton'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node3, 'singleton'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node4, 'singleton'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node5, 'singleton'))

        self.assertFalse(sk_tableaux.rule_is_applicable(node1, 'complement'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node2, 'complement'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node3, 'complement'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node4, 'complement'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node5, 'complement'))

        self.assertFalse(sk_tableaux.rule_is_applicable(node1, 'intersection'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node2, 'intersection'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node3, 'intersection'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node4, 'intersection'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node5, 'intersection'))

        # Intersection rule (has more than one premise so is a bit more difficult to test)
        node1 = MetainferentialTableauxNode(formula, index=S)
        node2 = MetainferentialTableauxNode(formula, index=F, parent=node1)
        self.assertTrue(sk_tableaux.rule_is_applicable(node2, 'intersection'))

        # When one is a subset of the other, do not apply the rule
        node1 = MetainferentialTableauxNode(formula, index=S)
        node2 = MetainferentialTableauxNode(formula, index=T, parent=node1)
        self.assertFalse(sk_tableaux.rule_is_applicable(node2, 'intersection'))

        # When one of the nodes is the empty node, do not apply the intersection rule
        # (otherwise it leads to infinite recursion in the solver)
        node1 = MetainferentialTableauxNode(formula, index=O)
        node2 = MetainferentialTableauxNode(formula, index=F, parent=node1)
        self.assertFalse(sk_tableaux.rule_is_applicable(node2, 'intersection'))
        node1 = MetainferentialTableauxNode(formula, index=F)
        node2 = MetainferentialTableauxNode(formula, index=O, parent=node1)
        self.assertFalse(sk_tableaux.rule_is_applicable(node2, 'intersection'))

        formula2 = Formula(['q'])
        node1 = MetainferentialTableauxNode(formula, index=S)
        node2 = MetainferentialTableauxNode(formula2, index=T, parent=node1)
        self.assertFalse(sk_tableaux.rule_is_applicable(node2, 'intersection'))  # Different formulas, should not apply

        node1 = MetainferentialTableauxNode(formula, index=ST)
        node2 = MetainferentialTableauxNode(formula, index=T, parent=node1)
        self.assertFalse(sk_tableaux.rule_is_applicable(node2, 'intersection'))  # Different standard levels

        # Try with one node in the middle
        node1 = MetainferentialTableauxNode(formula, index=S)
        node2 = MetainferentialTableauxNode(formula2, index=S, parent=node1)
        node3 = MetainferentialTableauxNode(formula, index=F, parent=node2)
        self.assertTrue(sk_tableaux.rule_is_applicable(node3, 'intersection'))

        # One in the middle with one of the provisos in the daughter class
        """
        r, {'1'} (inf0)
        └──  r, {'0'} (R∧i)
             └── r, {'0'} (singleton)
        """
        root = MetainferentialTableauxNode(content=classical_parser.parse('r'), index=S)
        node1 = MetainferentialTableauxNode(content=classical_parser.parse('r'), index=F, parent=root)
        node2 = MetainferentialTableauxNode(content=classical_parser.parse('r'), index=F, parent=node1)
        self.assertTrue(sk_tableaux.rule_is_applicable(node2, 'intersection'))

        # -------------------------------
        # Metainference nodes
        TSST = MetainferentialTableauxStandard([[{'1', 'i'}, {'1'}],[{'1'}, {'1', 'i'}]], bar=False)
        TSSTbar = MetainferentialTableauxStandard([[{'1', 'i'}, {'1'}],[{'1'}, {'1', 'i'}]], bar=True)
        metainference = Inference(premises=[Inference(premises=[Formula(['p'])], conclusions=[Formula(['q'])])],
                                  conclusions=[Inference(premises=[Formula(['p'])], conclusions=[Formula(['p'])])])

        node1 = MetainferentialTableauxNode(metainference, index=TSST)
        node2 = MetainferentialTableauxNode(metainference, index=TSSTbar)
        self.assertFalse(sk_tableaux.rule_is_applicable(node1, 'inf0'))
        self.assertTrue(sk_tableaux.rule_is_applicable(node1, 'inf1'))
        self.assertTrue(sk_tableaux.rule_is_applicable(node2, 'inf0'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node2, 'inf1'))

        # Try one with empty premises somewhere
        metainference = Inference(premises=[Inference(premises=[], conclusions=[Formula(['p'])])],
                                  conclusions=[Inference(premises=[Formula(['r'])], conclusions=[Formula(['p'])])])
        node1 = MetainferentialTableauxNode(metainference, index=TSST)
        node2 = MetainferentialTableauxNode(metainference, index=TSSTbar)
        self.assertFalse(sk_tableaux.rule_is_applicable(node1, 'inf0'))
        self.assertTrue(sk_tableaux.rule_is_applicable(node1, 'inf1'))
        self.assertTrue(sk_tableaux.rule_is_applicable(node2, 'inf0'))
        self.assertFalse(sk_tableaux.rule_is_applicable(node2, 'inf1'))

    def test_get_counterexample(self):
        empty = MetainferentialTableauxStandard(set())
        F = MetainferentialTableauxStandard({'0'})
        S = MetainferentialTableauxStandard({'1'})
        T = MetainferentialTableauxStandard({'1', 'i'})
        Sbar = MetainferentialTableauxStandard({'1'}, bar=True)
        TS = MetainferentialTableauxStandard([{'1', 'i'}, {'1'}], bar=False)

        root = MetainferentialTableauxNode(content=classical_parser.parse('~~(p or q)/p'), index=TS)
        node1 = MetainferentialTableauxNode(content=classical_parser.parse('~~(p or q)'), index=T, parent=root)
        node2 = MetainferentialTableauxNode(content=classical_parser.parse('q'), index=Sbar, parent=node1)
        node3 = MetainferentialTableauxNode(content=classical_parser.parse('p'), index=F, parent=node2)
        node4 = MetainferentialTableauxNode(content=classical_parser.parse('p'), index=T, parent=node1)
        node5 = MetainferentialTableauxNode(content=classical_parser.parse('q'), index=S, parent=node4)
        """
        ~~(p ∨ q) / p, [{'1', 'i'}, {'1'}]
        └── ~~(p ∨ q), {'1', 'i'}
            ├── q, -{'1'}
            │   └── p, {'0'}
            └── p, {'1', 'i'}
                └── q, {'1'}
        """
        # Takes the first branch, the bar is not counted
        self.assertEqual(sk_tableaux.get_counterexample(root), {'p': '0'})

        # Close the first branch, should get the q from the second
        node6 = MetainferentialTableauxNode(content=classical_parser.parse('p'), index=empty, parent=node3)
        self.assertEqual(sk_tableaux.get_counterexample(root), {'q': '1'})

        # Close the second branch, should now return None
        node7 = MetainferentialTableauxNode(content=classical_parser.parse('p'), index=empty, parent=node5)
        self.assertIs(sk_tableaux.get_counterexample(root), None)
