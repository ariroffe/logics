from copy import deepcopy

from anytree import PreOrderIter, LevelOrderIter

from logics.classes.propositional import Formula, Inference
from logics.classes.exceptions import SolverError
from logics.classes.propositional.proof_theories.tableaux import TableauxNode
from logics.classes.propositional.proof_theories.metainferential_tableaux import (
    MetainferentialTableauxNode, MetainferentialTableauxStandard
)


class TableauxSolver:
    """Solver for tableaux systems

    Will build a tree for an (either valid or invalid) inference. When a branch is closed, does not continue adding
    nodes to it. Does not have the rules hardcoded. The ``solve`` method takes a tableaux system as parameter, and the
    tableaux solver will derive with the rules of the system you give it.

    Attributes
    ----------
    beggining_premise_index: int or None
        Class attribute representing the index that the premises have at the beggining of the derivation.
        ``None`` by default.
    beggining_conclusion_index: int or None
        Class attribute representing the index that the conclusion has at the beggining of the derivation.
        ``None`` by default.
    """
    allow_repetition_of_nodes = True
    beggining_premise_index = None
    beggining_conclusion_index = None

    def solve(self, inference, tableaux_system, beggining_index=None, max_depth=100):
        """Builds a tableaux for an inference, given a tableaux system with which to operate.

        Parameters
        ----------
        inference: logics.classes.propositional.Inference
            The Inference to build a tableaux for
        tableaux_system: logics.classes.propositional.proof_theories.TableauxSystem
            A TableauxSystem or any class that inherits from it.
        beggining_index: list or set, optional
            For systems that require you to specify a label at the beginning of the proof (e.g. for metainferential tableaux
            it can be things like {'1'}, {'1', 'i'}, [{'1', 'i'}, {'1'}], [[{'1', 'i'}, {'1'}], [{'1'}, {'1', 'i'}]]
            for S, T, TS, TS/ST, respectively)
        max_depth: int, optional
            The maximum depth that a tableaux can have. Default is 100. Set it to ``None`` if you want infinity.

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.utils.solvers.tableaux import standard_tableaux_solver  # <-- The default instance of the solver
        >>> from logics.instances.propositional.tableaux import classical_tableaux_system
        >>> tree = standard_tableaux_solver.solve(classical_parser.parse("~(p ∨ q) / ~p ∧ ~q"), classical_tableaux_system)
        >>> tree.print_tree(classical_parser)
        ~(p ∨ q)
        └── ~(~p ∧ ~q)
            └── ~p (R~∨)
                └── ~q (R~∨)
                    ├── ~~p (R~∧)
                    └── ~~q (R~∧)
        >>> tree = standard_tableaux_solver.solve(classical_parser.parse("p ↔ ~(q → r) / ~~p ∨ q"), classical_tableaux_system)
        >>> tree.print_tree(classical_parser)
        (p ↔ ~(q → r))
        └── ~(~~p ∨ q)
            ├── p (R↔)
            │   └── ~(q → r) (R↔)
            │       └── ~~~p (R~∨)
            │           └── ~q (R~∨)
            │               └── q (R~→)
            │                   └── ~r (R~→)
            └── ~p (R↔)
                └── ~~(q → r) (R↔)
                    └── ~~~p (R~∨)
                        └── ~q (R~∨)
                            └── (q → r) (R~~)
                                └── ~p (R~~)
                                    ├── ~q (R→)
                                    └── r (R→)
        """
        tableaux = self._begin_tableaux(inference, beggining_index)

        # For each node of the tableaux (including the ones we add dynamically)
        for node in LevelOrderIter(tableaux):  # LevelOrder so that it does not get stuck on a branch
            # We go rule by rule seeing if it can be applied
            for rule_name in tableaux_system.rules:
                result = tableaux_system.rule_is_applicable(node, rule_name, return_subst_dict=True)
                applicable = result[0]
                if applicable:
                    # Get the rule and substitute the metavariables for formulae in it
                    subst_dict = result[1]
                    rule = tableaux_system.rules[rule_name]
                    rule_application = self.apply_rule(tableaux_system, rule_name, rule, subst_dict)

                    # Now get everything that isn't a premise in the tree obtained and add it to every open branch
                    rule_application_last_prem = self._get_last_premise_node(rule_application)
                    counter = 1
                    for leaf in node.leaves:
                        if not tableaux_system.node_is_closed(leaf):
                            # _add_children_to_leaf may change the root, so if this is not the last leaf,
                            # we need to copy the rule last prem subtree
                            root = rule_application_last_prem
                            if counter != len(node.leaves):
                                root = deepcopy(root)
                            counter += 1

                            self._add_children_to_leaf(root, leaf)

                    # After applying the rule we may have new leaves
                    some_leaf_open = False
                    for leaf in tableaux.leaves:
                        if max_depth is not None and leaf.depth == max_depth:
                            raise SolverError('Could not solve the tree. Maximum depth exceeded')

                        if not tableaux_system.node_is_closed(leaf):
                            some_leaf_open = True
                    if not some_leaf_open:
                        return tableaux

        return tableaux

    def _get_last_premise_node(self, rule_application):
        last_prem = None
        for node in PreOrderIter(rule_application):  # This assumes that the rule premises do not branch
            if node.justification is None:
                last_prem = node
            else:
                break
        return last_prem

    def _add_children_to_leaf(self, root, leaf):
        """
        Takes a tree (a root node, e.g. the last premise of a rule application) and a leaf from a different tree
        (e.g. a leaf in the current solver tree) and adds all the children of the first to the second.

        WARNING: It may modify the `root` tree, do not use again after passing it to this function (or deepcopy before)
        """
        num_children = len(root.children)  # need to calculate it here bc it will change dynamically in what follows
        for child in root.children:
            if self.allow_repetition_of_nodes:
                # If nodes can be repeated, simply attach the child to the leaf. The subree below it is kept
                child.parent = leaf

            else:
                # If there is only one child and it already occurs in the tree, skip
                if num_children == 1 and (child.content, child.index) in [(n.content, n.index) for n in leaf.path]:
                    child.parent = None  # For uniformity, bc the other clauses alter the root's child
                    self._add_children_to_leaf(child, leaf)  # Move to next node without doing anything with child
                else:  # there is more than one child or the child is not repeated
                    child.parent = leaf
                    self._add_children_to_leaf(child, child)  # The child is both the new leaf and new root

    def apply_rule(self, tableaux_system, rule_name, rule, subst_dict):
        return rule.instantiate(tableaux_system.language, subst_dict, instantiate_children=True)

    def _begin_tableaux(self, inference, beggining_index=None):
        """
        Initialize the tableaux by putting every premise and negated conclusion as a node
        May need to be overwritten for some non-classical systems
        """
        parent = None
        for premise in inference.premises:
            new_node = TableauxNode(content=premise, index=self.beggining_premise_index, parent=parent)
            parent = new_node
        for conclusion in inference.conclusions:
            new_node = TableauxNode(content=Formula(['~', conclusion]), index=self.beggining_conclusion_index,
                                    parent=parent)
            parent = new_node
        return new_node.root


standard_tableaux_solver = TableauxSolver()


# ----------------------------------------------------------------------------------------------------------------------
# SOLVERS FOR OTHER LOGIC SYSTEMS

class IndexedTableauxSolver(TableauxSolver):
    """Class for classical indexed and many-valued tableaux systems

    Basically the same as the above solver, only changes the way in which the tableaux is initialized
    (does not negate the conclusion, ``beggining_premise_index`` is 1, ``beggining_conclusion_index`` is 0)

    Examples
    --------
    >>> from logics.utils.parsers import classical_parser
    >>> from logics.utils.solvers.tableaux import indexed_tableaux_solver  # <-- The default instance of the solver
    >>> from logics.instances.propositional.tableaux import LP_tableaux_system
    >>> tree = indexed_tableaux_solver.solve(classical_parser.parse("~(p ∨ q) / ~~p ∧ ~~q"), LP_tableaux_system)
    >>> tree.print_tree(classical_parser)
    ~(p ∨ q), 1
    └── (~~p ∧ ~~q), 0
        └── (~p ∧ ~q), 1 (R~∨1)
            ├── ~~p, 0 (R∧0)
            │   └── ~p, 1 (R∧1)
            │       └── ~q, 1 (R∧1)
            │           └── p, 0 (R~~0)
            └── ~~q, 0 (R∧0)
                └── ~p, 1 (R∧1)
                    └── ~q, 1 (R∧1)
                        └── q, 0 (R~~0)
    """

    beggining_premise_index = 1
    beggining_conclusion_index = 0

    def _begin_tableaux(self, inference, beggining_index=None):
        """
        Conclusions are not negated in MV systems
        """
        parent = None
        for premise in inference.premises:
            new_node = TableauxNode(content=premise, index=self.beggining_premise_index, parent=parent)
            parent = new_node
        for conclusion in inference.conclusions:
            new_node = TableauxNode(content=conclusion, index=self.beggining_conclusion_index, parent=parent)
            parent = new_node
        return new_node.root


indexed_tableaux_solver = IndexedTableauxSolver()


# -----------------------------------------------
class MetainferentialTableauxSolver(TableauxSolver):
    """Solver class for many-valued metainferential systems

    The default instance of the class it at ``logics.utils.solvers.tableaux.metainferential_tableaux_solver``

    The ``solve`` method takes as parameters:

    * `inference`: a `logics.classes.propositional.Inference`
    * `tableaux_system`: a `logics.classes.propositional.proof_theories.tableaux.MetainferentialTableauxSystem`
    * `beggining_index`: a list or set like ``[{'1', 'i'}, {'1'}]``. Note that this is **not** a
      ``MetainferentialTableauxStandard`` -those are reserved for tableaux nodes.

    Examples
    --------
    >>> from logics.utils.parsers import classical_parser
    >>> from logics.instances.propositional.metainferential_tableaux import SK_metainferential_tableaux_system as sk_tableaux
    >>> from logics.utils.solvers.tableaux import metainferential_tableaux_solver
    >>> meta_explosion = classical_parser.parse('(/ p ∧ ~p) // (/q)')
    >>> tree = metainferential_tableaux_solver.solve(
    ...     inference=meta_explosion,
    ...     tableaux_system=sk_tableaux,
    ...     beggining_index=[[{'1', 'i'}, {'1'}], [{'1'}, {'1', 'i'}]]  # TS/ST, closed
    ... )
    >>> tree.print_tree(classical_parser)
    (/ p ∧ ~p) // (/ q), -[[{'1', 'i'}, {'1'}], [{'1'}, {'1', 'i'}]]
    └── / p ∧ ~p, [{'1', 'i'}, {'1'}] (inf0)
        └── / q, -[{'1'}, {'1', 'i'}] (inf0)
            └── p ∧ ~p, {'1'} (inf1)
                └── q, -{'1', 'i'} (inf0)
                    └── p, {'1'} (R∧1)
                        └── ~p, {'1'} (R∧1)
                            └── q, {'0'} (complement)
                                └── p, {'0'} (R~1)
                                    └── p, set() (intersection)
    >>> sk_tableaux.tree_is_closed(tree)
    True
    >>> tree = metainferential_tableaux_solver.solve(
    ...     inference=meta_explosion,
    ...     tableaux_system=sk_tableaux,
    ...     beggining_index=[[{'1'}, {'1', 'i'}], [{'1'}, {'1', 'i'}]], # ST/ST, not closed
    ... )
    >>> tree.print_tree(classical_parser)
    (/ p ∧ ~p) // (/ q), -[[{'1'}, {'1', 'i'}], [{'1'}, {'1', 'i'}]]
    └── / p ∧ ~p, [{'1'}, {'1', 'i'}] (inf0)
        └── / q, -[{'1'}, {'1', 'i'}] (inf0)
            └── p ∧ ~p, {'1', 'i'} (inf1)
                └── q, -{'1', 'i'} (inf0)
                    ├── p ∧ ~p, {'1'} (singleton)
                    │   └── q, {'0'} (complement)
                    │       └── p, {'1'} (R∧1)
                    │           └── ~p, {'1'} (R∧1)
                    │               └── p, {'0'} (R~1)
                    │                   └── p, set() (intersection)
                    └── p ∧ ~p, {'i'} (singleton)
                        └── q, {'0'} (complement)
                            ├── p, {'1', 'i'} (R∧i)
                            │   └── ~p, {'i'} (R∧i)
                            │       ├── p, {'1'} (singleton)
                            │       │   └── p, {'i'} (R~1)
                            │       │       └── p, set() (intersection)
                            │       └── p, {'i'} (singleton)
                            └── p, {'i'} (R∧i)
                                └── ~p, {'1', 'i'} (R∧i)
                                    ├── ~p, {'1'} (singleton)
                                    │   └── p, {'0'} (R~1)
                                    │       └── p, set() (intersection)
                                    └── ~p, {'i'} (singleton)
    >>> sk_tableaux.tree_is_closed(tree)
    False
    """
    allow_repetition_of_nodes = False

    def _begin_tableaux(self, inference, beggining_index):
        """
        Beggining index must be a list / set, not a MetainferentialTableauxStandard
        """
        return MetainferentialTableauxNode(
            content=inference,
            index=MetainferentialTableauxStandard(deepcopy(beggining_index), bar=True)
        )

    def apply_rule(self, tableaux_system, rule_name, rule, subst_dict):
        # This is kind of a hack. Since some rules in this system are more complicated, we hardcode their instantiaton.
        # e.g. they contain inference variables (which logics does not have) -inf0, inf1, lowering and lifting rules
        # or require you to do complex operations on the standards (e.g. the singleton, intersection, and bar rules)

        # Rules for inferences
        if rule_name == "inf0" or rule_name == "inf1":
            premises, conclusions = subst_dict['Γ'], subst_dict['Δ']
            root_inference = Inference(premises=premises, conclusions=conclusions)
            X, Y = subst_dict['X'], subst_dict['Y']

            if rule_name == "inf0":
                # Root node
                last_node = MetainferentialTableauxNode(content=root_inference,
                                                        index=MetainferentialTableauxStandard([X, Y], bar=True),
                                                        justification=None)
                # Premises
                for premise in premises:
                    last_node = MetainferentialTableauxNode(content=deepcopy(premise), index=deepcopy(X),
                                                            justification="inf0", parent=last_node)
                # Conclusions
                Ybar = deepcopy(Y)
                Ybar.bar = True
                for conclusion in conclusions:
                    last_node = MetainferentialTableauxNode(content=deepcopy(conclusion), index=deepcopy(Ybar),
                                                            justification="inf0", parent=last_node)
                return last_node.root

            elif rule_name == "inf1":
                # Root node
                root_node = MetainferentialTableauxNode(
                    content=Inference(premises=premises, conclusions=conclusions),
                    index=MetainferentialTableauxStandard([subst_dict['X'], subst_dict['Y']]),
                    justification=None
                )
                # Premises
                Xbar = deepcopy(X)
                Xbar.bar = True
                for premise in premises:
                    MetainferentialTableauxNode(content=deepcopy(premise), index=deepcopy(Xbar), justification="inf1",
                                                parent=root_node)
                # Conclusions
                for conclusion in conclusions:
                    MetainferentialTableauxNode(content=deepcopy(conclusion), index=deepcopy(Y), justification="inf1",
                                                parent=root_node)
                return root_node

        # Rules for formulae
        elif rule_name == "singleton" or rule_name == "intersection" or rule_name == "complement":
            formula = subst_dict['A']
            beginning_standard = subst_dict['X']

            if rule_name == "singleton":
                root = MetainferentialTableauxNode(content=deepcopy(formula), index=deepcopy(beginning_standard))
                for value in beginning_standard.content:
                    MetainferentialTableauxNode(
                        content=deepcopy(formula),
                        index=MetainferentialTableauxStandard(content={value}),
                        justification='singleton',
                        parent=root,
                    )
                return root

            elif rule_name == "intersection":
                beginning_standard2 = subst_dict['Y']
                root = MetainferentialTableauxNode(content=deepcopy(formula), index=deepcopy(beginning_standard))
                root2 = MetainferentialTableauxNode(content=deepcopy(formula), index=deepcopy(beginning_standard2),
                                                    parent=root)
                intersection_standard = MetainferentialTableauxStandard(
                    content=beginning_standard.content.intersection(beginning_standard2.content), bar=False
                )
                MetainferentialTableauxNode(
                    content=deepcopy(formula),
                    index=intersection_standard,
                    justification='intersection',
                    parent=root2)
                return root

            elif rule_name == "complement":
                new_standard = MetainferentialTableauxStandard(
                    content=tableaux_system.base_indexes.difference(beginning_standard.content), bar=False
                )
                root = MetainferentialTableauxNode(content=deepcopy(formula), index=deepcopy(beginning_standard))
                MetainferentialTableauxNode(
                    content=deepcopy(formula),
                    index=new_standard,
                    justification='complement',
                    parent=root
                )
                return root

        else:
            # In every other case, the rules behave as usual, so we return the super method
            return super().apply_rule(tableaux_system, rule_name, rule, subst_dict)


metainferential_tableaux_solver = MetainferentialTableauxSolver()


class ModalTableauxSolver(TableauxSolver):
    beggining_premise_index = 0
    beggining_conclusion_index = 0

    # Aca en solve guardar en una lista los nodos de PreOrderIter, y aplicar solo si esta en la lista
    # tod eso wrappeado en un while que trackee si hubo algun cambio


# ----------------------------------------------------------------------------------------------------------------------
# ----------------------------------------------------------------------------------------------------------------------

class ConstructiveTreeSolver(TableauxSolver):
    """Solver that returns the constructive tree of a formula

    Examples
    --------

    """
    def _begin_tableaux(self, inference, beggining_index=None):
        # In this case inference will be a formula
        return TableauxNode(content=inference, parent=None)


constructive_tree_solver = ConstructiveTreeSolver()
