from copy import deepcopy

from anytree import PreOrderIter, LevelOrderIter

from logics.classes.propositional import Formula
from logics.classes.exceptions import SolverError
from logics.classes.propositional.proof_theories.tableaux import TableauxNode


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

    beggining_premise_index = None
    beggining_conclusion_index = None

    def solve(self, inference, tableaux_system, max_depth=100):
        """Builds a tableaux for an inference, given a tableaux system with which to operate.

        Parameters
        ----------
        inference: logics.classes.propositional.Inference
            The Inference to build a tableaux for
        tableaux_system: logics.classes.propositional.proof_theories.TableauxSystem
            A TableauxSystem or any class that inherits from it.
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
        tableaux = self._begin_tableaux(inference)
        applied_rules = {rule_name: [] for rule_name in tableaux_system.rules}

        # For each node of the tableaux (including the ones we add dynamically)
        for node in LevelOrderIter(tableaux):  # LevelOrder so that it does not get stuck on a branch
            # We go rule by rule seeing if it can be applied
            for rule_name in tableaux_system.rules:
                result = tableaux_system.rule_is_applicable(node, rule_name, return_subst_dict=True)
                applicable = result[0]
                if applicable:
                    subst_dict = result[1]
                    rule = tableaux_system.rules[rule_name]
                    rule_application = rule.instantiate(tableaux_system.language, subst_dict)  # Has no parent

                    # applied_rules contains a list of the the instantiations of the rules. Done like this because
                    # in some modal systems, a rule may be applied twice to the same node & yield different results
                    if rule_application not in applied_rules[rule_name]:
                        applied_rules[rule_name].append(rule_application)

                        # We need to add the rule application last premise's children to every open branch
                        rule_application_last_prem = [n for n in PreOrderIter(rule_application) if
                                                      n.justification is None][-1]
                        for leaf in node.leaves:
                            if max_depth is not None and leaf.depth == max_depth:
                                raise SolverError('Could not solve the tree. Maximum depth exceeded')
                            if not tableaux_system.node_is_closed(leaf):
                                rule_application_children = list()
                                while rule_application_last_prem.children:
                                    # In order to put a copy of the rule child, we detach it, deepcopy, append
                                    # We reattach them all in the end so as to not modify the original order
                                    rule_child = rule_application_last_prem.children[0]
                                    rule_child.parent = None
                                    new_child = deepcopy(rule_child)
                                    new_child.parent = leaf
                                    rule_application_children.append(rule_child)
                                # Reattach all
                                rule_application_last_prem.children = rule_application_children

                        if tableaux_system.tree_is_closed(tableaux):
                            return tableaux

        return tableaux

    def _begin_tableaux(self, inference):
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

class ManyValuedTableauxSolver(TableauxSolver):
    """Class for many-valued tableaux systems

    Basically the same as the above solver, only changes the way in which the tableaux is initialized
    (does not negate the conclusion, ``beggining_premise_index`` is 1, ``beggining_conclusion_index`` is 0)

    Examples
    --------
    >>> from logics.utils.parsers import classical_parser
    >>> from logics.utils.solvers.tableaux import mvl_tableaux_solver  # <-- The default instance of the solver
    >>> from logics.instances.propositional.tableaux import LP_tableaux_system
    >>> tree = mvl_tableaux_solver.solve(classical_parser.parse("~(p ∨ q) / ~~p ∧ ~~q"), LP_tableaux_system)
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

    def _begin_tableaux(self, inference):
        """
        Conclusions are not negated in MV systems
        """
        parent = None
        for premise in inference.premises:
            new_node = TableauxNode(content=premise, index=self.beggining_premise_index, parent=parent)
            parent = new_node
        for conclusion in inference.conclusions:
            new_node = TableauxNode(content=conclusion, index=self.beggining_conclusion_index,
                                    parent=parent)
            parent = new_node
        return new_node.root


mvl_tableaux_solver = ManyValuedTableauxSolver()


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
    def _begin_tableaux(self, inference):
        # In this case inference will be a formula
        return TableauxNode(content=inference, parent=None)


constructive_tree_solver = ConstructiveTreeSolver()
