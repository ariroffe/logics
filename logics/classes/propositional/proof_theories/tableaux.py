"""
Tableaux implementation using AnyTree. See https://anytree.readthedocs.io/en/latest/
Because of how AnyTree works, the root node of a tableaux IS the tableaux.
"""
from copy import copy, deepcopy

from anytree import NodeMixin, RenderTree, PreOrderIter, LevelOrderIter

from logics.classes.propositional import Formula
from logics.classes.errors import ErrorCode, CorrectionError


class TableauxNode(NodeMixin):
    """Class for a tableaux node.

    Subclasses NodeMixin from the `anytree package <https://anytree.readthedocs.io/en/latest/>`_.
    Since a node can have children, it can also be taken to represent a tree (an entire tableaux), see below for some
    examples.

    Parameters
    ----------
    content: logics.classes.propositional.Formula
        The formula of the node
    index: int, optional
        An optional index for tableaux that have indexed nodes
    justification: str, optional
        If the node is non-root, this parameter should contain the name of the rule by which it was obtained
    parent: logics.classes.propositional.proof_theories.TableauxNode, optional
        The parent node. The root node of a tableaux has None as parent (the default value).
    children: list of logics.classes.propositional.proof_theories.TableauxNode, optional
        A list of the children node. Also optional. If child nodes are specified with the `parent` attribute, there
        is no need to provide this (see the example below).

    Examples
    --------
    Using the anytree package gives us a lot of base functionality. For example:

    >>> from logics.utils.parsers import classical_parser
    >>> from logics.classes.propositional.proof_theories import TableauxNode
    >>> n1 = TableauxNode(content=classical_parser.parse('~~~~p'))
    >>> n2 = TableauxNode(content=classical_parser.parse('~~p'), justification='R~~', parent=n1)
    >>> n3 = TableauxNode(content=classical_parser.parse('p'), justification='R~~', parent=n2)
    >>> n1.is_root
    True
    >>> n3.is_leaf
    True
    >>> n1.children  # returns (n2,)
    (['~', ['~', ['p']]] (R~~),)
    >>> n1.descendants  # returns (n2, n3)
    (['~', ['~', ['p']]] (R~~), ['p'] (R~~))
    >>> n3.root  # returns n1
    ['~', ['~', ['~', ['~', ['p']]]]]
    >>> n1.leaves  # returns (n3,)
    (['p'] (R~~),)
    >>> n3.path  # returns (n1, n2, n3)
    (['~', ['~', ['~', ['~', ['p']]]]], ['~', ['~', ['p']]] (R~~), ['p'] (R~~))
    >>> n3.depth
    2
    >>> n1.height
    2

    Notes
    -----
    The logics' extension of the anytree node class also includes some methods for pretty printing tableaux as trees,
    see below.
    """

    separator = '==>'

    def __init__(self, content, index=None, justification=None, parent=None, children=None):
        self.content = content
        self.index = index
        self.justification = justification
        self.parent = parent
        if children:
            self.children = children

    def is_instance_of(self, node, language, subst_dict=None, return_subst_dict=False):
        """Determines whether a node is as instance of another (schematic) node.

        A TableauxNode (`self`) is considered an instance of another TableauxNode (`node`) iff:

        * The content of `self` is an instance of the content of `node`
        * The index and justification of `self` are equal to the index and justification of `node`,
          or are `None` in `node`

        Parameters
        ----------
        node: logics.classes.propositional.proof_theories.TableauxNode
            The (schematic) TableauxNode of which we want to know if it is instance
        language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
            Instance of Language or InfiniteLanguage
        subst_dict: dict, optional
            A susbstitution dict of the form ``{'A': someformula, 'B': someformula}``
        return_subst_dict: bool, optional
            If ``True`` will additionally return a substitution dict.

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.languages import classical_language
        >>> from logics.classes.propositional.proof_theories import TableauxNode
        >>> n1 = TableauxNode(content=classical_parser.parse('~A'))
        >>> n2 = TableauxNode(content=classical_parser.parse('~~p'))
        >>> n2.is_instance_of(n1, classical_language)
        True
        >>> n2.is_instance_of(n1, classical_language, subst_dict={'A': classical_parser.parse('q')})
        False
        >>> n2.is_instance_of(n1, classical_language, return_subst_dict=True)
        (True, {'A': ['~', ['p']]})
        >>> n3 = TableauxNode(content=classical_parser.parse('~~p'), justification='R~~')
        >>> n3.is_instance_of(n1, classical_language)  # justification is None in n1
        True
        >>> n4 = TableauxNode(content=classical_parser.parse('A'), justification='R~~')
        >>> n2.is_instance_of(n4, classical_language)  # Justification is None in n2 but not in n4
        False

        Notes
        -----
        `subst_dict` and `return_subst_dict` are similar to the Formula homonymous methods.
        """
        if subst_dict is None:
            subst_dict = dict()

        # First check the index and justification (it is less costly)
        if (node.index is not None and self.index != node.index) or \
                (node.justification is not None and self.justification != node.justification):
            if not return_subst_dict:
                return False
            return False, subst_dict

        # Then check the content
        instance, subst_dict = self.content.is_instance_of(node.content, language, subst_dict, return_subst_dict=True)
        if not return_subst_dict:
            return instance
        return instance, subst_dict

    def instantiate(self, language, subst_dict, instantiate_children=True, first_iteration=True):
        """Given a TableauxNode with a schematic formula as content and a substitution dict, returns the schema
        instantiated with the dict.

        Will return a different TableauxNode object, and not modify the original. If the node given is not the root node
        will construct a new tree with the node given as root. The children will also be new nodes.

        Parameters
        ----------
        language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
            Instance of Language or InfiniteLanguage
        subst_dict: dict
            The susbstitution dict must have form ``{'A': someformula, 'B': someformula}``
        instantiate_children: bool, optional
            If ``True`` (default behavior), will also instantiate the children with the same substitution dict. Else,
            will leave them as is.
        first_iteration: bool, optional
            For recursion purposes, should not be altered.

        Returns
        -------
        logics.classes.propositional.proof_theories.TableauxNode
            A *different* formula instance from the original

        Raises
        ------
        ValueError
            if some schematic propositional within the formula has no substitution assigned in the dictionary

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.languages import classical_language
        >>> from logics.classes.propositional.proof_theories import TableauxNode
        >>> schema_parent = TableauxNode(content=classical_parser.parse('C'))
        >>> schema = TableauxNode(content=classical_parser.parse('A ∨ B'), parent=schema_parent)
        >>> schema_child = TableauxNode(content=classical_parser.parse('B'), parent=schema)
        >>> instance1 = schema.instantiate(classical_language,
        ...                                {'A': classical_parser.parse('p'), 'B': classical_parser.parse('q')},
        ...                                instantiate_children=True)
        >>> instance1
        ['∨', ['p'], ['q']]
        >>> instance1.parent is None  # the resulting node is the root of the new instance tree
        True
        >>> instance1.children
        (['q'],)
        >>> instance2 = schema.instantiate(classical_language,
        ...                                {'A': classical_parser.parse('p'), 'B': classical_parser.parse('q')},
        ...                                instantiate_children=False)
        >>> instance2
        ['∨', ['p'], ['q']]
        >>> instance2.children
        (['B'],)
        """
        # If it is the original node or (not the original but you want to instantiate its children as well)
        if first_iteration or instantiate_children:
            self_content_substitution = self.content.instantiate(language, subst_dict)
        # Else it is a child and you do not want to instantiate the content
        else:
            self_content_substitution = deepcopy(self.content)
        new_tableaux = self.__class__(content=self_content_substitution, index=self.index,
                                      justification=self.justification)

        for child_node in self.children:
            new_child = child_node.instantiate(language, subst_dict, instantiate_children, first_iteration=False)
            new_child.parent = new_tableaux

        return new_tableaux

    @property
    def child_index(self):
        """Returns the index of the node among the parent's children. E.g. if the node is the second sibling, returns 1.
        For the root it will return 0

        Examples
        --------
        >>> from logics.classes.propositional.proof_theories import TableauxNode
        >>> from logics.utils.parsers import classical_parser
        >>> n1 = TableauxNode(content=classical_parser.parse('~(A ∧ B)'))
        >>> n2 = TableauxNode(content=classical_parser.parse('~A'), justification='R∧', parent=n1)
        >>> n3 = TableauxNode(content=classical_parser.parse('~B'), justification='R∧', parent=n1)
        >>> n1.print_tree(classical_parser)  # For illustration purposes
        ~(A ∧ B)
        ├── ~A (R∧)
        └── ~B (R∧)
        >>> n2.child_index
        0
        >>> n3.child_index
        1
        >>> n1.child_index  # root node
        0
        """
        if self.is_root:
            return 0
        return self.parent.children.index(self)

    # ------------------------------------------------------------------------------------------------------------------
    # Methods to print the node / tree to the console

    def _self_string(self, parser=None):
        """Returns the content + the index and justification (if there are any) of the present node
        If a parser is given as argument, returns the content unparsed (see below for an example)
        """
        if not parser:
            s = f'{self.content}'
        else:
            s = f'{parser.unparse(self.content)}'
        if self.index is not None:
            s += f', {self.index}'
        if self.justification is not None:
            s += f' ({self.justification})'
        return s

    def __repr__(self):
        return self._self_string()

    def print_path(self, parser=None):
        """Will print a node and its *ancestors* in a pretty format

        If a parser is given as argument, returns the content unparsed

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.classes.propositional.proof_theories import TableauxNode
        >>> n1 = TableauxNode(content=classical_parser.parse('~~~~p'))
        >>> n2 = TableauxNode(content=classical_parser.parse('~~p'), justification='R~~', parent=n1)
        >>> n3 = TableauxNode(content=classical_parser.parse('p'), justification='R~~', parent=n2)
        >>> n3.print_path()
        ['~', ['~', ['~', ['~', ['p']]]]] ==> ['~', ['~', ['p']]] (R~~) ==> ['p'] (R~~)
        >>> n3.print_path(classical_parser)
        ~~~~p ==> ~~p (R~~) ==> p (R~~)
        """
        print(f' {self.separator} '.join([node._self_string(parser) for node in self.path]))

    def print_tree(self, parser=None):
        """Will print a node and its *descendants* in a pretty, tree-like, format

        If a parser is given as argument, returns the content unparsed

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.classes.propositional.proof_theories import TableauxNode
        >>> n1 = TableauxNode(content=classical_parser.parse('~~~~p'))
        >>> n2 = TableauxNode(content=classical_parser.parse('~~p'), justification='R~~', parent=n1)
        >>> n3 = TableauxNode(content=classical_parser.parse('p'), justification='R~~', parent=n2)
        >>> n1.print_tree()
        ['~', ['~', ['~', ['~', ['p']]]]], 0
        └── ['~', ['~', ['p']]], 0 (R~~)
            └── ['p'], 0 (R~~)
        >>> from logics.utils.parsers import classical_parser
        >>> n1.print_tree(classical_parser)
        ~~~~p, 0
        └── ~~p, 0 (R~~)
            └── p, 0 (R~~)
        """
        for pre, _, node in RenderTree(self):
            print(pre + node._self_string(parser))

    # The following raises hashing issues (for some reason I don't fully understand) so I remove it
    # def __eq__(self, other):
    #     """TableauxNode are compared without regards to their parents or children"""
    #     return isinstance(other, self.__class__) and \
    #         self.content == other.content and self.index == other.index and self.justification == other.justification
    #
    # def __ne__(self, other):
    #     return not self.__eq__(other)


# ----------------------------------------------------------------------------------------------------------------------
# ----------------------------------------------------------------------------------------------------------------------


class TableauxSystem:
    """Class for tableaux systems.

    Parameters
    ----------
    language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
        Instance of Language or InfiniteLanguage
    rules: dict (str: logics.classes.propositional.proof_theories.TableauxNode)
        The keys are strings (the name of the rule) and the values are TableauxNode (w/schematic content and children)
    closure_rules: list
        Each element of the list is a len2-list of (schematic) TableauxNode, e.g.
        ``[[TableauxNode(A), TableauxNode(~A)]]`` says that a node will be considered closed if A and ~A are found
        in its path.
    solver
        Any object with a ``solve`` method (which takes an inference and a tableaux system). ``None`` by default.

    Attributes
    ----------
    fast_node_is_closed_enabled: bool
        Class attribute. If ``True``, will consider a node closed if and only if it finds A, i and ~A, i in its path.
        Will not look at the closure rules, but rather follow this hardcoded rule.
        Is faster but less general than using closure rules.

    Examples
    --------
    Defining an example (toy) system with only conjunction and negation rules, and non-indexed nodes:

    >>> from logics.utils.parsers import classical_parser
    >>> from logics.instances.propositional.languages import classical_language
    >>> from logics.classes.propositional.proof_theories import TableauxNode, TableauxSystem

    We first define some rules:

    >>> double_negation_rule = TableauxNode(content=classical_parser.parse('~~A'))
    >>> TableauxNode(content=classical_parser.parse('A'), justification='R~~', parent=double_negation_rule)
    >>> double_negation_rule.print_tree(classical_parser)  # For illustration purposes
    ~~A
    └── A (R~~)
    >>> conjunction_rule = TableauxNode(content=classical_parser.parse('A ∧ B'))
    >>> conj_child1 = TableauxNode(content=classical_parser.parse('A'), justification='R∧', parent=conjunction_rule)
    >>> TableauxNode(content=classical_parser.parse('B'), justification='R∧', parent=conj_child1)
    >>> conjunction_rule.print_tree(classical_parser)  # For illustration purposes
    (A ∧ B)
    └── A (R∧)
        └── B (R∧)
    >>> neg_conjunction_rule = TableauxNode(content=classical_parser.parse('~(A ∧ B)'))
    >>> TableauxNode(content=classical_parser.parse('~A'), justification='R~∧', parent=neg_conjunction_rule)
    >>> TableauxNode(content=classical_parser.parse('~B'), justification='R~∧', parent=neg_conjunction_rule)
    >>> neg_conjunction_rule.print_tree(classical_parser)  # For illustration purposes
    ~(A ∧ B)
    ├── ~A (R~∧)
    └── ~B (R~∧)

    Now we can define the system:

    >>> system_rules = {
    ...     'R~~': double_negation_rule,
    ...     'R∧': conjunction_rule,
    ...     'R~∧': neg_conjunction_rule}
    >>> closure_rules = [
    ...     [TableauxNode(content=classical_parser.parse('~A')), TableauxNode(content=classical_parser.parse('A'))]
    ... ]  # This is actually not necessary since fast_node_is_closed_enabled is True by default
    >>> toy_tableaux_system = TableauxSystem(language=classical_language,
    ...                                      rules=system_rules,
    ...                                      closure_rules= closure_rules)

    Notes
    -----
    There are predefined instances of this class for known systems, see below.
    """

    # Assumes a branch is closed if a node and its negation (with the same index) are present in a branch:
    fast_node_is_closed_enabled = True

    def __init__(self, language, rules, closure_rules, solver=None):
        self.language = language
        self.rules = rules
        self.closure_rules = closure_rules
        self.solver = solver

    def node_is_closed(self, node):
        """Checks whether a node is closed, by looking at its *ancestors*

        A node is considered closed when an instance of a closure rule occurs in its path (see also the
        ``fast_node_is_closed_enabled`` class attribute).

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.classes.propositional.proof_theories import TableauxNode
        >>> from logics.instances.propositional.tableaux import classical_tableaux_system
        >>> n1 = TableauxNode(content=classical_parser.parse('~~~~p'))
        >>> n2 = TableauxNode(content=classical_parser.parse('~p'), parent=n1)
        >>> n3 = TableauxNode(content=classical_parser.parse('~~p'), justification='R~~', parent=n2)
        >>> n1.print_tree(classical_parser)  # For illustration purposes
        (~~~p)
        └── ~p
            └── ~~p (R~~)
        >>> classical_tableaux_system.node_is_closed(n2)
        False
        >>> classical_tableaux_system.node_is_closed(n3)
        True
        """
        # Execute the fast version below if enabled (check for a node and its negation)
        if self.fast_node_is_closed_enabled:
            return self._fast_node_is_closed(node)

        # Slow version for systems with more complicated closure rules (e.g. K3, FDE)
        # Checks every pair of nodes to see if they are instance of the closure rule's pair of nodes
        path = node.path
        for node2_index in range(len(path)):
            for node3_index in range(node2_index+1, len(path)):
                node2 = path[node2_index]
                node3 = path[node3_index]
                for closure_rule in self.closure_rules:
                    instance1, subst_dict2 = node2.is_instance_of(closure_rule[0], self.language,
                                                                  return_subst_dict=True)
                    if instance1:
                        instance2 = node3.is_instance_of(closure_rule[1], self.language, subst_dict2)
                        if instance2:
                            return True
                    # Check the reverse (current node is the second member of the closure rule)
                    instance3, subst_dict3 = node3.is_instance_of(closure_rule[0], self.language,
                                                                  return_subst_dict=True)
                    if instance3:
                        instance4 = node2.is_instance_of(closure_rule[1], self.language, subst_dict3)
                        if instance4:
                            return True
        return False

    @staticmethod
    def _fast_node_is_closed(node):
        """
        Much faster (but less general) node_is_closed implementation.
        Checks whether A, i and ~A, i are present in the branch
        """
        path = node.path
        # Basically, build a new list and add one node at a time, checking that its negation is not present
        # (or if it is a negated sentence, that the formula it negates is not present)
        new_list = [(path[0].content, path[0].index)]
        for node2 in path[1:]:
            if (Formula(['~', node2.content]), node2.index) in new_list:
                return True
            if node2.content.main_symbol == '~' and (node2.content[1], node2.index) in new_list:
                return True
            new_list.append((node2.content, node2.index))
        return False

    def tree_is_closed(self, node):
        """Same as above, but checks if all *descendant* branches (including the current node) are closed

        Will consider the node given as the root of the tableaux (i.e. will not look at its ancestors).

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.classes.propositional.proof_theories import TableauxNode
        >>> from logics.instances.propositional.tableaux import classical_tableaux_system
        >>> n1 = TableauxNode(content=classical_parser.parse('~~p ∧ q'))
        >>> n2 = TableauxNode(content=classical_parser.parse('~p'), parent=n1)
        >>> n3 = TableauxNode(content=classical_parser.parse('q'), justification='R∧', parent=n2)
        >>> n4 = TableauxNode(content=classical_parser.parse('p'), justification='R~~', parent=n3)
        >>> n1.print_tree(classical_parser)  # For illustration purposes
        (~~p ∧ q)
        └── ~p
            └── q (R∧)
                └── p (R~~)
        >>> classical_tableaux_system.tree_is_closed(n1)
        True
        >>> classical_tableaux_system.tree_is_closed(n3)
        False
        """
        # Detach the parent to evaluate closure only from here (the node_is_closed method looks at parents)
        parent = node.parent
        node.parent = None

        for node2 in node.leaves:
            if not self.node_is_closed(node2):
                # Re-attach parent before returning
                node.parent = parent
                return False

        # Re-attach parent before returning
        node.parent = parent
        return True

    def rule_is_applicable(self, node, rule_name, return_subst_dict=False):
        """Given a node and a rule name, determines if the rule can be applied to the node.

        If the rule has more than one premise, the node must be an instance of the *last* premise of the rule,
        and instances of the rest of the premises should be present above in the tree.

        Parameters
        ----------
        node: logics.classes.propositional.proof_theories.TableauxNode
            The node we want to look at
        rule_name: str
            The name of the rule. Should be present as key in TableauxSystem ``rules`` parameter
        return_subst_dict: bool
            If ``True`` will additionally return a substitution dict.

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.classes.propositional.proof_theories import TableauxNode
        >>> from logics.instances.propositional.tableaux import classical_tableaux_system
        >>> n1 = TableauxNode(content=classical_parser.parse('~~p ∧ q'))
        >>> classical_tableaux_system.rule_is_applicable(n1, 'R~~')
        False
        >>> classical_tableaux_system.rule_is_applicable(n1, 'R∧')
        True
        >>> classical_tableaux_system.rule_is_applicable(n1, 'R∧', return_subst_dict=True)
        (True, {'A': ['~', ['~', ['p']]], 'B': ['q']})
        True
        """
        rule = self.rules[rule_name]
        rule_prems = [n for n in PreOrderIter(rule) if n.justification is None]  # Rule premises
        instance, subst_dict = node.is_instance_of(rule_prems[-1], self.language, return_subst_dict=True)
        if instance:
            # If it is, check that the rest of the premises of the rule (if there are any) are present
            remaining_prems = rule_prems[:-1]
            if remaining_prems:
                # Walk up the path from the current node
                for node2 in node.iter_path_reverse():
                    result2 = node2.is_instance_of(remaining_prems[-1], self.language, subst_dict,
                                                   return_subst_dict=True)
                    instance2 = result2[0]
                    if instance2:
                        subst_dict.update(result2[1])
                        del remaining_prems[-1]
                        if not remaining_prems:
                            break

            if not remaining_prems:  # The rule can be applied
                if not return_subst_dict:
                    return True
                return True, subst_dict

        else:
            if not return_subst_dict:
                return False
            return False, subst_dict

    def is_correct_tree(self, tree, inference=None, return_error_list=False, exit_on_first_error=False, parser=None):
        """Checks if a given tableaux (a node and its descendants) is correctly derived, given the rules of the system.

        Parameters
        ----------
        tree: logics.classes.propositional.proof_theories.TableauxNode
            A ``TableauxNode``, posssibly with children.
        inference: logics.classes.propositional.Inference or None, optional
            If ``None``, will just check correct application of the rules. If an inference, will check that the steps
            with no justification are either premises or the negation of the conclusion (this behavior can be overriden
            for other systems, see the source code).
        return_error_list: bool, optional
            If False, will just return True or False (exits when it finds an error, more efficient) If True, will return
            (True, a list of ``logics.classes.errors.CorrectionError``)
        exit_on_first_error: bool, optional
            If `return_error_list` and this are both true, it will return a list with a single error instead of many.
            More efficient, since it makes early exits.
        parser: logics.utils.parsers.standard_parser.StandardParser, optional
            If present, will return the error list with unparsed instead of parsed formulae.
            Can be of another class that implements ``unparse`` for ``Formula``.
            Can be the ``classical_parser`` (see below in the Examples) or some other parser defined by the user.

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.classes.propositional.proof_theories import TableauxNode
        >>> from logics.instances.propositional.tableaux import classical_tableaux_system

        A correct derivation of ``~~p ∧ q / p``:

        >>> n1 = TableauxNode(content=classical_parser.parse('~~p ∧ q'))
        >>> n2 = TableauxNode(content=classical_parser.parse('~p'), parent=n1)
        >>> n3 = TableauxNode(content=classical_parser.parse('~~p'), justification='R∧', parent=n2)
        >>> n4 = TableauxNode(content=classical_parser.parse('q'), justification='R∧', parent=n3)
        >>> n5 = TableauxNode(content=classical_parser.parse('p'), justification='R~~', parent=n4)
        >>> n1.print_tree(classical_parser)  # For illustration purposes
        (~~p ∧ q)
        └── ~p
            └── q (R∧)
                └── p (R~~)
        >>> classical_tableaux_system.is_correct_tree(n1)
        True
        >>> classical_tableaux_system.is_correct_tree(n1, inference=classical_parser.parse('~~p ∧ q / p'))
        True
        >>> classical_tableaux_system.is_correct_tree(n1, inference=classical_parser.parse('~~p ∧ q / ~p'))
        False
        >>> classical_tableaux_system.is_correct_tree(n1, inference=classical_parser.parse('~~p ∧ q / ~p'),
        ...                                           return_error_list=True)
        (False, [(): Conclusion ['~', ['p']] is not present in the tree, (0, 0): Node ['~', ['p']] is an incorrect premise node])
        >>> from logics.utils.parsers import classical_parser
        >>> classical_tableaux_system.is_correct_tree(n1, inference=classical_parser.parse('~~p ∧ q / ~p'),
        ...                                           return_error_list=True, parser=classical_parser)
        (False, [(): Conclusion ~p is not present in the tree, (0, 0): Node ~p is an incorrect premise node])

        Notes
        -----
        All premise nodes (including negations of conclusions) must come at the beginning of the tableaux, before
        any other rules are applied and before branching. Otherwise the tableaux will be marked as incorrect.
        """
        # Implementation works top-down, as follows. Will walk the tree from root to leaves, looking at:
        # - If the justification of the node is None (premise node), if inference is not None, will check that the
        #   content is either a premise or the negation of some conclusion, and add them to correctly_derived_nodes
        # - For all nodes (including premises) will then check if they are the last premise of some rule. If so, calls
        #   rule_is_applicable, which will look above it to see if the rest of the premises of the rule are present
        #   If they are:
        # - Will call the method is_correctly_applied(rule), which will check that the conclusions of the rule are
        #   present in every OPEN branch (the implementation of that is documented below). If they are, they are added
        #   to correcrlty_derived_nodes.
        # - Finally, checks if there are nodes in the tree that are not in correctly_derived_nodes

        error_list = list()
        correctly_derived_nodes = set()
        present_premises = set()
        present_conclusions = set()
        traversing_premises = True
        for node in LevelOrderIter(tree):
            # PREMISE NODES
            if node.justification is not None:
                traversing_premises = False
            else:
                # Premises must come at the beggining of the tableaux (to avoid premises present in only one branch)
                if not traversing_premises:
                    if not return_error_list:
                        return False
                    error_list.append(CorrectionError(code=ErrorCode.TBL_PREMISE_NOT_BEGINNING,
                                                      index=tuple(n.child_index for n in node.path),
                                                      description='Premise nodes must be at the beggining of the '
                                                                  'tableaux, before applying any rule and before '
                                                                  'opening any new branch'))
                    if exit_on_first_error:
                        return False, error_list

                # If an inference was given
                if inference is not None:
                    # Check that the node is a premise or negated conclusion of the inference
                    is_premise_idx, is_conclusion_idx = self._is_correct_premise_node(node, inference)
                    if is_premise_idx or is_conclusion_idx:
                        present_premises |= is_premise_idx
                        present_conclusions |= is_conclusion_idx
                        correctly_derived_nodes.add(node)  # Not really necessary but leave it just in case
                    else:
                        if not return_error_list:
                            return False
                        error_list.append(CorrectionError(code=ErrorCode.TBL_INCORRECT_PREMISE,
                                                          index=tuple(n.child_index for n in node.path),
                                                          description=f'Node {node._self_string(parser)} is an '
                                                                      f'incorrect premise node'))
                        if exit_on_first_error:
                            return False, error_list
                else:
                    correctly_derived_nodes.add(node)  # Not really necessary but leave it just in case
            if len(node.children) > 1:
                traversing_premises = False  # Cannot contain any further premises after opening a new branch

            # Check if a rule applies to the node and is correctly applied in the tree
            # e.g. if the node is a conjunction, see that both conjuncts are below in the tree, and save both conjuncts
            # as correctly derived nodes
            for rule_name in self.rules:
                # For each rule, see if the current node is an instance of the LAST premise of the rule
                result = self.rule_is_applicable(node, rule_name, return_subst_dict=True)
                applicable = result[0]
                if applicable:
                    subst_dict = result[1]
                    # Get the rule premises
                    rule_prems = [n for n in PreOrderIter(self.rules[rule_name]) if n.justification is None]
                    # See if the rule is correctly applied
                    # (rule_prems[-1] contains the last premise AND ITS SUBTREE)
                    result3 = self._is_correctly_applied(node, rule_prems[-1], correctly_derived_nodes, subst_dict)
                    correct = result3[0]
                    if not correct:
                        if not return_error_list:
                            return False
                        error_list.append(CorrectionError(code=ErrorCode.TBL_RULE_NOT_APPLIED,
                                                          index=tuple(n.child_index for n in node.path),
                                                          description=f'Rule {rule_name} was not applied to '
                                                                      f'node {node._self_string(parser)}'))
                        if exit_on_first_error:
                            return False, error_list
                    else:
                        correctly_derived_nodes |= result3[1]

        # After visiting all nodes, check that all premises and conclusions are present in the tableaux
        if inference is not None:
            # returns a bool, MUTATES ERROR_LIST
            all_premises_present = self._all_premises_present(inference, present_premises, present_conclusions,
                                                              return_error_list, error_list, exit_on_first_error, parser)
            if not all_premises_present:
                if not return_error_list:
                    return False
                if exit_on_first_error:
                    return False, error_list

        # After checking all nodes and all rules that can be applied to it, the correctly derived nodes should be
        # all the tree nodes (that are not premises),
        # otherwise there is some node which is unnacounted for by its previous nodes & the rules
        unaccounted_nodes = {n for n in PreOrderIter(tree) if
                             (n not in correctly_derived_nodes and n.justification is not None)}
        if unaccounted_nodes:
            if not return_error_list:
                return False
            for node in unaccounted_nodes:
                error_list.append(CorrectionError(code=ErrorCode.TBL_RULE_INCORRECTLY_APPLIED,
                                                  index=tuple(n.child_index for n in node.path),
                                                  description=f'Rule incorrectly applied to '
                                                              f'node {node._self_string(parser)}'))
                if exit_on_first_error:
                    return False, error_list

        # If you got to here with return_error_list = False, then everything is alright
        if not return_error_list:
            return True
        # Oterwise, check if there are errors
        if error_list:
            return False, sorted(error_list, key=lambda e: (len(e.index), e.index))  # errors sorted by LevelOrder
        return True, []

    def _is_correct_premise_node(self, node, inference):
        """
        For classical logic (default here) a premise node is correct if it is a premise or the negation of a conclusion
        May need to be overwritten for other non-classical systems

        Returns
        -------
        Two sets. Each may be empty (if the node is neither a premise nor a negated conclusion).
        Or it may contain a number/s. E.g. {0,1}, {} means that the node is the node is premises number 0 and 1 of the
        inference (both premises are the same, e.g. p, p / q)
        """
        # Check that the node is a premise of the inference
        premises = {idx for idx in range(len(inference.premises)) if inference.premises[idx] == node.content}
        conclusions = {idx for idx in range(len(inference.conclusions)) if
                       (node.content.main_symbol == '~' and inference.conclusions[idx] == node.content[1])}
        return premises, conclusions

    def _all_premises_present(self, inference, present_premises, present_conclusions, return_error_list, error_list,
                              exit_on_first_error, parser):
        """After visiting all nodes, check that all premises and negated conclusions are present"""
        not_present_premises = set(range(len(inference.premises))) - present_premises
        not_present_conclusions = set(range(len(inference.conclusions))) - present_conclusions
        if not_present_premises:
            if not return_error_list:
                return False
            for not_present_premise_idx in not_present_premises:
                prem = inference.premises[not_present_premise_idx]
                if parser:
                    prem = parser.unparse(prem)
                error_list.append(CorrectionError(code=ErrorCode.TBL_PREMISE_NOT_PRESENT, index=tuple(),
                                                  description=f'Premise {prem} is not present in the tree'))
                if exit_on_first_error:
                    return False
        if not_present_conclusions:
            if not return_error_list:
                return False
            for not_present_conclusion_idx in not_present_conclusions:
                concl = inference.conclusions[not_present_conclusion_idx]
                if parser:
                    concl = parser.unparse(concl)
                error_list.append(CorrectionError(code=ErrorCode.TBL_CONCLUSION_NOT_PRESENT, index=tuple(),
                                                  description=f'Conclusion {concl} is not present in the tree'))
                if exit_on_first_error:
                    return False
        return True

    def _is_correctly_applied(self, start_node, rule_subtree, correctly_derived_nodes, subst_dict=None):
        """
        Both start_node and rule_subtree are TableauxNode.
        correctly_derived_nodes is a set of TableauxNodes
        subst_dict is for uniform substituion, as always
        Returns a boolean and a set of nodes (to add to correctly_derived_nodes)

        This function works recursively in order to walk the tree. Works like follows:
        - Rule subtree contains the last premise of the rule and its subtree below
        - Checks if the derivation provided has as immediate children (instances of) the children of the rule
          * If it does not, then the rule is applied below in the instance derivation (and another rule was applied at
            that step). So, it sends the entire rule to all the children to check for application below them
          * If it does, then the rule may have more children for each branch (for example, biconditional opens two
            branches and has two children in each branch). So, to each branch it sends as a rule the children (AND THEIR
            DESCENDANTS) to match with this same algorithm
          * If you reach the end of the instance tree, check if the final node is closed. If it is, then the rule
            is considered correctly applied (there is no need to apply further rules to closed branches)
        """
        if subst_dict is None:
            subst_dict = dict()

        # Base step: either rule_subtree or start_node are leafs
        if rule_subtree.is_leaf:
            return True, correctly_derived_nodes, subst_dict
            # Since we have already checked that start_node is instance of rule_subtree when calling this method
        if start_node.is_leaf:
            if self.node_is_closed(start_node):  # If it is closed, then we dont need to apply the rule in question
                return True, correctly_derived_nodes, subst_dict
            return False, correctly_derived_nodes, subst_dict

        # Check if the start node's children are instances of the rule's children
        children_are_instance = True
        # If the number of children is different they are not
        if len(start_node.children) != len(rule_subtree.children):
            children_are_instance = False
        else:
            subst_dict2 = dict()  # kwargs2 should be used only if all the children are instance
            for index in range(len(start_node.children)):
                node_child = start_node.children[index]
                # If the child is in correctly_derived_nodes then it is an application of a previous rule, not this one
                if node_child in correctly_derived_nodes:
                    children_are_instance = False
                else:
                    rule_child = rule_subtree.children[index]
                    result = node_child.is_instance_of(rule_child, self.language, subst_dict, return_subst_dict=True)
                    instance = result[0]
                    subst_dict2.update(result[1])
                    if not instance:
                        children_are_instance = False

        # If they are not instance, then the rule subtree must be applied to each child for the tree to be correct
        if not children_are_instance:
            correctly_derived_nodes2 = copy(correctly_derived_nodes)
            for node_child in start_node.children:
                result2 = self._is_correctly_applied(node_child, rule_subtree, correctly_derived_nodes, subst_dict)
                correct = result2[0]
                correctly_derived_nodes2 |= result2[1]  # Save the correct nodes in case they are correctly applied
                subst_dict.update(result2[2])
                if not correct:
                    return False, correctly_derived_nodes, subst_dict
            # If you did not return up to here, it is because the rule was correctly applied
            return True, correctly_derived_nodes2, subst_dict

        # If the children are instance we need to give each child the corresponding part of the rule subtree
        else:
            correctly_derived_nodes3 = copy(correctly_derived_nodes)
            for index in range(len(start_node.children)):
                node_child = start_node.children[index]
                rule_child = rule_subtree.children[index]
                # Use kwargs2 in order to maintain the dict from the above children isntance check
                result3 = self._is_correctly_applied(node_child, rule_child, correctly_derived_nodes, subst_dict2)
                correct = result3[0]
                correctly_derived_nodes3 |= result3[1]
                subst_dict2.update(result3[2])
                if not correct:
                    return False, correctly_derived_nodes, subst_dict2
            # If you did not return up to here, it is because the rule was correctly applied
            # We now need to add the start_node's children as correctly derived nodes
            correctly_derived_nodes3 |= set(start_node.children)
            return True, correctly_derived_nodes3, subst_dict2

    def solve_tree(self, inference):
        """Takes an inference and returns its tree-derivation

        For this to work, the parameter ``solver`` must be assigned.

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.tableaux import classical_tableaux_system
        >>> tree = classical_tableaux_system.solve_tree(classical_parser.parse("~(p ∧ q) / ~p ∨ ~q"))
        >>> tree.print_tree(classical_parser)
        ~(p ∧ q)
        └── ~(~p ∨ ~q)
            ├── ~p (R~∧)
            │   └── ~~p (R~∨)
            │       └── ~~q (R~∨)
            └── ~q (R~∧)
                └── ~~p (R~∨)
                    └── ~~q (R~∨)
        """
        if self.solver is not None:
            return self.solver.solve(inference, self)
        raise AttributeError("The current tableaux system has no solver assigned")

    def is_valid(self, inference):
        """Takes an inference and determines wheter it is valid

        For this to work, the parameter ``solver`` must be assigned.

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.tableaux import classical_tableaux_system
        >>> classical_tableaux_system.is_valid(classical_parser.parse("~(p ∧ q) / ~p ∨ ~q"))
        True
        >>> classical_tableaux_system.is_valid(classical_parser.parse("p / q"))
        False
        """
        tableaux = self.solve_tree(inference)
        return self.tree_is_closed(tableaux)


class ManyValuedTableauxSystem(TableauxSystem):
    """Class for many-valued tableaux systems.

    Basically the same as the above, only overrides what it considers a correct non-justified node,
    since the initial nodes have form ``premise, 1`` or ``conclusion, 0``. Note that ``A, 0`` and ``~A, 1`` are
    different claims in this kind of system.

    Examples
    --------
    >>> from logics.utils.parsers import classical_parser
    >>> from logics.classes.propositional.proof_theories import TableauxNode
    >>> from logics.instances.propositional.tableaux import FDE_tableaux_system
    >>> inference = classical_parser.parse("~~p ∧ q / p")

    Incorrectly initializing the tableaux:

    >>> n1 = TableauxNode(content=classical_parser.parse('~~p ∧ q'), index=1)
    >>> n2 = TableauxNode(content=classical_parser.parse('~p'), index=1, parent=n1)
    >>> n3 = TableauxNode(content=classical_parser.parse('~~p'), index=1, justification="R∧1", parent=n2)
    >>> n4 = TableauxNode(content=classical_parser.parse('q'), index=1, justification="R∧1", parent=n3)
    >>> n5 = TableauxNode(content=classical_parser.parse('p'), index=1, justification="R~~1", parent=n4)
    >>> n1.print_tree(classical_parser)  # For illustration purposes
    (~~p ∧ q), 1
    └── ~p, 1
        └── ~~p, 1 (R∧1)
            └── q, 1 (R∧1)
                └── p, 1 (R~~1)
    >>> FDE_tableaux_system.is_correct_tree(n1, inference=inference)
    False
    >>> FDE_tableaux_system.is_correct_tree(n1, inference=inference, return_error_list=True)
    (False, ["Node ['~', ['p']], 1 is an incorrect premise node", "Nodes {['~', ['p']], 1} are not accounted for in the derivation"])

    To initialize it correctly we must do the following:

    >>> n1 = TableauxNode(content=classical_parser.parse('~~p ∧ q'), index=1)
    >>> n2 = TableauxNode(content=classical_parser.parse('p'), index=0, parent=n1)  # <-- This changed
    >>> n3 = TableauxNode(content=classical_parser.parse('~~p'), index=1, justification="R∧1", parent=n2)
    >>> n4 = TableauxNode(content=classical_parser.parse('q'), index=1, justification="R∧1", parent=n3)
    >>> n5 = TableauxNode(content=classical_parser.parse('p'), index=1, justification="R~~1", parent=n4)
    >>> n1.print_tree(classical_parser)  # For illustration purposes
    (~~p ∧ q), 1
    └── p, 0
        └── ~~p, 1 (R∧1)
            └── q, 1 (R∧1)
                └── p, 1 (R~~1)
    >>> FDE_tableaux_system.is_correct_tree(n1, inference=inference)
    True
    >>> # Also considers it closed bc of how the closure rules are given to the instance, see below
    >>> FDE_tableaux_system.tree_is_closed(n1)
    True
    """
    fast_node_is_closed_enabled = False

    def _is_correct_premise_node(self, node, inference):
        """A premise A must be initialized as A, 1, a conclusion B as B, 0"""
        premises = {idx for idx in range(len(inference.premises)) if
                    (node.index == 1 and inference.premises[idx] == node.content)}
        conclusions = {idx for idx in range(len(inference.conclusions)) if
                       (node.index == 0 and inference.conclusions[idx] == node.content)}
        return premises, conclusions


class IndexedTableauxSystem(ManyValuedTableauxSystem, TableauxSystem):
    """Class for propositional indexed tableaux.

    Initializes nodes as the ``ManyValuedTableauxSystem``, and has ``[(A, 1), (A, 0)]`` as a hardcoded closure rule.
    """
    fast_node_is_closed_enabled = True

    @staticmethod
    def _fast_node_is_closed(node):
        """Checks whether A, 1 and A, 0 are present in the branch"""
        path = node.path
        # Basically, build a new list and add one node at a time, checking that its negation is not present
        # (or if it is a negated sentence, that the formula it negates is not present)
        new_list = [(path[0].content, path[0].index)]
        for node2 in path[1:]:
            if (node2.content, 1 - node2.index) in new_list:
                return True
            new_list.append((node2.content, node2.index))
        return False


# ----------------------------------------------------------------------------------------------------------------------
# ----------------------------------------------------------------------------------------------------------------------

class ConstructiveTreeSystem(TableauxSystem):
    """Constructive tree system for a given language

    Only takes a language (make sure it is an instance of ``InfiniteLanguage``) and, optionally, a solver.
    Will automatically build the tableaux rules from the given language.

    Examples
    --------
    >>> from logics.utils.parsers import classical_parser
    >>> from logics.instances.propositional.languages import classical_infinite_language
    >>> from logics.utils.solvers.tableaux import constructive_tree_solver
    >>> from logics.classes.propositional.proof_theories.tableaux import ConstructiveTreeSystem
    >>> classical_ct_system = ConstructiveTreeSystem(classical_infinite_language, solver=constructive_tree_solver)

    The rules are automatically built:

    >>> classical_ct_system.rules['R~'].print_tree(classical_parser)
    ~A1
    └── A1 (R~)
    >>> classical_ct_system.rules['R∧'].print_tree(classical_parser)
    A1 ∧ A2
    ├── A1 (R∧)
    └── A2 (R∧)

    The solver works as expected:

    >>> tree = classical_ct_system.solve_tree(classical_parser.parse('p and not q'))
    >>> tree.print_tree(classical_parser)
    p ∧ ~q
    ├── p (R∧)
    └── ~q (R∧)
        └── q (R~)
    >>> tree = classical_ct_system.solve_tree(classical_parser.parse('(p iff ~r) and ~~q'))
    >>> tree.print_tree(classical_parser)
    (p ↔ ~r) ∧ ~~q
    ├── p ↔ ~r (R∧)
    │   ├── p (R↔)
    │   └── ~r (R↔)
    │       └── r (R~)
    └── ~~q (R∧)
        └── ~q (R~)
    """
    fast_node_is_closed_enabled = False

    def __init__(self, language, solver=None):
        self.language = language
        self.closure_rules = []
        self.solver = solver
        self.rules = dict()

        # Automatically establish the rules based on the language
        for constant in language.constant_arity_dict:
            arity = language.constant_arity_dict[constant]
            initial_formula = [constant]
            initial_formula.extend([[f'A{num+1}'] for num in range(arity)])
            initial_formula = Formula(initial_formula)
            initial_node = TableauxNode(content=initial_formula, justification=None)
            for ar in range(arity):
                TableauxNode(content=Formula([f'A{ar+1}']), justification=f'R{constant}', parent=initial_node)
            self.rules[f'R{constant}'] = initial_node

    def node_is_closed(self, node):
        """In a constructive tree system a node is considered closed iff its content is an atomic wff

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.tableaux import classical_constructive_tree_system  # Identical to the above
        >>> tree = classical_constructive_tree_system.solve_tree(classical_parser.parse('~p'))
        >>> classical_constructive_tree_system.node_is_closed(tree.children[0])
        True
        >>> classical_constructive_tree_system.tree_is_closed(tree)
        True
        """
        if node.content.is_atomic and self.language.is_well_formed(node.content):
            return True
        return False

    def is_well_formed(self, formula):
        """Determines through tableaux methods if a formula is well-formed (if its constructive tree is closed)

        This method is actually an alias of `is_valid`

        Examples
        --------
        >>> from logics.classes.propositional import Formula
        >>> from logics.instances.propositional.tableaux import classical_constructive_tree_system
        >>> classical_constructive_tree_system.is_well_formed(Formula(['~', ['~', ['p']]]))
        True
        >>> classical_constructive_tree_system.is_well_formed(Formula(['~', '~', ['p']]))
        False
        """
        return self.is_valid(formula)
