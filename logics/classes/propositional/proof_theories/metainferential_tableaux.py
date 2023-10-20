from logics.classes.propositional import Formula, Inference
from .tableaux import TableauxNode, TableauxSystem


class MetainferentialTableauxStandard:
    """Class for a standard in metainferential tableaux (the second member of each node)

    Parameters
    ----------
    content: list or set or string
        Basic (level-0) indices are sets (e.g. ``{'1', 'i'}``), higher level standards are 2-lists of lower level ones,
        (e.g. ``[{'1', 'i'}, {'1'}]`` -aka *TS*). The formulation of a system's rules can include variables as standards
        (e.g. ``'X'``). See `MetainferentialTableauxStandard.standard_variables`
    bar: bool, optional
        Whether the index has a bar on top or not. Defaults to ``False``.

    Notes
    -----
    Note that the `__init__` method of will automatically turn sets and lists within a standard into standard. Thus,
    you can write ``MetainferentialTableauxStandard([{'1'}, {'1'}])`` instead of
    ``MetainferentialTableauxStandard([MetainferentialTableauxStandard({'1'}), MetainferentialTableauxStandard({'1'})])``

    Examples
    --------
    >>> from logics.classes.propositional.proof_theories.metainferential_tableaux import MetainferentialTableauxStandard
    >>> standard = MetainferentialTableauxStandard([[{'1', 'i'}, {'1'}], [{'1', 'i'}, {'1'}]], bar=True)
    >>> isinstance(standard, MetainferentialTableauxStandard)
    True
    >>> isinstance(standard.content[0], MetainferentialTableauxStandard)
    True
    >>> standard.content[0].bar  # bar status is not inherited to content sub-standards
    False
    """
    standard_variables = ['W', 'X', 'Y', 'Z']  # These should not coincide with the formula metavariables of the lang

    def __init__(self, content, bar=False):
        self.content = content
        self.bar = bar

        # At initialization, turn list elements into MetainferentialTableauxStandard
        if type(self.content) == list:
            for index in range(len(self.content)):
                argument = self.content[index]
                argument = self.__class__(argument)
                self.content[index] = argument

    @property
    def level(self):
        """Returns the level of a standard

        Examples
        --------
        >>> from logics.classes.propositional.proof_theories.metainferential_tableaux import MetainferentialTableauxStandard
        >>> standard = MetainferentialTableauxStandard([[{'1', 'i'}, {'1'}], [{'1', 'i'}, {'1'}]])  # TS/ST
        >>> standard.level
        2
        >>> standard.content[0].level  # TS
        1
        >>> standard.content[0].content[1].level  # S
        0

        Note that standard variables do not have a level, and will raise ``ValueError`` if their level is queried

        >>> MetainferentialTableauxStandard('X').level
        Traceback (most recent call last):
        ...
        ValueError: Variable standard can have any level
        >>> MetainferentialTableauxStandard(['X', {'1'}]).level
        Traceback (most recent call last):
        ...
        ValueError: Variable standard can have any level
        """
        # The standard is something like 'X'
        if self.content in self.standard_variables:
            raise ValueError('Variable standard can have any level')
        # Sets are standards of level 0
        elif type(self.content) == set:
            return 0
        # For lists -i.e. type [S1, S2], return the maximum level between S1 and S2 + 1
        return max(self.content[0].level, self.content[1].level) + 1

    def is_instance_of(self, idx2, subst_dict=None, return_subst_dict=False):
        """Determines whether a standard is an instance of another standard

        A MetainferentialTableauxStandard (`self`) is considered an instance of another (`idx2`) iff `self` and `node`
        have the same ``bar`` status, and one of the following occurs:

        * `idx2` is a standard variable (see ``MetainferentialTableauxStandard.standard_variables``). The default
          standard variables are ``'W', 'X', 'Y', 'Z'``
        * `idx2` is a set (i.e. a level-0 standard) and ``self.content == idx2.content``
        * `idx2` is a 2-list (a level-n>0 standard) and both members of `self.content` are instances of both members of
          `idx2.content`, respectively

        Examples
        --------
        >>> from logics.classes.propositional.proof_theories.metainferential_tableaux import MetainferentialTableauxStandard
        >>> simple_standard = MetainferentialTableauxStandard({'1', 'i'}, bar=False)  # T
        >>> simple_standard.is_instance_of(MetainferentialTableauxStandard('X'))
        True
        >>> simple_standard.is_instance_of(MetainferentialTableauxStandard({'1', 'i'}))
        True
        >>> simple_standard.is_instance_of(MetainferentialTableauxStandard({'1'}))
        False
        >>> simple_standard.is_instance_of(MetainferentialTableauxStandard(['X', 'Y']))
        False

        >>> complex_standard = MetainferentialTableauxStandard([{'1', 'i'}, {'1'}], bar=False)  # TS
        >>> complex_standard.is_instance_of(MetainferentialTableauxStandard('X'))
        True
        >>> complex_standard.is_instance_of(MetainferentialTableauxStandard(['X', 'Y']))
        True
        >>> complex_standard.is_instance_of(MetainferentialTableauxStandard(['X', 'X']))
        False
        >>> complex_standard.is_instance_of(MetainferentialTableauxStandard([{'1'}, {'1', 'i'}]))
        False
        """
        if subst_dict is None:
            subst_dict = dict()

        # if one index has bar and the other one does not, it is not an instance
        if self.bar != idx2.bar:
            if return_subst_dict:
                return False, subst_dict
            return False

        std1 = self.content
        std2 = idx2.content
        # The rule standard is a standard variable
        if std2 in self.standard_variables:
            if std2 in subst_dict:
                if return_subst_dict:
                    return subst_dict[std2] == self, subst_dict
                return subst_dict[std2] == self
            else:
                # Every standard is an instance of the standard variables
                if return_subst_dict:
                    subst_dict[std2] = self
                    return True, subst_dict
                return True

        # Complex index (e.g. [[{1, 'i'}, {'1'}], [{1}, {'1', 'i'}]], aka TS/ST)
        elif isinstance(std1, list) and isinstance(std2, list) and len(std2) == 2:
            # both std1 and std2 are MetainferentialTableauxStandard
            result, subst_dict = std1[0].is_instance_of(std2[0], subst_dict, True)
            if not result:
                if return_subst_dict:
                    return False, subst_dict
                return False
            result2, subst_dict = std1[1].is_instance_of(std2[1], subst_dict, True)
            if return_subst_dict:
                return result2, subst_dict
            return result2

        # Simple index, e.g. {'1', 'i'} or {'1'}
        elif isinstance(std1, set) and isinstance(std2, set):
            if return_subst_dict:
                return std1 == std2, subst_dict
            return std1 == std2

        if return_subst_dict:
            return False, subst_dict
        return False

    def __eq__(self, other):
        # A standard is equal to another if its content and bar are the same
        return self.content == other.content and self.bar == other.bar

    def __ne__(self, other):
        return not self == other

    def __repr__(self):
        # Bars are represented as a - sign at the beggining, so you may see things like -[-[{1}, -{1}], [{1}, {1}]]
        s = '-' if self.bar else ''
        return s + str(self.content)


class MetainferentialTableauxNode(TableauxNode):
    """Nodes for metainferential tableaux

    Parameters
    ----------
    content: logics.classes.propositional.Formula or logics.classes.propositional.Inference
        The formula or inference of the node
    index: logics.classes.propositional.proof_theories.metainferntial_tableaux.MetainferentialTableauxStandard
        The standard of the node
    justification: str, optional
        If the node is non-root, this parameter should contain the name of the rule by which it was obtained
    parent: logics.classes.propositional.proof_theories.TableauxNode, optional
        The parent node. The root node of a tableaux has None as parent (the default value).
    children: list of logics.classes.propositional.proof_theories.TableauxNode, optional
        A list of the children node. Also optional. If child nodes are specified with the `parent` attribute, there
        is no need to provide this (see the example below).

    Notes
    -----
    This subclasses ``logics.classes.propositional.proof_theories.tableaux.TableauxNode``, and overrides a few methods.
    The functioning is almost identical

    Examples
    --------
    >>> from logics.utils.parsers import classical_parser
    >>> from logics.instances.propositional.languages import classical_infinite_language as lang
    >>> from logics.classes.propositional.proof_theories.metainferential_tableaux import (
    ...     MetainferentialTableauxStandard, MetainferentialTableauxNode
    >>> )
    >>> S = MetainferentialTableauxStandard({'1'})
    >>> Sbar = MetainferentialTableauxStandard({'1'}, bar=True)
    >>> ST = MetainferentialTableauxStandard([{'1'}, {'1', 'i'}])
    >>> XY = MetainferentialTableauxStandard(['X', 'Y'])
    >>> XYbar = MetainferentialTableauxStandard(['X', 'Y'], bar=True)
    >>> node1 = MetainferentialTableauxNode(classical_parser.parse('p / q'), index=ST)
    >>> node2 = MetainferentialTableauxNode(classical_parser.parse('p / q'), index=XY)
    >>> node3 = MetainferentialTableauxNode(classical_parser.parse('p / q'), index=XYbar)
    >>> node1.is_instance_of(node2, lang)
    True
    >>> node1.is_instance_of(node3, lang)
    False
    >>> MetainferentialTableauxNode(classical_parser.parse('p'), index=S, parent=node1)
    >>> MetainferentialTableauxNode(classical_parser.parse('q'), index=S, parent=node1)
    >>> node1.print_tree(classical_parser)
    p / q, [{'1'}, {'1', 'i'}]
    ├── p, {'1'}
    └── q, {'1'}
    """
    def index_is_instance_of(self, idx2, subst_dict, return_subst_dict):
        # This method will update the subst dict (add things like 'X': {'1', 'i'})
        return self.index.is_instance_of(idx2, subst_dict, return_subst_dict)

    def content_is_instance_of(self, content2, language, subst_dict, return_subst_dict):
        # Nodes of different types (formula and inference) are never instances of each other
        if type(self.content) != type(content2):
            if return_subst_dict:
                return False, subst_dict
            return False

        # This is kind of a hack, it states any inference node's content is an instance of Γ / Δ (useful for inf0, inf1)
        # Since logics has no inference variables, we must treat Γ and Δ as formulae
        if (content2 == Inference(premises=[Formula(['Γ'])], conclusions=[Formula(['Δ'])]) and
                isinstance(self.content, Inference)):
            if return_subst_dict:
                subst_dict['Γ'] = self.content.premises
                subst_dict['Δ'] = self.content.conclusions
                return True, subst_dict
            return True
        return super().content_is_instance_of(content2, language, subst_dict, return_subst_dict)

    # def instantiate(self, language, subst_dict, instantiate_children=True, first_iteration=True):

        # See if we need this for is_correct_tree. Otherwise delete it.

        # Again, these are hacks to instantiate the rules inf0 and inf1
        # Instantiate nodes of the form Γ / Δ
        # if first_iteration and self.content == Inference(premises=[Formula(['Γ'])], conclusions=[Formula(['Δ'])]):
        #     # For the first node, replace Γ with the list of premises and Δ with the list of conclusions
        #     self_content_substitution = Inference(premises=subst_dict['Γ'], conclusions=subst_dict['Δ'])
        #     new_tableaux = self.__class__(content=self_content_substitution, index=self.index,
        #                                   justification=self.justification)
        #     for idx, premise in enumerate(subst_dict['Γ']):
        #         subst_dict[f'γ{idx}'] = premise
        #     for idx, conclusion in enumerate(subst_dict['Δ']):
        #         subst_dict[f'δ{idx}'] = conclusion
        #
        #     for child_node in self.children:
        #         new_child = child_node.instantiate(language, subst_dict, instantiate_children, first_iteration=False)
        #         new_child.parent = new_tableaux
        #
        #     return new_tableaux
        #
        # # Instantiate nodes of the form γ1, ...
        # elif self.content[0] in ('γ', 'δ'):
        #     if self.content in subst_dict:
        #         new_tableaux = self.__class__(content=subst_dict[self.content], index=self.index,
        #                                       justification=self.justification)
        #         for child_node in self.children:
        #             new_child = child_node.instantiate(language, subst_dict, instantiate_children,
        #                                                first_iteration=False)
        #             if new_child is not None:
        #                 new_child.parent = new_tableaux
        #         return new_tableaux
        #     else:  # if you get γ5 but the actual inference only has 2 premises
        #         return None
        # else:
        #     return super().instantiate(language, subst_dict, instantiate_children, first_iteration)


class MetainferentialTableauxSystem(TableauxSystem):
    """Class for metainferential tableaux systems

    Takes an extra parameter ``base_indexes``, which should be a set. This defines what will be the valid standards.
    E.g. if ``base_indexes`` is ``{'1', 'i', '0'}`` then ``[{'1', 'i'}, {'1'}]`` will be a valid standard but
    ``[{'1', 'n'}, {'1'}]`` will not.

    Notes
    -----
    * This subclasses ``logics.classes.propositional.proof_theories.tableaux.TableauxSystem``,
      and overrides a few methods. The functioning is almost identical
    * Also note that the ``is_correct_tree`` **method has not been implemented yet for this class.**
    """
    fast_node_is_closed_enabled = True

    def __init__(self, base_indexes, language, rules, closure_rules, solver=None):
        self.base_indexes = base_indexes
        super().__init__(language, rules, closure_rules, solver)

    @staticmethod
    def _fast_node_is_closed(node):
        for node in node.path:
            # if it finds the empty set at the right, close
            if node.index.content == set():
                return True
            # If it finds the empty inference with no bar, close
            if (type(node.content) == Inference and
                    len(node.content.premises) == 0 and len(node.content.conclusions) == 0 and not node.index.bar):
                return True
        return False

    def _rule_is_applicable_additional_conditions(self, node, subst_dict, rule_name):
        # For the inf0 and inf1 rules, check that the level of the inference and of the standard is the same
        if rule_name == 'inf0' or rule_name == 'inf1':
            if type(node.content) != Inference or node.content.level != node.index.level:
                return False

        # The lowering and lifting rules apply to inferences
        # (we have not implemented these rules yet but I leave this here just in case we do it)
        elif (rule_name == 'lowering' or rule_name == 'lifting') and type(node.content) != Inference:
            # Here we would need to check that for one the level is higher and for the other lower
            return False

        else:
            # For all the other rules, check that the standard is of level 1
            if node.index.level != 0:
                return False
            # The singleton rule is only applicable if the standard has two or more values
            if rule_name == "singleton" and len(node.index.content) < 2:
                return False
            # The intersection rule is applicalbe only if both standards are of level 0
            # And none of the standards is a subset of the other (i.e., none is the empty set)
            if rule_name == "intersection":
                if (subst_dict['X'].level != 0 or
                        subst_dict['X'].content.issubset(subst_dict['Y'].content) or
                        subst_dict['Y'].content.issubset(subst_dict['X'].content)):
                    return False

        return True

    def is_correct_tree(self, tree, inference=None, return_error_list=False, exit_on_first_error=False, parser=None):
        raise NotImplementedError()
