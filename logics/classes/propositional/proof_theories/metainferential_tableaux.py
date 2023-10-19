from logics.classes.propositional import Formula, Inference
from .tableaux import TableauxNode, TableauxSystem


class MetainferentialTableauxStandard:
    """
    todo Document class and add to the docs/ folder
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
        # The standard is something like 'X'
        if self.content in self.standard_variables:
            raise ValueError('Variable standard can have any level')
        # Sets are standards of level 0
        elif type(self.content) == set:
            return 0
        # For lists -i.e. type [S1, S2], return the maximum level between S1 and S2 + 1
        return max(self.content[0].level, self.content[1].level) + 1

    def is_instance_of(self, idx2, subst_dict=None, return_subst_dict=False):
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

    def instantiate(self, language, subst_dict, instantiate_children=True, first_iteration=True):
        # Again, these are hacks to instantiate the rules inf0 and inf1
        # Instantiate nodes of the form Γ / Δ
        if first_iteration and self.content == Inference(premises=[Formula(['Γ'])], conclusions=[Formula(['Δ'])]):
            # For the first node, replace Γ with the list of premises and Δ with the list of conclusions
            self_content_substitution = Inference(premises=subst_dict['Γ'], conclusions=subst_dict['Δ'])
            new_tableaux = self.__class__(content=self_content_substitution, index=self.index,
                                          justification=self.justification)
            for idx, premise in enumerate(subst_dict['Γ']):
                subst_dict[f'γ{idx}'] = premise
            for idx, conclusion in enumerate(subst_dict['Δ']):
                subst_dict[f'δ{idx}'] = conclusion

            for child_node in self.children:
                new_child = child_node.instantiate(language, subst_dict, instantiate_children, first_iteration=False)
                new_child.parent = new_tableaux

            return new_tableaux

        # Instantiate nodes of the form γ1, ...
        elif self.content[0] in ('γ', 'δ'):
            if self.content in subst_dict:
                new_tableaux = self.__class__(content=subst_dict[self.content], index=self.index,
                                              justification=self.justification)
                for child_node in self.children:
                    new_child = child_node.instantiate(language, subst_dict, instantiate_children,
                                                       first_iteration=False)
                    if new_child is not None:
                        new_child.parent = new_tableaux
                return new_tableaux
            else:  # if you get γ5 but the actual inference only has 2 premises
                return None
        else:
            return super().instantiate(language, subst_dict, instantiate_children, first_iteration)


class MetainferentialTableauxSystem(TableauxSystem):
    """
    Document the base_indexes param
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

    def rule_is_applicable(self, node, rule_name, return_subst_dict=False):
        """Basically applies the super rule, but checks a few additional things"""
        # Apply the super rule
        applicable, subst_dict = super().rule_is_applicable(node, rule_name, return_subst_dict=True)
        if not applicable:
            if not return_subst_dict:
                return False
            return False, subst_dict

        # For the inf0 and inf1 rules, check that the level of the inference and of the standard is the same
        if rule_name == 'inf0' or rule_name == 'inf1':
            if type(node.content) != Inference or node.content.level != node.index.level:
                if not return_subst_dict:
                    return False
                return False, subst_dict

        # The lowering and lifting rules apply to inferences
        # (we have not implemented these rules yet but I leave this here just in case we do it)
        elif (rule_name == 'lowering' or rule_name == 'lifting') and type(node.content) != Inference:
            if not return_subst_dict:
                return False
            return False, subst_dict

        else:
            # For all the other rules, check that the standard is of level 1
            if node.index.level != 0:
                if not return_subst_dict:
                    return False
                return False, subst_dict
            # The singleton rule is only applicable if the standard has two or more values
            if rule_name == "singleton" and len(node.index.content) < 2:
                if not return_subst_dict:
                    return False
                return False, subst_dict
            # The intersection rule is applicalbe only if both standards are of level 0
            # And none of the standards is a subset of the other (i.e., none is the empty set)
            if rule_name == "intersection":
                if (subst_dict['X'].level != 0 or
                        subst_dict['X'].content.issubset(subst_dict['Y'].content) or
                        subst_dict['Y'].content.issubset(subst_dict['X'].content)):
                    if not return_subst_dict:
                        return False
                    return False, subst_dict

        if return_subst_dict:
            return applicable, subst_dict
        return applicable
