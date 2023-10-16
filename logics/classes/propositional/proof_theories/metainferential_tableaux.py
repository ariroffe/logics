from .tableaux import TableauxNode


class MetainferentialTableauxStandard:
    """
    todo Document class and add to the docs/ folder
    """
    standard_variables = ['W', 'X', 'Y', 'Z']

    def __init__(self, content, bar=False):
        self.content = content
        self.bar = bar

        # At initialization, turn list elements into MetainferentialTableauxStandard
        if type(self.content) == list:
            for index in range(len(self.content)):
                argument = self.content[index]
                argument = self.__class__(argument)
                self.content[index] = argument

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
                    return subst_dict[std2] == std1, subst_dict
                return subst_dict[std2] == std1
            else:
                # Every standard is an instance of the standard variables
                if return_subst_dict:
                    subst_dict[std2] = std1
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
    def index_is_instance_of(self, idx2):
        return self.index.is_instance_of(idx2)
