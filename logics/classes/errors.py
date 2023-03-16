from enum import IntEnum


class ErrorCode(IntEnum):
    """Enum to represent error codes. Advantages: more readable than a dict, JSON serializable variants (into ints)"""
    # Natural deduction
    ND_INCORRECT_PREMISE = 1
    ND_INCORRECT_SUPPOSITION = 2
    ND_INCORRECT_JUSTIFICATION = 3
    ND_RULE_INCORRECTLY_APPLIED = 4
    ND_INCORRECT_CONCLUSION = 5
    ND_INCORRECT_ON_STEPS = 6
    ND_CLOSED_SUPPOSITION = 7
    ND_NONARBITRARY_CONSTANT = 8

    # Tableaux
    TBL_PREMISE_NOT_BEGINNING = 9
    TBL_INCORRECT_PREMISE = 10
    TBL_RULE_NOT_APPLIED = 11
    TBL_RULE_INCORRECTLY_APPLIED = 12
    TBL_PREMISE_NOT_PRESENT = 13
    TBL_CONCLUSION_NOT_PRESENT = 14

    @property
    def name(self):
        return error_names[self.value]

error_names = {
    # Natural deduction
    1: "ND: Incorrect premise step",
    2: "ND: Incorrect supposition handling",
    3: "ND: Incorrect justification",
    4: "ND: Rule incorrectly applied",
    5: "ND: Incorrect conclusion",
    6: "ND: Incorrect specification of 'on steps'",
    7: "ND: Using step in a closed supposition",
    8: "ND: Non-arbitrary constant",

    # Tableaux
    9: "TBL: Premise not at the beggining",
    10: "TBL: Incorrect premise",
    11: "TBL: Rule not applied to node",
    12: "TBL: Rule incorrectly applied",
    13: "TBL: Premise not present",
    14: "TBL: Conclusion not present",
}


class CorrectionError:
    def __init__(self, code:ErrorCode, category:str, description:str, index=None):
        """This class is just to group data in `is_correct_xxx` methods. In Taut, it facilitates building statistics

        json serializable with ``json.dumps(instance.__dict__)``
        """
        self.code = code
        self.category = category
        self.index = index
        self.description = description

    def __eq__(self, other):
        return self.code == other.code and self.category == other.category and self.index == other.index and \
            self.description == other.description

    def __ne__(self, other):
        return not self.__eq__(other)

    def __repr__(self):
        if self.index is not None:
            return f"{self.index}: {self.description}"
        return self.description
