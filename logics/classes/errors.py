from enum import IntEnum


class ErrorCode(IntEnum):
    """Enum to represent error codes. Advantages: more readable than a dict, JSON serializable variants (into ints)"""
    # Natural deduction
    ND_INCORRECT_PREMISE = 101
    ND_INCORRECT_SUPPOSITION = 102
    ND_INCORRECT_JUSTIFICATION = 103
    ND_RULE_INCORRECTLY_APPLIED = 104
    ND_INCORRECT_CONCLUSION = 105
    ND_INCORRECT_ON_STEPS = 106
    ND_CLOSED_SUPPOSITION = 107
    ND_NONARBITRARY_CONSTANT = 108

    # Tableaux
    TBL_PREMISE_NOT_BEGINNING = 201
    TBL_INCORRECT_PREMISE = 202
    TBL_RULE_NOT_APPLIED = 203
    TBL_RULE_INCORRECTLY_APPLIED = 204
    TBL_PREMISE_NOT_PRESENT = 205
    TBL_CONCLUSION_NOT_PRESENT = 206

    # Axiom systems
    AX_INCORRECT_PREMISE = 301
    AX_INCORRECT_AXIOM = 302
    AX_RULE_INCORRECTLY_APPLIED = 303
    AX_INCORRECT_JUSTIFICATION = 304
    AX_INCORRECT_CONCLUSION = 305

    # Sequent calculi
    SEQ_INCORRECT_PREMISE = 401
    SEQ_INCORRECT_AXIOM = 402
    SEQ_RULE_INCORRECTLY_APPLIED = 403

    @property
    def name(self):
        return error_names[self.value]

error_names = {
    # Natural deduction
    101: "ND: Incorrect premise step",
    102: "ND: Incorrect supposition handling",
    103: "ND: Incorrect justification",
    104: "ND: Rule incorrectly applied",
    105: "ND: Incorrect conclusion",
    106: "ND: Incorrect specification of 'on steps'",
    107: "ND: Using step in a closed supposition",
    108: "ND: Non-arbitrary constant",

    # Tableaux
    201: "TBL: Premise not at the beggining",
    202: "TBL: Incorrect premise",
    203: "TBL: Rule not applied to node",
    204: "TBL: Rule incorrectly applied",
    205: "TBL: Premise not present",
    206: "TBL: Conclusion not present",

    # Axiom systems
    301: "AX: Incorrect premise",
    302: "AX: Not an axiom instance",
    303: "AX: Rule incorrectly applied",
    304: "AX: Incorrect justification",
    305: "AX: Incorrect conclusion",

    # Sequent calculi
    401: "SEQ: Incorrect premise",
    402: "SEQ: Incorrect axiom",
    403: "SEQ: Rule incorrectly applied",
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
