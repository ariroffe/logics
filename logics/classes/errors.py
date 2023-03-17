from enum import IntEnum


class ErrorCode(IntEnum):
    """Enum to represent error codes. Advantages: more readable than a dict, JSON serializable variants (into ints)"""
    # General
    GEN_MALFORMED_FORMULA = 101
    GEN_MALFORMED_INFERENCE = 102

    # Natural deduction
    ND_INCORRECT_PREMISE = 201
    ND_INCORRECT_SUPPOSITION = 202
    ND_INCORRECT_JUSTIFICATION = 203
    ND_RULE_INCORRECTLY_APPLIED = 204
    ND_INCORRECT_CONCLUSION = 205
    ND_INCORRECT_ON_STEPS = 206
    ND_CLOSED_SUPPOSITION = 207
    ND_NONARBITRARY_CONSTANT = 208

    # Tableaux
    TBL_PREMISE_NOT_BEGINNING = 301
    TBL_INCORRECT_PREMISE = 302
    TBL_RULE_NOT_APPLIED = 303
    TBL_RULE_INCORRECTLY_APPLIED = 304
    TBL_PREMISE_NOT_PRESENT = 305
    TBL_CONCLUSION_NOT_PRESENT = 306

    # Axiom systems
    AX_INCORRECT_PREMISE = 401
    AX_INCORRECT_AXIOM = 402
    AX_RULE_INCORRECTLY_APPLIED = 403
    AX_INCORRECT_JUSTIFICATION = 404
    AX_INCORRECT_CONCLUSION = 405

    # Sequent calculi
    SEQ_INCORRECT_PREMISE = 501
    SEQ_INCORRECT_AXIOM = 502
    SEQ_RULE_INCORRECTLY_APPLIED = 503

    @property
    def name(self):
        return error_names[self.value]

error_names = {
    # General
    101: "GEN: Malformed formula",
    102: "GEN: Malformed inference",

    # Natural deduction
    201: "ND: Incorrect premise step",
    202: "ND: Incorrect supposition handling",
    203: "ND: Incorrect justification",
    204: "ND: Rule incorrectly applied",
    205: "ND: Incorrect conclusion",
    206: "ND: Incorrect specification of 'on steps'",
    207: "ND: Using step in a closed supposition",
    208: "ND: Non-arbitrary constant",

    # Tableaux
    301: "TBL: Premise not at the beggining",
    302: "TBL: Incorrect premise",
    303: "TBL: Rule not applied to node",
    304: "TBL: Rule incorrectly applied",
    305: "TBL: Premise not present",
    306: "TBL: Conclusion not present",

    # Axiom systems
    401: "AX: Incorrect premise",
    402: "AX: Not an axiom instance",
    403: "AX: Rule incorrectly applied",
    404: "AX: Incorrect justification",
    405: "AX: Incorrect conclusion",

    # Sequent calculi
    501: "SEQ: Incorrect premise",
    502: "SEQ: Incorrect axiom",
    503: "SEQ: Rule incorrectly applied",
}


class CorrectionError:
    def __init__(self, code:ErrorCode, description:str, index=None):
        """This class is just to group data in `is_correct_xxx` methods. In Taut, it facilitates building statistics

        json serializable with ``json.dumps(instance.__dict__)``
        """
        self.code = code
        self.index = index
        self.description = description

    def __eq__(self, other):
        return self.code == other.code and self.index == other.index and self.description == other.description

    def __ne__(self, other):
        return not self.__eq__(other)

    def __repr__(self):
        if self.index is not None:
            return f"{self.index}: {self.description}"
        return self.description
