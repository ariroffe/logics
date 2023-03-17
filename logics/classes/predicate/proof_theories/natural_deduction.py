from copy import deepcopy

from logics.classes.errors import ErrorCode, CorrectionError
from logics.classes.propositional.proof_theories.natural_deduction import (
    NaturalDeductionRule,
    NaturalDeductionSystem,
    NaturalDeductionStep,  # To have it available as an import from here
)


class PredicateNaturalDeductionRule(NaturalDeductionRule):
    """The differences between this class and the propositional one stem only from the rules requiring that a given
    constant is arbitrary up to that point in the derivation

    Examples
    --------
    >>> from logics.classes.predicate import PredicateFormula as Formula
    >>> from logics.classes.predicate.proof_theories.natural_deduction import NaturalDeductionStep, PredicateNaturalDeductionRule
    >>> univ_intro = PredicateNaturalDeductionRule([
    ...     '(...)',
    ...     NaturalDeductionStep(Formula(['[α/χ]A']), open_suppositions=[]),
    ...     '(...)',
    ...     NaturalDeductionStep(Formula(['∀', 'x', ['A']]), 'I∀', [0], open_suppositions=[])
    ... ], arbitrary_cts=['α'])
    >>> univ_intro.arbitrary_cts
    ['α']
    >>> # The rest works the same than in the propositional case
    >>> univ_intro.premises
    [['[α/χ]A']]
    >>> univ_intro.index(NaturalDeductionStep(Formula(['∀', 'x', ['A']]), open_suppositions=[]))
    1
    """
    def __init__(self, rule, arbitrary_cts=None):
        self.arbitrary_cts = arbitrary_cts
        super().__init__(rule)


class PredicateNaturalDeductionSystem(NaturalDeductionSystem):
    """The differences between this class and the propositional one stem from rules with arbitrary constants
    and rules with formulae of the form [α/χ]A. The user interface is the same, though.

    Examples
    --------
    >>> from logics.utils.parsers.predicate_parser import classical_predicate_parser as parser
    >>> from logics.instances.predicate.natural_deduction import predicate_classical_natural_deduction_system as nd_system
    >>> deriv = parser.parse_derivation('''
    ...     ∃x R(x, a); premise; []; []
    ...     ∃y ∃x R(x, y); I∃; [0]; []
    ... ''', natural_deduction=True)
    >>> nd_system.is_correct_application(deriv, 1, nd_system.rules['I∃'])
    True
    >>> deriv = parser.parse_derivation('''
    ...     P(a); premise; []; []
    ...     ∀x P(x); I∀; [0]; []
    ... ''', natural_deduction=True)
    >>> rule = nd_system.substitute_rule(deriv, 1, nd_system.rules['I∀'])  # to get a specific instance of the rule
    >>> is_correct, error = nd_system.check_arbitrary_constants(deriv, 1, rule)
    >>> is_correct
    False
    >>> error
    "Constant 'a' is not arbitrary"
    >>> deriv = parser.parse_derivation('''
    ...     ∃x R(x, x); premise; []; []
    ...     R(a, a); supposition; []; [1]
    ...     ∃y R(y, y); I∃; [1]; [1]
    ...     R(a, a) → ∃y R(y, y); I→; [1,2]; []
    ...     ∃y R(y, y); E∃; [0, 3]; []
    ... ''', natural_deduction=True)
    >>> nd_system.is_correct_derivation(deriv)
    True

    Notes
    -----
    The class is hardcoded to work with the usual quantifier rules. If you want to give it different ones,
    you may need to adjust the code
    """
    def substitute_rule(self, derivation, step, rule):
        """Gets rid of things of form [α/χ] in the rules, by vsubstituting the χ's for α's and returning the modified
        rule.
        """
        # Implementation is hardwired for the classical quantifier rules. Later, we might want something more general
        step_conclusion = derivation[step]

        # For both introduction rules we need to begin by looking at the conclusion
        if step_conclusion.justification == 'I∀' or step_conclusion.justification == 'I∃':
            # In both these cases we need to begin by looking at the conclusion
            instance, subst_dict = step_conclusion.content.is_instance_of(rule[-1].content, self.language,
                                                                          return_subst_dict=True)
            if not instance:
                raise ValueError("Conclusion not an instance of the rule's conclusion")

            # Suppose the inference is Rab / ∃y Ryb
            # The rule states [α/χ]A / ∃χ A
            # The subst dict should now contain something like {'χ': 'y', 'A': ['R', 'y', 'b']}
            new_rule_conclusion = rule[-1].content.instantiate(self.language, subst_dict)
            # the new rule conclusion is now something like ['∃', 'y' ['R', 'y', 'b']]

            # For the rule premise, we must now take A from there, and vsubstitute y for α
            new_rule_premise = new_rule_conclusion[-1].vsubstitute(subst_dict['χ'], 'α')
            # in the above example, the rule premise now says ['R', 'α', 'b']

            new_rule = deepcopy(rule)
            new_rule[1].content = new_rule_premise
            new_rule[-1].content = new_rule_conclusion
            return new_rule

        elif step_conclusion.justification == "E∀":
            # Here we need to begin by looking at the premise
            step_premise = derivation[step_conclusion.on_steps[0]]
            instance, subst_dict = step_premise.content.is_instance_of(rule[1].content, self.language,
                                                                       return_subst_dict=True)
            if not instance:
                raise ValueError("On step formula not an instance of the rule's premise")

            # Suppose the inference is ∀y Ryb / Rab
            # The rule states ∀χ A / [α/χ]A
            # The subst dict should now contain something like {'χ': 'y', 'A': ['R', 'y', 'b']}
            new_rule_premise = rule[1].content.instantiate(self.language, subst_dict)
            # the new rule premise is now something like ['∀', 'y' ['R', 'y', 'b']]

            new_rule_conclusion = new_rule_premise[-1].vsubstitute(subst_dict['χ'], 'α')
            # in the above example, the rule conclusion now says ['R', 'α', 'b']

            new_rule = deepcopy(rule)
            new_rule[1].content = new_rule_premise
            new_rule[-1].content = new_rule_conclusion
            return new_rule

        elif step_conclusion.justification == "E∃":
            # This rule has 3 steps, we need to modify the first and second
            step_first_premise = derivation[step_conclusion.on_steps[0]]
            instance, subst_dict = step_first_premise.content.is_instance_of(rule[1].content, self.language,
                                                                             return_subst_dict=True)
            if not instance:
                raise ValueError("On step formula not an instance of the rule's first premise")

            # Suppose the inference is ∃y Ryb, Rab → Pc / Pc
            # The rule states ∃χ A, [α/χ]A → B / B
            # The subst dict should now contain something like {'χ': 'y', 'A': ['R', 'y', 'b']}
            new_rule_first_premise = rule[1].content.instantiate(self.language, subst_dict)
            # the new rule premise is now something like ['∃', 'y' ['R', 'y', 'b']]

            # What we need to modify now is not the conclusion of the rule, but the antecedent of the second premise
            new_rule_second_premise = rule[3].content
            new_rule_second_premise[1] = new_rule_first_premise[-1].vsubstitute(subst_dict['χ'], 'α')
            # in the above example, the rule's second premise now says ['→', ['R', 'α', 'b'], 'B']

            new_rule = deepcopy(rule)
            new_rule[1].content = new_rule_first_premise
            new_rule[3].content = new_rule_second_premise
            return new_rule

        else:
            # If none of the above rules, just return the original
            return rule

    def check_arbitrary_constants(self, derivation, step, rule):
        """For a rule that requires an arbitrary constant, determines what that constant is and determines if it is so

        Returns
        -------
        tuple (bool, ``logics.classes.errors.CorrectionError`` or None)

        Raises
        ------
        NotImplementedError: if the rule name is anything other than "I∀" and "E∃"

        Notes
        -----
        Requires the modified version of the rule (by ``substitute_rule``); that is, one that does not contain [α/χ]
        """
        if rule.arbitrary_cts is None:
            return True, None

        # rule is the modified version (by the above method), it does not contain things of the form [α/χ]
        # but does contain things of the form α. We also know by now that, except for this, the application is correct

        if rule[-1].justification == "I∀":
            # The modified rule has something of the form, e.g., ['R', 'α', 'b'] as premise
            # We need to find out what α is
            step_premise = derivation[derivation[step].on_steps[0]].content
            instance, subst_dict = step_premise.is_instance_of(rule[1].content, self.language, return_subst_dict=True)
            arbitrary_constant = subst_dict['α']
            possible_error = f"Constant '{arbitrary_constant}' is not arbitrary"

        elif rule[-1].justification == "E∃":
            # Now the constant that we need to check is present as antecedent of the second premise of the modified rule
            step_premise2 = derivation[derivation[step].on_steps[1]].content
            instance, subst_dict = step_premise2.is_instance_of(rule[3].content, self.language, return_subst_dict=True)
            arbitrary_constant = subst_dict['α']
            possible_error = f"Constant '{arbitrary_constant}' is not arbitrary"

            # In this case, we also need to check that the existential does not contain the constant as well
            if derivation[derivation[step].on_steps[0]].content.contains_string(arbitrary_constant):
                return False, CorrectionError(code=ErrorCode.ND_NONARBITRARY_CONSTANT, index=step,
                                              description=possible_error)
        else:
            raise NotImplementedError("No arbitrary constant checking for the rule given yet")


        # 1) Check that arbitrary_constant is not in the formula at the current step
        if derivation[step].content.contains_string(arbitrary_constant):
            return False, CorrectionError(code=ErrorCode.ND_NONARBITRARY_CONSTANT, index=step,
                                          description=possible_error)

        open_sups = derivation[step].open_suppositions
        for step2_idx in range(step):  # Go up to (but not including) the current step of the derivation
            step2 = derivation[step2_idx]

            # 2) Check that arbitrary_constant it is not in a premise
            if step2.justification == "premise" and step2.content.contains_string(arbitrary_constant):
                return False, CorrectionError(code=ErrorCode.ND_NONARBITRARY_CONSTANT, index=step,
                                              description=possible_error)

            # 3) Check that arbitrary_constant it is not in an open supposition
            if step2.justification == "supposition" and step2_idx in open_sups and \
                    step2.content.contains_string(arbitrary_constant):
                return False, CorrectionError(code=ErrorCode.ND_NONARBITRARY_CONSTANT, index=step,
                                              description=possible_error)

        return True, None

    def is_correct_application(self, derivation, step, rule, return_error=False):
        # Get rid of the [a/x]A sorts of things in the rules by doing the replacement directly
        try:
            rule = self.substitute_rule(derivation, step, rule)
        except ValueError as e:
            if not return_error:
                return False
            return False, CorrectionError(code=ErrorCode.ND_RULE_INCORRECTLY_APPLIED, index=step, description=str(e))

        # Super method
        correct, error = super().is_correct_application(derivation, step, rule, return_error=True)
        if not correct:
            if not return_error:
                return False
            return False, error

        # Check if the constants are arbitrary
        correct, error = self.check_arbitrary_constants(derivation, step, rule)
        if not return_error:
            return correct
        return correct, error
