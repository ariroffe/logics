from copy import deepcopy

from logics.classes.propositional.proof_theories.natural_deduction import (
    NaturalDeductionRule,
    NaturalDeductionSystem,
    NaturalDeductionStep as PredicateNaturalDeductionStep,  # To have it available as an import from here
)


class PredicateNaturalDeductionRule(NaturalDeductionRule):
    """The differences between this class and the propositional one stem only from the rules requiring that a given
    constant is arbitrary up to that point in the derivation

    Examples
    --------
    >>> from logics.classes.predicate import PredicateFormula as Formula
    >>> from logics.classes.predicate.proof_theories.natural_deduction import PredicateNaturalDeductionStep, PredicateNaturalDeductionRule
    >>> univ_intro = PredicateNaturalDeductionRule([
    ...     '(...)',
    ...     PredicateNaturalDeductionStep(Formula(['[α/x]A']), 'I∨1', [0], open_suppositions=[]),
    ...     '(...)',
    ...     PredicateNaturalDeductionStep(Formula(['∀', 'x', ['A']]), open_suppositions=[])
    ... ], arbitrary_cts=['α'])
    >>> univ_intro.arbitrary_cts
    ['α']
    >>> # The rest works the same than in the propositional case
    >>> univ_intro.premises
    [['[α/x]A']]
    >>> univ_intro.index(PredicateNaturalDeductionStep(Formula(['∀', 'x', ['A']]), open_suppositions=[]))
    1
    """
    def __init__(self, rule, arbitrary_cts=None):
        self.arbitrary_cts = arbitrary_cts
        super().__init__(rule)


class PredicateNaturalDeductionSystem(NaturalDeductionSystem):
    """The differences between this class and the propositional one stem from rules with given constants as arbitrary
    up to that point in the derivation, and things like [a/x]A
    """
    def substitute_rule(self, derivation, step, rule):
        """Gets rid of things of form [α/χ] in the rules, by vsubstituting the χ's for α's and returning the modified
        rule.
        """
        # Implementation is hardwired for the classical quantifier rules. Later, we might want something more general
        step_conclusion = derivation[step]

        # For both introduction rules we need to begin by looking at the conclusion
        if step_conclusion.justification == 'I∀' or step_conclusion.justification == 'I∃':
            instance, subst_dict = step_conclusion.content.is_instance_of(rule[-1].content, self.language,
                                                                          return_subst_dict=True)
            if not instance:
                raise ValueError("Conclusion not an instance of the rule's conclusion")

            # The subst dict should now contain something like {'χ': 'y', 'A': ['R', 'y', 'x']}
            new_rule_conclusion = deepcopy(rule[-1].content)
            new_rule_conclusion[-1] = subst_dict['A']
            new_rule_conclusion[1] = subst_dict['χ']
            # the new rule conclusion is now something like ['∀', 'y' ['R', 'y', 'x']]

            # For the rule premise, we must now take A from there, and vsubstitute χ for α
            new_rule_premise = new_rule_conclusion[-1].vsubstitute(subst_dict['χ'], 'α')
            # in the above example, the rule premise now says ['R', 'α', 'y']

            new_rule = deepcopy(rule)
            new_rule[1].content = new_rule_premise
            new_rule[-1].content = new_rule_conclusion
            return new_rule

        elif step_conclusion.justification == "E∀":
            # todo DO THIS
            new_rule = deepcopy(rule)
            return new_rule

        elif step_conclusion.justification == "E∃":
            # todo DO THIS
            new_rule = deepcopy(rule)
            return new_rule

        else:
            # If none of the above rules, just return the original
            return rule

    def is_correct_application(self, derivation, step, rule, return_error=False):
        rule = self.substitute_rule(derivation, step, rule)
        # todo Somewhere around here put a new method to check if the constant is arbitrary
        return super().is_correct_application(derivation, step, rule, return_error=False)
