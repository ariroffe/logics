from copy import deepcopy

from logics.classes.propositional import Formula, Inference
from logics.classes.predicate import PredicateFormula
from logics.classes.predicate.proof_theories import Derivation
from logics.classes.propositional.proof_theories.natural_deduction import NaturalDeductionRule
from logics.classes.predicate.proof_theories.natural_deduction import PredicateNaturalDeductionRule


def upgrade_to_predicate_formula(formula):
    """Upgrades a Formula to a PredicateFormula NOT in-place, returns a new object"""
    if formula.is_atomic:
        return PredicateFormula(formula)
    for subformula_idx in range(len(formula)):
        if type(formula[subformula_idx]) == Formula:
            formula[subformula_idx] = upgrade_to_predicate_formula(formula[subformula_idx])
    return PredicateFormula(formula)


def upgrade_inference(inference):
    """Upgrades the inference NOT in-place. Turns Formula in the premises and conclusions to PredicateFormula"""
    new_inference = Inference(premises=[], conclusions=[])
    for premise in inference.premises:
        new_inference.premises.append(upgrade_to_predicate_formula(premise))
    for conclusion in inference.conclusions:
        new_inference.conclusions.append(upgrade_to_predicate_formula(conclusion))
    return new_inference


def upgrade_derivation(derivation):
    """Upgrades the derivation NOT in-place. Turns Formula in the steps.content to PredicateFormula"""
    new_derivation = Derivation([])
    if type(derivation) == NaturalDeductionRule:
        new_derivation = PredicateNaturalDeductionRule([])

    for step in derivation:
        if step == "(...)":  # for natural deduction rules
            new_derivation.append(step)
        else:
            new_step = deepcopy(step)
            new_step.content = upgrade_to_predicate_formula(new_step.content)
            new_derivation.append(new_step)
    return new_derivation
