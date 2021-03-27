from copy import deepcopy
try:
    # For importing in the frontend
    from utils_models import substitute
    from utils_formula_parser import FOL_individual_constants
except ModuleNotFoundError:
    # For importing in the backend
    from exercises.templates.exercises.utils_models import substitute
    from exercises.templates.exercises.utils_formula_parser import FOL_individual_constants


# ----------------------------------------------------------------------------------------------------------------------
# LOGIC CLASS


class Logic:

    def __init__(self, short_name, values, premise_designated, conclusion_designated, false_values, true_values,
                 logical_constants, truth_functions, inference_rules, quantifiers=None, parsed_constants=None):
        """Values, designated and false_values are lists (designated and f_v are subsets of values)
        logical_constants is a dict. Keys are arities (integers), and values are sets of strings
        quantifiers is a list of strings
        truth_functions is a dict, keys are the logical constants and quantifiers, values are functions
        parsed_constants is optional, says how the constants look when parsed
        """

        if not set(premise_designated) <= set(values) or not set(conclusion_designated) <= set(values):
            raise ValueError('Designated values must be a subset of the entire set of truth values')
        if not set(false_values) <= set(values):
            raise ValueError('False values must be a subset of the entire set of truth values')

        self.short_name = short_name
        self.values = values
        self.false_values = false_values
        self.true_values = true_values
        self.premise_designated_values = premise_designated
        self.conclusion_designated_values = conclusion_designated
        self.dict_logical_constants = logical_constants
        self.truth_functions = truth_functions
        self.inference_rules = inference_rules

        if quantifiers is None:
            self.quantifiers = list()
        else:
            self.quantifiers = quantifiers

        if parsed_constants is None:
            self.parsed_constants = dict()
        else:
            self.parsed_constants = parsed_constants

    def constants(self, arity=None):
        """Returns the constants of a given arity"""
        if arity is None:
            ctes = list()
            for x in self.dict_logical_constants:
                ctes.extend(self.dict_logical_constants[x])
            return ctes
        else:
            if arity in self.dict_logical_constants:
                return self.dict_logical_constants[arity]
            else:
                return list()

    def t_function(self, constant, *args):
        return self.truth_functions[constant](*args)

    def __str__(self):
        if self.short_name == 'CL':
            return 'Classical'
        if self.short_name == 'L3':
            return 'Ł3'
        return self.short_name


# ----------------------------------------------------------------------------------------------------------------------
# PROPOSITIONAL LOGIC INSTANCES (FOR TRUTH TABLES)

# CLASSICAL LOGIC

def classical_negation(val):
    if val == '1':
        return '0'
    elif val == '0':
        return '1'
def classical_conjunction(val1, val2):
    if val1 == '0' or val2 == '0':
        return '0'
    return '1'
def classical_disjunction(val1, val2):
    if val1 == '1' or val2 == '1':
        return '1'
    return '0'
def classical_conditional(val1, val2):
    return classical_disjunction(classical_negation(val1), val2)  # p -> q is defined as ¬p v q
def classical_biconditional(val1, val2):  # also defined (p <--> q) = (p --> q) & (q --> p)
    return classical_conjunction(classical_conditional(val1, val2), classical_conditional(val2, val1))

classical_connectives = {1: ['¬'], 2: ['˅', '˄', '→', '↔']}
classical_t_functions = {"¬": classical_negation,
                         "˅": classical_disjunction,
                         "˄": classical_conjunction,
                         "→": classical_conditional,
                         "↔": classical_biconditional}
parsed_classical_constants = {"not": "¬",
                              "or": "˅",
                              "&": "˄",
                              "and": "˄",
                              "then": "→",
                              "iff": "↔",
                              "all": "∀",
                              "V": "∀",
                              "exists": "∃",
                              "E": "∃"}
quants=['∃', '∀']

Classical = Logic(short_name="CL", values=['0', '1'], premise_designated=['1'], conclusion_designated=['1'],
                  false_values=['0'], true_values = ['1'],
                  logical_constants=classical_connectives,
                  truth_functions=classical_t_functions, inference_rules=dict(), quantifiers=quants,
                  parsed_constants=parsed_classical_constants)


# ------------------------------------
# K3, L3 and LP

trivalued_values = ['0', 'i', '1']
def k3_negation(val1):
    if val1 == '0':
        return '1'
    if val1 == '1':
        return '0'
    if val1 == 'i':
        return 'i'
def k3_disjunction(val1, val2):
    if val1 == '1' or val2 == '1':
        return '1'
    elif val1 == 'i' or val2=='i':
        return 'i'
    else:
        return '0'
def k3_conjunction(val1, val2):
    if val1 == '0' or val2 == '0':
        return '0'
    elif val1 == 'i' or val2 == 'i':
        return 'i'
    else:
        return '1'
def k3_conditional(val1, val2):
    return k3_disjunction(k3_negation(val1), val2)  # p -> q is defined as ¬p v q
def l3_conditional(val1, val2):
    if val1 == val2 == 'i':
        return '1'
    else:
        return k3_conditional(val1, val2)
def k3_biconditional(val1, val2):  # also defined (p <--> q) = (p --> q) & (q --> p)
    return k3_conjunction(k3_conditional(val1, val2), k3_conditional(val2, val1))
def l3_biconditional(val1, val2):
    return k3_conjunction(l3_conditional(val1, val2), l3_conditional(val2, val1))
k3_t_functions = {"¬": k3_negation,
                  "˅": k3_disjunction,
                  "˄": k3_conjunction,
                  "→": k3_conditional,
                  "↔": k3_biconditional}
l3_t_functions = {"¬": k3_negation,
                  "˅": k3_disjunction,
                  "˄": k3_conjunction,
                  "→": l3_conditional,
                  "↔": l3_biconditional}

K3 = Logic(short_name="K3", values=trivalued_values, premise_designated=['1'], conclusion_designated=['1'],
           false_values=['0'], true_values=['1'],
           logical_constants=classical_connectives,
           truth_functions=k3_t_functions, inference_rules=dict(), parsed_constants=parsed_classical_constants,
           quantifiers=quants)
L3 = Logic(short_name="L3", values=trivalued_values, premise_designated=['1'], conclusion_designated=['1'],
           false_values=['0'], true_values=['1'],
           logical_constants=classical_connectives,
           truth_functions=l3_t_functions, inference_rules=dict(), parsed_constants=parsed_classical_constants,
           quantifiers=quants)
LP = Logic(short_name="LP", values=trivalued_values, premise_designated=['i', '1'], conclusion_designated=['i', '1'],
           false_values=['0', 'i'], true_values=['1', 'i'],
           logical_constants=classical_connectives, truth_functions=k3_t_functions, inference_rules=dict(),
           parsed_constants=parsed_classical_constants, quantifiers=quants)
ST = Logic(short_name="ST", values=trivalued_values, premise_designated=['1'], conclusion_designated=['i', '1'],
           false_values=['0', 'i'], true_values=['1', 'i'],
           logical_constants=classical_connectives, truth_functions=k3_t_functions, inference_rules=dict(),
           parsed_constants=parsed_classical_constants, quantifiers=quants)
TS = Logic(short_name="TS", values=trivalued_values, premise_designated=['1', 'i'], conclusion_designated=['1'],
           false_values=['0', 'i'], true_values=['1', 'i'],
           logical_constants=classical_connectives, truth_functions=k3_t_functions, inference_rules=dict(),
           parsed_constants=parsed_classical_constants, quantifiers=quants)

# ------------------------------------
# RM3

def RM3_conditional(val1, val2):
    if val1 == '0':
        return '1'
    elif val2 == '1':
        return '1'
    elif val2 == '0':
        return '0'
    else:
        return 'i'
def RM3_biconditional(val1, val2):
    return k3_conjunction(RM3_conditional(val1, val2), RM3_conditional(val2, val1))
RM3_t_functions = {"¬": k3_negation,
                  "˅": k3_disjunction,
                  "˄": k3_conjunction,
                  "→": RM3_conditional,
                  "↔": RM3_biconditional}
RM3 = Logic(short_name="RM3", values=trivalued_values, premise_designated=['i', '1'], conclusion_designated=['i', '1'],
            false_values=['0', 'i'], true_values=['1', 'i'],
            logical_constants=classical_connectives, truth_functions=RM3_t_functions, inference_rules=dict(),
            parsed_constants=parsed_classical_constants, quantifiers=quants)


# ------------------------------------
# LFI1

def consistency_operator(val):
    if val == '1' or val == '0':
        return '1'
    return '0'

LFI1_parsed_constants = dict(parsed_classical_constants)
LFI1_parsed_constants["°"] = "∘"

LFI1_connectives = {1: ['¬', '∘'], 2: ['˄', '˅', '→', '↔']}
fc_copy = k3_t_functions.copy()
fc_copy["∘"] = consistency_operator
LFI1 = Logic(short_name="LFI1", values=trivalued_values, premise_designated=['i', '1'], conclusion_designated=['i', '1'],
             false_values=['0', 'i'], true_values=['1', 'i'],
             logical_constants=LFI1_connectives, truth_functions=fc_copy, inference_rules=dict(),
             parsed_constants=LFI1_parsed_constants, quantifiers=quants)


# ------------------------------------
# FDE

cuatrivalued_values = ['0', 'n', 'b', '1']
def FDE_negation(val1):
    if val1 == '1':
        return '0'
    elif val1 == '0':
        return '1'
    else:
        return val1
def FDE_disjunction(val1, val2):
    if val1 == '1' or val2 == '1':
        return '1'
    elif (val1 == 'b' and val2=='n') or (val1 == 'n' and val2=='b'):
        return '1'
    elif val1 == 'b' or val2 == 'b':
        return 'b'
    elif val1 == 'n' or val2 == 'n':
        return 'n'
    else:
        return '0'
def FDE_conjunction(val1, val2):
    if val1 == '0' or val2 == '0':
        return '0'
    elif (val1 == 'b' and val2 == 'n') or (val1 == 'n' and val2 == 'b'):
        return '0'
    elif val1 == 'n' or val2 == 'n':
        return 'n'
    elif val1 == 'b' or val2 == 'b':
        return 'b'
    else:
        return '1'
def FDE_conditional(val1, val2):
    return FDE_disjunction(FDE_negation(val1), val2)  # p -> q is defined as ¬p v q
def FDE_biconditional(val1, val2):  # also defined (p <--> q) = (p --> q) & (q --> p)
    return FDE_conjunction(FDE_conditional(val1, val2), FDE_conditional(val2, val1))
FDE_t_functions = {"¬": FDE_negation,
                   "˅": FDE_disjunction,
                   "˄":FDE_conjunction,
                   "→": FDE_conditional,
                   "↔": FDE_biconditional}
FDE = Logic(short_name="FDE", values=cuatrivalued_values, premise_designated=['b', '1'], conclusion_designated=['b', '1'],
            false_values=['0'], true_values=['1', 'i'],
            logical_constants=classical_connectives, truth_functions=FDE_t_functions, inference_rules=dict(),
            parsed_constants=parsed_classical_constants, quantifiers=quants)


logics = [Classical, K3, L3, LP, RM3, LFI1, FDE, ST, TS]


# ----------------------------------------------------------------------------------------------------------------------
# NATURAL DEDUCTION PROPOSITIONAL LOGICS

classical_connectives2 = {1: ['¬'], 2: ['˄', '˅', '→']}
parsed_classical_constants2 = {"not": "¬",
                               "or": "˅",
                               "&": "˄",
                               "and": "˄",
                               "then": "→",
                               "all": "∀",
                               "V": "∀",
                               "exists": "∃",
                               "E": "∃"}
classical_t_functions2 = {"¬": classical_negation,
                          "˅": classical_disjunction,
                          "˄": classical_conjunction,
                          "→": classical_conditional}

def Iconj(current_step, prev_steps):
    if len(prev_steps) != 2:
        if len(prev_steps) == 1:
            raise ValueError(f'Conjunction introduction takes two premises but one was given')
        else:
            raise ValueError(f'Conjunction introduction takes two premises but {len(prev_steps)} were given')
    for open_sup in prev_steps[0]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('One of the formulas given is inside a closed supposition')
    for open_sup in prev_steps[1]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('One of the formulas given is inside a closed supposition')
    prev_formula1 = prev_steps[0]['formula']
    prev_formula2 = prev_steps[1]['formula']
    return [[prev_formula1, '˄', prev_formula2], [prev_formula2, '˄', prev_formula1]]
def Econj(current_step, prev_steps):
    if len(prev_steps) != 1:
        raise ValueError(f'Conjunction elimination takes one premise but {len(prev_steps)} were given')
    for open_sup in prev_steps[0]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('The formulas given is inside a closed supposition')
    prev_formula = prev_steps[0]['formula']
    if len(prev_formula) == 3 and prev_formula[1] == '˄':
        return [prev_formula[0], prev_formula[2]]
    else:
        raise ValueError('Conjunction elimination rule was incorrectly applied')
def Idisj(current_step, prev_steps):
    if len(prev_steps) != 1:
        raise ValueError(f'Disjunction introduction takes one premise but {len(prev_steps)} were given')
    for open_sup in prev_steps[0]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('The formula given is inside a closed supposition')
    prev_formula = prev_steps[0]['formula']
    # Any formula can be entered in the other disjunct, so it just returns the formula that is present in the step
    return [[current_step['formula'][0], '˅', prev_formula], [current_step['formula'][2], '˅', prev_formula],
           [prev_formula, '˅', current_step['formula'][0]], [prev_formula, '˅', current_step['formula'][2]]]
def Edisj(current_step, prev_steps):
    if len(prev_steps) != 3:
        if len(prev_steps) == 1:
            raise ValueError(f'Disjunction elimination takes three premises but one was given')
        else:
            raise ValueError(f'Disjunction elimination takes three premises but {len(prev_steps)} were given')
    for open_sup in prev_steps[0]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('One of the formulas given is inside a closed supposition')
    for open_sup in prev_steps[1]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('One of the formulas given is inside a closed supposition')
    for open_sup in prev_steps[2]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('One of the formulas given is inside a closed supposition')
    # Check if the disjunction is present and save the disjuncts. The other two formulas are saved in conditionals
    disjunction = None
    prev_step_formulas = [s['formula'] for s in prev_steps]
    conditionals = deepcopy(prev_step_formulas)
    for formula in prev_step_formulas:
        if len(formula) == 3 and formula[1] == '˅':
            disjunction = formula
            disjunct1 = formula[0]
            disjunct2 = formula[2]
            conditionals.remove(formula)
            break
    if disjunction is None:
        raise ValueError('Disjunction elimination rule was incorrectly applied: '
                         'none of the premises given is a disjunction')

    # Check the first alleged conditional, see if it is a conditional, if its antecedent is one of the disjuncts
    # If it is, save the consequent
    if len(conditionals[0]) == 3 and conditionals[0][1] == '→':
        if conditionals[0][0] == disjunct1:
            cond0 = 'left_disjunct'
            consequent = conditionals[0][2]
        elif conditionals[0][0] == disjunct2:
            cond0 = 'right_disjunct'
            consequent = conditionals[0][2]
        else:
            raise ValueError('Disjunction elimination rule was incorrectly applied: '
                             'At least one of the conditionals does not have one of the disjuncts as antecedent')
    else:
        raise ValueError('Disjunction elimination rule was incorrectly applied: '
                         'A disjunction was given but at least one of the other formulas is not a conditional')

    # Now check the second alleged conditional
    if len(conditionals[1]) == 3 and conditionals[1][1] == '→':
        if conditionals[1][0] == disjunct1:
            # If the previous conditional paired with the left disjunct and both disjuncts are different
            if cond0 == 'left_disjunct' and disjunct1 != disjunct2:
                raise ValueError('Disjunction elimination rule was incorrectly applied: '
                                 'Both conditionals have the same disjunct as antecedent')
            elif cond0 == 'right_disjunct':
                if conditionals[1][2] != consequent:
                    raise ValueError('Disjunction elimination rule was incorrectly applied: '
                                     'The two conditionals have different consequents')

        elif conditionals[1][0] == disjunct2:
            # If the previous conditional paired with the right disjunct and both disjuncts are different
            if cond0 == 'right_disjunct' and disjunct1 != disjunct2:
                raise ValueError('Disjunction elimination rule was incorrectly applied: '
                                 'Both conditionals have the same disjunct as antecedent')
            elif cond0 == 'left_disjunct':
                if conditionals[1][2] != consequent:
                    raise ValueError('Disjunction elimination rule was incorrectly applied: '
                                     'The two conditionals have different consequents')
        else:
            raise ValueError('Disjunction elimination rule was incorrectly applied: '
                             'At least one of the conditionals does not have one of the disjuncts as antecedent')
    else:
        raise ValueError('Disjunction elimination rule was incorrectly applied: '
                         'A disjunction was given but at least one of the other formulas is not a conditional')

    # If no exception was raised at this point, then the rule was correctly applied
    return [consequent]
def Icond(current_step, prev_steps):
    if len(prev_steps) != 2:
        if len(prev_steps) == 1:
            raise ValueError(f'Conditional introduction rule takes more than one premise')
        else:
            # The GUI should never give more than two formulas here... it should check that the format is 3-10
            raise ValueError(f'An error has occured in TAUT, cannot verify application of this rule')

    # In this case, the premises come should come ordered, no need to see which is which
    # See that the first premise opens a supposition
    if not prev_steps[0]['open_sups'] or prev_steps[0]['open_sups'][-1] != prev_steps[0]['step']:
        raise ValueError("Conditional introduction rule requires that you open a supposition")
    # See that the second premise is at the same level of suppositions as the first
    if prev_steps[0]['open_sups'] != prev_steps[1]['open_sups']:
        raise ValueError('Conditional introduction rule was incorrectly applied: '
                         'First and last premises given are at different levels of supposition')
    # See that the current step closes the last supposition
    if current_step['open_sups'] != prev_steps[0]['open_sups'][:-1]:
        raise ValueError('Conditional introduction rule was incorrectly applied: '
                         'The current step does not close the supposition introduced in the first premise given')

    # If none of the above happened, return the conditional between the two formulas
    prev_formula1 = prev_steps[0]['formula']
    prev_formula2 = prev_steps[1]['formula']
    return [[prev_formula1, '→', prev_formula2]]
def Econd(current_step, prev_steps):
    if len(prev_steps) != 2:
        if len(prev_steps) == 1:
            raise ValueError(f'Conditional elimination takes two premises but one was given')
        else:
            raise ValueError(f'Conditional elimination takes two premises but {len(prev_steps)} were given')
    for open_sup in prev_steps[0]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('One of the formulas given is inside a closed supposition')
    for open_sup in prev_steps[1]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('One of the formulas given is inside a closed supposition')
    prev_formula1 = prev_steps[0]['formula']
    prev_formula2 = prev_steps[1]['formula']
    # The first formula is a conditional and the second is its antecedent, return the consequent
    if len(prev_formula1) == 3 and prev_formula1[1] == '→' and prev_formula1[0] == prev_formula2:
        return [prev_formula1[2]]
    # Same with the second formula
    elif len(prev_formula2) == 3 and prev_formula2[1] == '→' and prev_formula2[0] == prev_formula1:
        return [prev_formula2[2]]
    else:
        raise ValueError('Conditional elimination rule was incorrectly applied')
def Ineg(current_step, prev_steps):
    if len(prev_steps) != 2:
        if len(prev_steps) == 1:
            raise ValueError(f'Negation introduction rule takes more than one premise')
        else:
            # The GUI should never give more than two formulas here... it should check that the format is 3-10
            raise ValueError(f'An error has occured in TAUT, cannot verify application of this rule')

    # In this case, the premises come should come ordered, no need to see which is which
    # See that the first premise opens a supposition
    if not prev_steps[0]['open_sups'] or prev_steps[0]['open_sups'][-1] != prev_steps[0]['step']:
        raise ValueError("Negation introduction rule requires that you open a supposition")
    # See that the second premise is at the same level of suppositions as the first
    if prev_steps[0]['open_sups'] != prev_steps[1]['open_sups']:
        raise ValueError('Negation introduction rule was incorrectly applied: '
                         'First and last premises given are at different levels of supposition')
    # See that the current step closes the last supposition
    if current_step['open_sups'] != prev_steps[0]['open_sups'][:-1]:
        raise ValueError('Negation introduction rule was incorrectly applied: '
                         'The current step does not close the supposition introduced in the first premise given')

    # See that the second premise is Falsum
    prev_formula1 = prev_steps[0]['formula']
    prev_formula2 = prev_steps[1]['formula']
    if prev_formula2 != ['⊥']:
        raise ValueError('Negation introduction rule was incorrectly applied: '
                         'The last premise given is not ⊥')

    return [['¬', prev_formula1]]
def Eneg(current_step, prev_steps):
    if len(prev_steps) != 2:
        if len(prev_steps) == 1:
            raise ValueError(f'Negation elimination takes two premises but one was given')
        else:
            raise ValueError(f'Negation elimination takes two premises but {len(prev_steps)} were given')
    for open_sup in prev_steps[0]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('One of the formulas given is inside a closed supposition')
    for open_sup in prev_steps[1]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('One of the formulas given is inside a closed supposition')
    prev_formula1 = prev_steps[0]['formula']
    prev_formula2 = prev_steps[1]['formula']
    # The first formula is the negation of the first
    if len(prev_formula1) == 2 and prev_formula1[0] == '¬' and prev_formula1[1] == prev_formula2:
        return [['⊥']]
    # The second is a negation of the first
    if len(prev_formula2) == 2 and prev_formula2[0] == '¬' and prev_formula2[1] == prev_formula1:
        return [['⊥']]
    else:
        raise ValueError('Negation elimination rule was incorrectly applied')
def EFSQ(current_step, prev_steps):
    if len(prev_steps) != 1:
        raise ValueError(f'EFSQ rule takes one premise but {len(prev_steps)} were given')
    for open_sup in prev_steps[0]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('One of the formulas given is inside a closed supposition')
    prev_formula = prev_steps[0]['formula']
    current_formula = current_step['formula']
    if prev_formula == ['⊥']:
        return [current_formula]
    else:
        raise ValueError('EFSQ rule was incorrectly applied: the premise given as input is not ⊥')
def DN(current_step, prev_steps):
    if len(prev_steps) != 1:
        raise ValueError(f'Double negation rule takes one premise but {len(prev_steps)} were given')
    for open_sup in prev_steps[0]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('One of the formulas given is inside a closed supposition')
    prev_formula = prev_steps[0]['formula']
    if len(prev_formula) == 2 and prev_formula[0] == '¬' and len(prev_formula[1]) == 2 and prev_formula[1][0] == '¬':
        return [prev_formula[1][1]]
    else:
        raise ValueError('Double negation rule was incorrectly applied: '
                         'the formula given as input is not a double negation')
def REP(current_step, prev_steps):
    if len(prev_steps) != 1:
        raise ValueError(f'Repetition rule takes one premise but {len(prev_steps)} were given')
    for open_sup in prev_steps[0]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('One of the formulas given is inside a closed supposition')
    return [prev_steps[0]['formula']]

classical_inference_rules = {
    'I˄': Iconj,
    'E˄': Econj,
    'I˅': Idisj,
    'E˅': Edisj,
    'I→': Icond,
    'E→': Econd,
    'I¬': Ineg,
    'E¬': Eneg,
    'EFSQ': EFSQ,
    'DN': DN,
    'REP': REP}

Classical2 = Logic(short_name="CL", values=['0', '1'], premise_designated=['1'], conclusion_designated=['1'],
                   false_values=['0'], true_values=['1'],
                   logical_constants=classical_connectives2,
                   truth_functions=classical_t_functions2, inference_rules=classical_inference_rules,
                   parsed_constants=parsed_classical_constants2, quantifiers=quants)

minimal_inference_rules = {
    'I˄': Iconj,
    'E˄': Econj,
    'I˅': Idisj,
    'E˅': Edisj,
    'I→': Icond,
    'E→': Econd,
    'I¬': Ineg,
    'E¬': Eneg,
    'REP': REP
}
Minimal = Logic(short_name="Minimal", values=[], premise_designated=[], conclusion_designated=[],
                false_values=[], true_values=[], logical_constants=classical_connectives2,
                truth_functions=dict(), inference_rules=minimal_inference_rules,
                parsed_constants=parsed_classical_constants2, quantifiers=quants)

intuitionist_inference_rules = {
    'I˄': Iconj,
    'E˄': Econj,
    'I˅': Idisj,
    'E˅': Edisj,
    'I→': Icond,
    'E→': Econd,
    'I¬': Ineg,
    'E¬': Eneg,
    'EFSQ': EFSQ,
    'REP': REP
}
Intuitionist = Logic(short_name="Intuitionistic", values=[], premise_designated=[], conclusion_designated=[],
                     false_values=[], true_values=[], logical_constants=classical_connectives2,
                     truth_functions=dict(), inference_rules=intuitionist_inference_rules,
                     parsed_constants=parsed_classical_constants2, quantifiers=quants)

natural_deduction_logics = [Classical2, Minimal, Intuitionist]


def Iuniv(current_step, prev_steps):
    if len(prev_steps) != 1:
        raise ValueError(f'Universal quantifier introduction takes one premise but {len(prev_steps)} were given')
    for open_sup in prev_steps[0]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('The formula given is inside a closed supposition')
    prev_formula = prev_steps[0]['formula']
    current_formula = current_step['formula']
    if current_formula[0] != '∀':
        raise ValueError("Universal quantifier introduction rule was incorrectly applied: "
                         "The current formula is not an universally quantified one")
    for c in FOL_individual_constants:
        if substitute(current_formula[2], current_formula[1], c, Classical2) == prev_formula:
            if c in current_step['non_arbitrary_cts'] or c in str(current_formula):
                raise ValueError(f"Constant {c} is not arbitrary")
            return [current_formula]
    raise ValueError("Universal quantifier introduction rule was incorrectly applied: "
                     "The previous formula is not an instance of the current formula")
def Euniv(current_step, prev_steps):
    if len(prev_steps) != 1:
        raise ValueError(f'Universal quantifier elimination takes one premise but {len(prev_steps)} were given')
    for open_sup in prev_steps[0]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('The formula given is inside a closed supposition')
    prev_formula = prev_steps[0]['formula']
    if len(prev_formula) == 3 and prev_formula[0] == '∀':
        for c in FOL_individual_constants:
            if current_step['formula'] == substitute(prev_formula[2], prev_formula[1], c, Classical2):
                return [current_step['formula']]
        raise ValueError('Current formula is not an instance of the quantified formula')
    else:
        raise ValueError('Universal quantifier elimination rule was incorrectly applied:'
                         ' the formula given as input is not a universally quantified one')
def Iexist(current_step, prev_steps):
    if len(prev_steps) != 1:
        raise ValueError(f'Existential quantifier introduction takes one premise but {len(prev_steps)} were given')
    for open_sup in prev_steps[0]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('The formula given is inside a closed supposition')
    prev_formula = prev_steps[0]['formula']
    current_formula = current_step['formula']
    if current_formula[0] != '∃':
        raise ValueError("Existential quantifier introduction rule was incorrectly applied: "
                         "The current formula is not an existentially quantified one")
    for c in FOL_individual_constants:
        if substitute(current_formula[2], current_formula[1], c, Classical2) == prev_formula:
            return [current_formula]
    raise ValueError("Existential quantifier introduction rule was incorrectly applied: "
                     "The previous formula is not an instance of the current formula")
def Eexist(current_step, prev_steps):
    if len(prev_steps) != 2:
        if len(prev_steps) == 1:
            raise ValueError(f'Existential quantifier elimination takes two premises but one was given')
        else:
            raise ValueError(f'Existential quantifier elimination takes two premises but {len(prev_steps)} were given')
    for open_sup in prev_steps[0]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('One of the formulas given is inside a closed supposition')
    for open_sup in prev_steps[1]['open_sups']:
        if open_sup not in current_step['open_sups']:
            raise ValueError('One of the formulas given is inside a closed supposition')

    prev_formula1 = prev_steps[0]['formula']
    prev_formula2 = prev_steps[1]['formula']

    # The first formula is an existential quant and the second is one if its instances, return the consequent
    if len(prev_formula1) == 3 and prev_formula1[0] == '∃' and len(prev_formula2) == 3 and prev_formula2[1] == '→':
        # Check if the antecedent is an instance of the quantifier
        for c in FOL_individual_constants:
            if substitute(prev_formula1[2], prev_formula1[1], c, Classical2) == prev_formula2[0]:
                if c in current_step['non_arbitrary_cts'] or c in str(prev_formula1) or c in str(prev_formula2[2]):
                    raise ValueError(f"Constant {c} is not arbitrary")
                else:
                    return [prev_formula2[2]]
        raise ValueError("Existential quantifier elimination rule was incorrectly applied: "
                         "The antecedent of the conditional is not an instance of the existential quantifier")

    # First formula is the conditional and second is the quantifier
    elif len(prev_formula1) == 3 and prev_formula1[1] == '→' and len(prev_formula2) == 3 and prev_formula2[0] == '∃':
        # Check if the antecedent is an instance of the quantifier
        for c in FOL_individual_constants:
            if substitute(prev_formula2[2], prev_formula2[1], c, Classical2) == prev_formula1[0]:
                if c in current_step['non_arbitrary_cts'] or c in str(prev_formula2) or c in str(prev_formula1[2]):
                    raise ValueError(f"Constant {c} is not arbitrary")
                else:
                    return [prev_formula1[2]]
        raise ValueError("Existential quantifier elimination rule was incorrectly applied: "
                         "The antecedent of the conditional is not an instance of the existential quantifier")

    else:
        raise ValueError('Existential quantifier elimination rule was incorrectly applied')
classical_inference_rules2 = {
    'I˄': Iconj,
    'E˄': Econj,
    'I˅': Idisj,
    'E˅': Edisj,
    'I→': Icond,
    'E→': Econd,
    'I¬': Ineg,
    'E¬': Eneg,
    'I∀': Iuniv,
    'E∀': Euniv,
    'I∃': Iexist,
    'E∃': Eexist,
    'EFSQ': EFSQ,
    'DN': DN,
    'REP': REP}

Classical3 = Logic(short_name="CL", values=['0', '1'], premise_designated=['1'], conclusion_designated=['1'],
                   false_values=['0'], true_values=['1'],
                   logical_constants=classical_connectives2,
                   truth_functions=classical_t_functions2, inference_rules=classical_inference_rules2,
                   parsed_constants=parsed_classical_constants2, quantifiers=quants)

FOL_natural_deduction_logics = [Classical3]