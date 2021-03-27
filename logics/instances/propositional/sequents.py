from copy import deepcopy

from logics.classes.propositional.proof_theories.sequents import SequentNode, SequentCalculus
from logics.utils.parsers import classical_parser
from logics.instances.propositional.languages import classical_infinite_language_nobiconditional, \
    classical_infinite_language_noconditional
from logics.utils.solvers.sequents import LKmin_sequent_reducer, LKminEA_sequent_reducer

# LK and LKmin standard presentations

# Axioms
identity = classical_parser.parse('A ==> A')

# Rules, remember that they are read backwards (the parent of the tree is the conclusion, its children the premises)
# Exchange rules
# exchange_left_premise = SequentNode(content=classical_parser.parse('Gamma, A, B, Delta ==> Pi'))
# exchange_left = SequentNode(content=classical_parser.parse('Gamma, B, A, Delta ==> Pi'),
#                             children=[exchange_left_premise])
# exchange_right_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A, B, Pi'))
# exchange_right = SequentNode(content=classical_parser.parse('Gamma ==> Delta, B, A, Pi'),
#                              children=[exchange_right_premise])
# With context variables
exchange_left_premise = SequentNode(content=classical_parser.parse('Gamma, Sigma, Lambda, Delta ==> Pi'))
exchange_left = SequentNode(content=classical_parser.parse('Gamma, Lambda, Sigma, Delta ==> Pi'),
                            children=[exchange_left_premise])
exchange_right_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta, Sigma, Lambda, Pi'))
exchange_right = SequentNode(content=classical_parser.parse('Gamma ==> Delta, Lambda, Sigma, Pi'),
                             children=[exchange_right_premise])

# Weakening rules
# weakening_left_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta'))
# weakening_left = SequentNode(content=classical_parser.parse('A, Gamma ==> Delta'),
#                              children=[weakening_left_premise])
# weakening_right_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta'))
# weakening_right = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A'),
#                               children=[weakening_right_premise])
# With context
weakening_left_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta'))
weakening_left = SequentNode(content=classical_parser.parse('Pi, Gamma ==> Delta'),
                             children=[weakening_left_premise])
weakening_right_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta'))
weakening_right = SequentNode(content=classical_parser.parse('Gamma ==> Delta, Pi'),
                              children=[weakening_right_premise])

# Contraction rules
# contraction_left_premise = SequentNode(content=classical_parser.parse('A, A, Gamma ==> Delta'))
# contraction_left = SequentNode(content=classical_parser.parse('A, Gamma ==> Delta'),
#                                children=[contraction_left_premise])
# contraction_right_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A, A'))
# contraction_right = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A'),
#                                 children=[contraction_right_premise])
# With context Variables
contraction_left_premise = SequentNode(content=classical_parser.parse('Pi, Pi, Gamma ==> Delta'))
contraction_left = SequentNode(content=classical_parser.parse('Pi, Gamma ==> Delta'),
                               children=[contraction_left_premise])
contraction_right_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta, Pi, Pi'))
contraction_right = SequentNode(content=classical_parser.parse('Gamma ==> Delta, Pi'),
                                children=[contraction_right_premise])

# Cut Rule
cut_premise_1 = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A'))
cut_premise_2 = SequentNode(content=classical_parser.parse('A, Pi ==> Sigma'))
cut = SequentNode(content=classical_parser.parse('Gamma, Pi ==> Delta, Sigma'),
                  children=[cut_premise_1, cut_premise_2])

# Operational rules
negation_left_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A'))
negation_left = SequentNode(content=classical_parser.parse('~A, Gamma ==> Delta'),
                            children=[negation_left_premise])
negation_right_premise = SequentNode(content=classical_parser.parse('A, Gamma ==> Delta'))
negation_right = SequentNode(content=classical_parser.parse('Gamma ==> Delta, ~A'),
                             children=[negation_right_premise])

conjunction_left1_premise = SequentNode(content=classical_parser.parse('A, Gamma ==> Delta'))
conjunction_left1 = SequentNode(content=classical_parser.parse('A & B, Gamma ==> Delta'),
                                children=[conjunction_left1_premise])
conjunction_left2_premise = SequentNode(content=classical_parser.parse('B, Gamma ==> Delta'))
conjunction_left2 = SequentNode(content=classical_parser.parse('A & B, Gamma ==> Delta'),
                                children=[conjunction_left2_premise])

conjunction_right_premise1 = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A'))
conjunction_right_premise2 = SequentNode(content=classical_parser.parse('Gamma ==> Delta, B'))
conjunction_right = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A & B'),
                                children=[conjunction_right_premise1, conjunction_right_premise2])

disjunction_left_premise1 = SequentNode(content=classical_parser.parse('A, Gamma ==> Delta'))
disjunction_left_premise2 = SequentNode(content=classical_parser.parse('B, Gamma ==> Delta'))
disjunction_left = SequentNode(content=classical_parser.parse('A or B, Gamma ==> Delta'),
                               children=[disjunction_left_premise1, disjunction_left_premise2])

disjunction_right1_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A'))
disjunction_right1 = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A or B'),
                                 children=[disjunction_right1_premise])
disjunction_right2_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta, B'))
disjunction_right2 = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A or B'),
                                 children=[disjunction_right2_premise])

conditional_left_premise1 = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A'))
conditional_left_premise2 = SequentNode(content=classical_parser.parse('B, Pi ==> Sigma'))
conditional_left = SequentNode(content=classical_parser.parse('A then B, Gamma, Pi ==> Delta, Sigma'),
                               children=[conditional_left_premise1, conditional_left_premise2])

conditional_right_premise = SequentNode(content=classical_parser.parse('A, Gamma ==> Delta, B'))
conditional_right = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A then B'),
                                children=[conditional_right_premise])

LK_rules = {
    'EL': exchange_left,
    'ER': exchange_right,
    'WL': weakening_left,
    'WR': weakening_right,
    'CL': contraction_left,
    'CR': contraction_right,
    'Cut': cut,
    '~L': negation_left,
    '~R': negation_right,
    '∧L1': conjunction_left1,
    '∧L2': conjunction_left2,
    '∧R': conjunction_right,
    '∨L': disjunction_left,
    '∨R1': disjunction_right1,
    '∨R2': disjunction_right2,
    '→L': conditional_left,
    '→R': conditional_right
}
LK = SequentCalculus(language=classical_infinite_language_nobiconditional, axioms={'identity': identity},
                     rules=LK_rules)
# LKmin (same as LK with no Cut)
LKmin_rules = deepcopy(LK_rules)
del LKmin_rules['Cut']
LKmin_order = ['~L', '~R', '∧L1', '∧L2', '∧R', '∨L', '∨R1', '∨R2', 'WL', 'WR', 'CL', 'CR', 'EL', 'ER']
LKmin = SequentCalculus(language=classical_infinite_language_nobiconditional, axioms={'identity': identity},
                        rules=LKmin_rules, solver=LKmin_sequent_reducer, solver_rule_order=LKmin_order)


# ----------------------------------------------------------------------------------------------------------------------
# A calculus for LKmin with Exchange Admissible (internalized in the rules), called LKminEA.
# This makes it much more efficient for the solver to work with
# And it is also easier than changing sequences for multisets (don't have to rewrite the class)

# WEAKENING RULES (Will not be applied in the solver if smart_weakening is allowed)
# For formulae only
# EA_weakening_left_premise = SequentNode(content=classical_parser.parse('Gamma, Delta ==> Pi, Sigma'))
# EA_weakening_left = SequentNode(content=classical_parser.parse('Gamma, A, Delta ==> Pi, Sigma'),
#                                 children=[EA_weakening_left_premise])
# EA_weakening_right_premise = SequentNode(content=classical_parser.parse('Gamma, Delta ==> Pi, Sigma'))
# EA_weakening_right = SequentNode(content=classical_parser.parse('Gamma, Delta ==> Pi, A, Sigma'),
#                                  children=[EA_weakening_right_premise])
# Weakening with context
EA_weakening_left_premise = SequentNode(content=classical_parser.parse('Gamma, Delta ==> Sigma'))
EA_weakening_left = SequentNode(content=classical_parser.parse('Gamma, Lambda, Delta ==> Sigma'),
                                children=[EA_weakening_left_premise])
EA_weakening_right_premise = SequentNode(content=classical_parser.parse('Gamma ==> Pi, Sigma'))
EA_weakening_right = SequentNode(content=classical_parser.parse('Gamma ==> Pi, Lambda, Sigma'),
                                 children=[EA_weakening_right_premise])

# CONTRACTION RULES (Also do not need to be applied if the multiplicative rules below are used)
# For formulae only
# EA_contraction1_left_premise = SequentNode(content=classical_parser.parse('Gamma, A, Delta, A, Pi ==> Sigma'))
# EA_contraction1_left = SequentNode(content=classical_parser.parse('Gamma, A, Delta, Pi ==> Sigma'),
#                                    children=[EA_contraction1_left_premise])
# EA_contraction2_left_premise = SequentNode(content=classical_parser.parse('Gamma, A, Delta, A, Pi ==> Sigma'))
# EA_contraction2_left = SequentNode(content=classical_parser.parse('Gamma, Delta, A, Pi ==> Sigma'),
#                                    children=[EA_contraction2_left_premise])
#
# EA_contraction1_right_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A, Pi, A, Sigma'))
# EA_contraction1_right = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A, Pi, Sigma'),
#                                     children=[EA_contraction1_right_premise])
# EA_contraction2_right_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A, Pi, A, Sigma'))
# EA_contraction2_right = SequentNode(content=classical_parser.parse('Gamma ==> Delta, Pi, A, Sigma'),
#                                     children=[EA_contraction2_right_premise])
# With context (makes things much much slower, but perhaps some sequents will not be provable without them)
EA_contraction1_left_premise = SequentNode(content=classical_parser.parse('Gamma, Lambda, Delta, Lambda, Pi ==> Sigma'))
EA_contraction1_left = SequentNode(content=classical_parser.parse('Gamma, Lambda, Delta, Pi ==> Sigma'),
                                   children=[EA_contraction1_left_premise])
EA_contraction2_left_premise = SequentNode(content=classical_parser.parse('Gamma, Lambda, Delta, Lambda, Pi ==> Sigma'))
EA_contraction2_left = SequentNode(content=classical_parser.parse('Gamma, Delta, Lambda, Pi ==> Sigma'),
                                   children=[EA_contraction2_left_premise])

EA_contraction1_right_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta, Lambda, Pi, Lambda, Sigma'))
EA_contraction1_right = SequentNode(content=classical_parser.parse('Gamma ==> Delta, Lambda, Pi, Sigma'),
                                    children=[EA_contraction1_right_premise])
EA_contraction2_right_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta, Lambda, Pi, Lambda, Sigma'))
EA_contraction2_right = SequentNode(content=classical_parser.parse('Gamma ==> Delta, Pi, Lambda, Sigma'),
                                    children=[EA_contraction2_right_premise])

# OPERATIONAL RULES
EA_negation_left_premise = SequentNode(content=classical_parser.parse('Gamma, Delta ==> Pi, A, Sigma'))
EA_negation_left = SequentNode(content=classical_parser.parse('Gamma, ~A, Delta ==> Pi, Sigma'),
                               children=[EA_negation_left_premise])
EA_negation_right_premise = SequentNode(content=classical_parser.parse('Gamma, A, Delta ==> Pi, Sigma'))
EA_negation_right = SequentNode(content=classical_parser.parse('Gamma, Delta ==> Pi, ~A, Sigma'),
                                children=[EA_negation_right_premise])

# Conjunction additive left rule
# EA_conjunction_left1_premise = SequentNode(content=classical_parser.parse('Gamma, A, Delta ==> Pi'))
# EA_conjunction_left1 = SequentNode(content=classical_parser.parse('Gamma, A & B, Delta ==> Pi'),
#                                    children=[EA_conjunction_left1_premise])
# EA_conjunction_left2_premise = SequentNode(content=classical_parser.parse('Gamma, B, Delta ==> Pi'))
# EA_conjunction_left2 = SequentNode(content=classical_parser.parse('Gamma, A & B, Delta ==> Pi'),
#                                    children=[EA_conjunction_left2_premise])

# Conjunction multiplicative left rule
# (again, more efficient to work with, no need of contraction) -- i'm following Takeuti here
EA_conjunction_left1_premise = SequentNode(content=classical_parser.parse('Gamma, A, Delta, B, Pi ==> Sigma'))
EA_conjunction_left1 = SequentNode(content=classical_parser.parse('Gamma, A & B, Delta, Pi ==> Sigma'),
                                   children=[EA_conjunction_left1_premise])
EA_conjunction_left2_premise = SequentNode(content=classical_parser.parse('Gamma, A, Delta, B, Pi ==> Sigma'))
EA_conjunction_left2 = SequentNode(content=classical_parser.parse('Gamma, Delta, A & B, Pi ==> Sigma'),
                                   children=[EA_conjunction_left2_premise])

# Do we need the reverse rules? e.g the one that concludes Gamma, Delta, B & A, Pi ==> Sigma, etc.
# I think they could be useful for the checker, but idk if for the solver

EA_conjunction_right_premise1 = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A, Pi'))
EA_conjunction_right_premise2 = SequentNode(content=classical_parser.parse('Gamma ==> Delta, B, Pi'))
EA_conjunction_right = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A & B, Pi'),
                                   children=[EA_conjunction_right_premise1, EA_conjunction_right_premise2])

EA_disjunction_left_premise1 = SequentNode(content=classical_parser.parse('Gamma, A, Delta ==> Pi'))
EA_disjunction_left_premise2 = SequentNode(content=classical_parser.parse('Gamma, B, Delta ==> Pi'))
EA_disjunction_left = SequentNode(content=classical_parser.parse('Gamma, A or B, Delta ==> Pi'),
                                  children=[EA_disjunction_left_premise1, EA_disjunction_left_premise2])

# Disjunction additive left rule
# EA_disjunction_right1_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A, Pi'))
# EA_disjunction_right1 = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A or B, Pi'),
#                                     children=[EA_disjunction_right1_premise])
# EA_disjunction_right2_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta, B, Pi'))
# EA_disjunction_right2 = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A or B, Pi'),
#                                     children=[EA_disjunction_right2_premise])
# Disjunction multiplicative left rule
EA_disjunction_right1_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A, Pi, B, Sigma'))
EA_disjunction_right1 = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A or B, Pi, Sigma'),
                                    children=[EA_disjunction_right1_premise])
EA_disjunction_right2_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A, Pi, B, Sigma'))
EA_disjunction_right2 = SequentNode(content=classical_parser.parse('Gamma ==> Delta, Pi, A or B, Sigma'),
                                    children=[EA_disjunction_right2_premise])

LKminEA_rules = {
    'WL': EA_weakening_left,
    'WR': EA_weakening_right,
    'CL1': EA_contraction1_left,
    'CL2': EA_contraction2_left,
    'CR1': EA_contraction1_right,
    'CR2': EA_contraction2_right,
    '~L': EA_negation_left,
    '~R': EA_negation_right,
    '∧L1': EA_conjunction_left1,
    '∧L2': EA_conjunction_left2,
    '∧R': EA_conjunction_right,
    '∨L': EA_disjunction_left,
    '∨R1': EA_disjunction_right1,
    '∨R2': EA_disjunction_right2,
}
LKminEA_order = ['~L', '~R', '∧L1', '∧L2', '∧R', '∨L', '∨R1', '∨R2']
LKminEA = SequentCalculus(language=classical_infinite_language_noconditional, axioms={'identity': identity},
                          rules=LKminEA_rules, solver=LKminEA_sequent_reducer, solver_rule_order=LKminEA_order)
