from logics.classes.predicate.language import PredicateLanguage, InfinitePredicateLanguage, TruthPredicateLanguage

# Classical predicate logic
individual_constants = ['a', 'b', 'c', 'd', 'e']
variables = ['x', 'y', 'z']
individual_metavariables = ['α', 'β', 'γ', 'δ', 'ε']  # for rules, can be instantiated with either variables or ind constants
quantifiers = ['∀', '∃']
metavariables = ['A', 'B', 'C', 'D', 'E']  # These are formula metavariables
constant_arity_dict = {'~': 1, '∧': 2, '∨': 2, '→': 2, '↔': 2}
predicate_letters = {'P': 1, 'Q': 1, 'R': 2, 'S': 3}
predicate_variables = {'W': 1, 'X': 1, 'Y': 1, 'Z': 2}  # These can be quantified over in second order languages
predicate_metavariables = {'Π': 1, 'Σ': 1, 'Φ': 2, 'Ψ': 3}  # for rules, can be instantiated with either pred letters or pred variables
sentential_constants = ['⊥', '⊤']

classical_predicate_language = PredicateLanguage(individual_constants=individual_constants,
                                                 variables=variables,
                                                 individual_metavariables=individual_metavariables,
                                                 quantifiers=quantifiers,
                                                 metavariables=metavariables,
                                                 constant_arity_dict=constant_arity_dict,
                                                 predicate_letters=predicate_letters,
                                                 predicate_variables=predicate_variables,
                                                 predicate_metavariables=predicate_metavariables,
                                                 sentential_constants=sentential_constants)
classical_infinite_predicate_language = InfinitePredicateLanguage(individual_constants=individual_constants,
                                                                  variables=variables,
                                                                  individual_metavariables=individual_metavariables,
                                                                  quantifiers=quantifiers,
                                                                  metavariables=metavariables,
                                                                  constant_arity_dict=constant_arity_dict,
                                                                  predicate_letters=predicate_letters,
                                                                  predicate_variables=predicate_variables,
                                                                  predicate_metavariables=predicate_metavariables,
                                                                  sentential_constants=sentential_constants)

function_symbols = {'f': 1, 'g': 2}
classical_function_language = InfinitePredicateLanguage(individual_constants=individual_constants,
                                                        variables=variables,
                                                        individual_metavariables=individual_metavariables,
                                                        quantifiers=quantifiers,
                                                        metavariables=metavariables,
                                                        constant_arity_dict=constant_arity_dict,
                                                        predicate_letters=predicate_letters,
                                                        predicate_variables=predicate_variables,
                                                        predicate_metavariables=predicate_metavariables,
                                                        sentential_constants=sentential_constants,
                                                        function_symbols=function_symbols)


# ----------------------------------------------------------------------------------------------------------------------
# Arithmetic languages (natural and real number)

arithmetic_language = PredicateLanguage(individual_constants=['0'],
                                        variables=['x', 'y', 'z'],
                                        individual_metavariables=individual_metavariables,
                                        quantifiers=quantifiers,
                                        metavariables=metavariables,
                                        constant_arity_dict=constant_arity_dict,
                                        predicate_letters={'=': 2, '>': 2, '<': 2},
                                        predicate_variables=predicate_variables,
                                        predicate_metavariables=predicate_metavariables,
                                        function_symbols={'s': 1, '+': 2, '*': 2, '**': 2})


def is_numeral(string):
    try:
        float(string)
        return True
    except ValueError:
        return False
real_number_arithmetic_language = PredicateLanguage(individual_constants=is_numeral,
                                                    variables=['x', 'y', 'z'],
                                                    individual_metavariables=individual_metavariables,
                                                    quantifiers=quantifiers, metavariables=metavariables,
                                                    constant_arity_dict=constant_arity_dict,
                                                    predicate_letters={'=': 2, '>': 2, '<': 2},
                                                    predicate_variables=predicate_variables,
                                                    predicate_metavariables=predicate_metavariables,
                                                    function_symbols={'+': 2, '-': 2, '*': 2, '/': 2, '//': 2, '**': 2})


arithmetic_truth_language = TruthPredicateLanguage(individual_constants=['0'],
                                                   variables=['x', 'y', 'z'],
                                                   individual_metavariables=individual_metavariables,
                                                   quantifiers=quantifiers, metavariables=metavariables,
                                                   constant_arity_dict=constant_arity_dict,
                                                   predicate_letters={'Tr': 1, '=': 2, '>': 2, '<': 2},
                                                   predicate_variables=predicate_variables,
                                                   predicate_metavariables=predicate_metavariables,
                                                   sentential_constants=['λ'],
                                                   function_symbols={'s': 1, 'quote': 1, '+': 2, '*': 2, '**': 2})
