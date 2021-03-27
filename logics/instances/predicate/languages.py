from logics.classes.predicate.language import PredicateLanguage, InfinitePredicateLanguage, TruthPredicateLanguage

# Classical predicate logic
individual_constants = ['a', 'b', 'c', 'd']
variables = ['x', 'y', 'z']
quantifiers = ['∀', '∃']
metavariables = ['A', 'B', 'C']
constant_arity_dict = {'~': 1, '∧': 2, '∨': 2, '→': 2, '↔': 2}
predicate_letters = {'P': 1, 'Q': 1, 'R': 2, 'S': 3}
predicate_variables = {'X': 1, 'Y': 1, 'Z': 2}
sentential_constants = ['⊥', '⊤']

classical_predicate_language = PredicateLanguage(individual_constants=individual_constants, variables=variables,
                                                 quantifiers=quantifiers, metavariables=metavariables,
                                                 constant_arity_dict=constant_arity_dict,
                                                 predicate_letters=predicate_letters,
                                                 predicate_variables=predicate_variables,
                                                 sentential_constants=sentential_constants)
classical_infinite_predicate_language = InfinitePredicateLanguage(individual_constants=individual_constants,
                                                                  variables=variables,
                                                                  quantifiers=quantifiers,
                                                                  metavariables=metavariables,
                                                                  constant_arity_dict=constant_arity_dict,
                                                                  predicate_letters=predicate_letters,
                                                                  predicate_variables=predicate_variables,
                                                                  sentential_constants=sentential_constants)

function_symbols = {'f': 1, 'g': 2}
classical_function_language = InfinitePredicateLanguage(individual_constants=individual_constants,
                                                        variables=variables,
                                                        quantifiers=quantifiers,
                                                        metavariables=metavariables,
                                                        constant_arity_dict=constant_arity_dict,
                                                        predicate_letters=predicate_letters,
                                                        predicate_variables=predicate_variables,
                                                        sentential_constants=sentential_constants,
                                                        function_symbols=function_symbols)


# ----------------------------------------------------------------------------------------------------------------------
# Arithmetic languages (natural and real number)

arithmetic_language = PredicateLanguage(individual_constants=['0'],
                                        variables=['x', 'y', 'z'],
                                        quantifiers=quantifiers, metavariables=metavariables,
                                        constant_arity_dict=constant_arity_dict,
                                        predicate_letters={'=': 2, '>': 2, '<': 2},
                                        predicate_variables=predicate_variables,
                                        function_symbols={'s': 1, '+': 2, '*': 2, '**': 2})


def is_numeral(string):
    try:
        float(string)
        return True
    except ValueError:
        return False
real_number_arithmetic_language = PredicateLanguage(individual_constants=is_numeral,
                                                    variables=['x', 'y', 'z'],
                                                    quantifiers=quantifiers, metavariables=metavariables,
                                                    constant_arity_dict=constant_arity_dict,
                                                    predicate_letters={'=': 2, '>': 2, '<': 2},
                                                    predicate_variables=predicate_variables,
                                                    function_symbols={'+': 2, '-': 2, '*': 2, '/': 2, '//': 2, '**': 2})


arithmetic_truth_language = TruthPredicateLanguage(individual_constants=['0'],
                                                   variables=['x', 'y', 'z'],
                                                   quantifiers=quantifiers, metavariables=metavariables,
                                                   constant_arity_dict=constant_arity_dict,
                                                   predicate_letters={'Tr': 1, '=': 2, '>': 2, '<': 2},
                                                   predicate_variables=predicate_variables,
                                                   sentential_constants=['λ'],
                                                   function_symbols={'s': 1, 'quote': 1, '+': 2, '*': 2, '**': 2})
