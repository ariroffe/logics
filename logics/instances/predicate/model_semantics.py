from copy import copy

from logics.classes.predicate.semantics.models import ModelTheory, TruthPredicateModelTheory
from logics.instances.predicate.languages import classical_infinite_predicate_language as classical_language
from logics.instances.predicate.languages import classical_function_language, arithmetic_language, \
    real_number_arithmetic_language, arithmetic_truth_language
from logics.utils.parsers.predicate_parser import arithmetic_truth_parser


# ----------------------------------------------------------------------------------------------------------------------
# Classical logic (with sentential constants)

from logics.instances.propositional.many_valued_semantics import classical_truth_functions, \
    classical_sentential_constants_values


def classical_atomic_valuation_clause(predicate_denotation, term_denotations):
    if term_denotations in predicate_denotation:
        return '1'
    return '0'
def classical_universal_quantifier_truth_function(*args):
    if '0' in args:
        return '0'
    return '1'
def classical_existential_quantifier_truth_function(*args):
    if '1' in args:
        return '1'
    return '0'

predicate_classical_truth_functions = copy(classical_truth_functions)
predicate_classical_truth_functions['atomic'] = classical_atomic_valuation_clause
predicate_classical_truth_functions['∀'] = classical_universal_quantifier_truth_function
predicate_classical_truth_functions['∃'] = classical_existential_quantifier_truth_function


classical_model_semantics = ModelTheory(language=classical_language,
                                        truth_values=['1', '0'],
                                        designated_value='1',
                                        truth_function_dict=predicate_classical_truth_functions,
                                        sentential_constant_values_dict=classical_sentential_constants_values,
                                        use_molecular_valuation_fast_version=True,
                                        use_quantifier_fast_version=True)
classical_functional_model_semantics = ModelTheory(language=classical_function_language,
                                           truth_values=['1', '0'],
                                           designated_value='1',
                                           truth_function_dict=predicate_classical_truth_functions,
                                           sentential_constant_values_dict=classical_sentential_constants_values,
                                           use_molecular_valuation_fast_version=True,
                                           use_quantifier_fast_version=True)


# ----------------------------------------------------------------------------------------------------------------------
# Classical theories

arithmetic_model_semantics = ModelTheory(language=arithmetic_language,
                                         truth_values=['1', '0'],
                                         designated_value='1',
                                         truth_function_dict=predicate_classical_truth_functions,
                                         use_molecular_valuation_fast_version=True,
                                         use_quantifier_fast_version=True)
realnumber_arithmetic_model_semantics = ModelTheory(language=real_number_arithmetic_language,
                                         truth_values=['1', '0'],
                                         designated_value='1',
                                         truth_function_dict=predicate_classical_truth_functions,
                                         sentential_constant_values_dict=classical_sentential_constants_values,
                                         use_molecular_valuation_fast_version=True,
                                         use_quantifier_fast_version=True)


from logics.utils.parsers.predicate_parser import arithmetic_truth_parser
arithmetic_truth_sentential_constants = {
    'λ': arithmetic_truth_parser.parse('~Tr(⌜λ⌝)')
}
arithmetic_truth_model_semantics = TruthPredicateModelTheory(
                                                parser=arithmetic_truth_parser,
                                                language=arithmetic_truth_language,
                                                truth_values=['1', '0'], designated_value='1',
                                                truth_function_dict=predicate_classical_truth_functions,
                                                sentential_constant_values_dict=arithmetic_truth_sentential_constants,
                                                use_molecular_valuation_fast_version=True,
                                                use_quantifier_fast_version=True)


# ----------------------------------------------------------------------------------------------------------------------
# LP, K3, ST, TS (with sentential constants)


def mvl_universal_quantifier_truth_function(*args):
    if '0' in args:
        return '0'
    if 'i' in args:
        return 'i'
    return '1'
def mvl_existential_quantifier_truth_function(*args):
    if '1' in args:
        return '1'
    if 'i' in args:
        return 'i'
    return '0'
