"""Mapped Logics Module (Instances)

author: Joaquin S. Toranzo Calderon
date: 2021-02-08
"""

from logics.classes.propositional.semantics.mapped_logic import MappingMatrix, MappedManyValuedSemantics
from logics.instances.propositional.languages import classical_infinite_language_with_sent_constants \
    as classical_language


# ----------------------------------------------------------------------------------------------------------------------
# Two Valued Logics (with sentential constants):
# Truth and Falsity preservation, universal and existential readings for multiple conclusions.

two_valued_truth_preservation_from_all_premises_to_some_conclusions = MappingMatrix(
    ['1', '0'],
    [   #[] ['1'] ['0'] ['1', '0']
        [ 0,  1,    0,       1   ], #[]
        [ 0,  1,    0,       1   ], #['1']
        [ 1,  1,    1,       1   ], #['0']
        [ 1,  1,    1,       1   ], #['1', '0']
    ])

two_valued_falsity_preservation_from_all_premises_to_some_conclusions = MappingMatrix(
    ['1', '0'],
    [   #[] ['1'] ['0'] ['1', '0']
        [ 0,  0,    1,       1   ], #[]
        [ 1,  1,    1,       1   ], #['1']
        [ 0,  0,    1,       1   ], #['0']
        [ 1,  1,    1,       1   ], #['1', '0']
    ])

two_valued_truth_preservation_from_all_premises_to_all_conclusions = MappingMatrix(
    ['1', '0'],
    [   #[] ['1'] ['0'] ['1', '0']
        [ 0,  1,    0,       0   ], #[]
        [ 0,  1,    0,       0   ], #['1']
        [ 1,  1,    1,       1   ], #['0']
        [ 1,  1,    1,       1   ], #['1', '0']
    ])

two_valued_falsity_preservation_from_all_premises_to_all_conclusions = MappingMatrix(
    ['1', '0'],
    [   #[] ['1'] ['0'] ['1', '0']
        [ 0,  0,    1,       0   ], #[]
        [ 1,  1,    1,       1   ], #['1']
        [ 0,  0,    1,       0   ], #['0']
        [ 1,  1,    1,       1   ], #['1', '0']
    ])

classical_truth_functions = {
    '~': ['0', '1'],
    '∧': [  # 1   #0
        ['1', '0'],  # 1
        ['0', '0']],  # 0
    '∨': [  # 1   #0
        ['1', '1'],  # 1
        ['1', '0']],  # 0
    '→': [  # 1   #0
        ['1', '0'],  # 1
        ['1', '1']],  # 0
    '↔': [  # 1   #0
        ['1', '0'],  # 1
        ['0', '1']],  # 0
}

classical_sentential_constants_values = {'⊥': '0', '⊤': '1'}

two_valued_truth_preservation_from_all_premises_to_some_conclusions_logic = MappedManyValuedSemantics(
    language=classical_language,
    truth_values=['1', '0'],
    mapping_constraints=two_valued_truth_preservation_from_all_premises_to_some_conclusions,
    truth_function_dict=classical_truth_functions,
    sentential_constant_values_dict=classical_sentential_constants_values,
    use_molecular_valuation_fast_version=True,
    name='CL_2V_all_some')

two_valued_falsity_preservation_from_all_premises_to_some_conclusions_logic = MappedManyValuedSemantics(
    language=classical_language,
    truth_values=['1', '0'],
    mapping_constraints=two_valued_falsity_preservation_from_all_premises_to_some_conclusions,
    truth_function_dict=classical_truth_functions,
    sentential_constant_values_dict=classical_sentential_constants_values,
    use_molecular_valuation_fast_version=True,
    name='FalsityPreservation_2V_all_some')

two_valued_truth_preservation_from_all_premises_to_all_conclusions_logic = MappedManyValuedSemantics(
    language=classical_language,
    truth_values=['1', '0'],
    mapping_constraints=two_valued_truth_preservation_from_all_premises_to_all_conclusions,
    truth_function_dict=classical_truth_functions,
    sentential_constant_values_dict=classical_sentential_constants_values,
    use_molecular_valuation_fast_version=True,
    name='CL_2V_all_all')

two_valued_falsity_preservation_from_all_premises_to_all_conclusions_logic = MappedManyValuedSemantics(
    language=classical_language,
    truth_values=['1', '0'],
    mapping_constraints=two_valued_falsity_preservation_from_all_premises_to_all_conclusions,
    truth_function_dict=classical_truth_functions,
    sentential_constant_values_dict=classical_sentential_constants_values,
    use_molecular_valuation_fast_version=True,
    name='FalsityPreservation_2V_all_all')

# ----------------------------------------------------------------------------------------------------------------------
# Three Valued Logics (with sentential constants):

three_valued_truth_values = ['1', 'i', '0']
three_valued_sentential_constants_values = {'⊥': '0', 'I':'i', '⊤': '1'}

three_valued_truth_functions = {
    '~': ['0', 'i', '1'],
    '∧': [ #1   #i   #0
          ['1', 'i', '0'],    # 1
          ['i', 'i', '0'],    # i
          ['0', '0', '0']],  # 0
    '∨': [ #1   #i   #0
          ['1', '1', '1'],    # 1
          ['1', 'i', 'i'],    # i
          ['1', 'i', '0']],  # 0
    '→': [ #1   #i   #0
          ['1', 'i', '0'],    # 1
          ['1', 'i', 'i'],    # i
          ['1', '1', '1']],  # 0
    '↔': [ #1   #i   #0
          ['1', 'i', '0'],    # 1
          ['i', 'i', 'i'],    # i
          ['0', 'i', '1']],  # 0
    }

#-- TS - All to Some --#
three_valued_tolerant_strict_from_all_premises_to_some_conclusions = MappingMatrix(
    three_valued_truth_values,
    [   #[] ['1'] ['i'] ['0'] ['1', 'i'] ['1', '0'] ['i', '0'] ['1', 'i', '0']
        [ 0,  1,    0,    0,      1,         1,         0,            1      ], #[]
        [ 0,  1,    0,    0,      1,         1,         0,            1      ], #['1']
        [ 0,  1,    0,    0,      1,         1,         0,            1      ], #['i']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['0']
        [ 0,  1,    0,    0,      1,         1,         0,            1      ], #['1', 'i']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['1', '0']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['i', '0']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['1', 'i', '0']
    ])

#-- TT - All to Some --#
three_valued_tolerant_tolerant_from_all_premises_to_some_conclusions = MappingMatrix(
    three_valued_truth_values,
    [   #[] ['1'] ['i'] ['0'] ['1', 'i'] ['1', '0'] ['i', '0'] ['1', 'i', '0']
        [ 0,  1,    1,    0,      1,         1,         1,            1      ], #[]
        [ 0,  1,    1,    0,      1,         1,         1,            1      ], #['1']
        [ 0,  1,    1,    0,      1,         1,         1,            1      ], #['i']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['0']
        [ 0,  1,    1,    0,      1,         1,         1,            1      ], #['1', 'i']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['1', '0']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['i', '0']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['1', 'i', '0']
    ])

#-- ST - All to Some --#
three_valued_strict_tolerant_from_all_premises_to_some_conclusions = MappingMatrix(
    three_valued_truth_values,
    [   #[] ['1'] ['i'] ['0'] ['1', 'i'] ['1', '0'] ['i', '0'] ['1', 'i', '0']
        [ 0,  1,    1,    0,      1,         1,         1,            1      ], #[]
        [ 0,  1,    1,    0,      1,         1,         1,            1      ], #['1']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['i']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['0']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['1', 'i']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['1', '0']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['i', '0']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['1', 'i', '0']
    ])

#-- SS - All to Some --#
three_valued_strict_strict_from_all_premises_to_some_conclusions = MappingMatrix(
    three_valued_truth_values,
    [   #[] ['1'] ['i'] ['0'] ['1', 'i'] ['1', '0'] ['i', '0'] ['1', 'i', '0']
        [ 0,  1,    0,    0,      1,         1,         0,            1      ], #[]
        [ 0,  1,    0,    0,      1,         1,         0,            1      ], #['1']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['i']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['0']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['1', 'i']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['1', '0']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['i', '0']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['1', 'i', '0']
    ])

#-- SS interseted with TT - All to Some --#
intersective_mixed_logic_between_ss_and_tt_relations_all_some = MappingMatrix(
    three_valued_truth_values,
    [   #[] ['1'] ['i'] ['0'] ['1', 'i'] ['1', '0'] ['i', '0'] ['1', 'i', '0']
        [ 0,  1,    0,    0,      1,         1,         0,            1      ], #[]
        [ 0,  1,    0,    0,      1,         1,         0,            1      ], #['1']
        [ 0,  1,    1,    0,      1,         1,         1,            1      ], #['i']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['0']
        [ 0,  1,    1,    0,      1,         1,         1,            1      ], #['1', 'i']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['1', '0']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['i', '0']
        [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['1', 'i', '0']
    ])

three_valued_tolerant_strict_from_all_premises_to_some_conclusions_logic = MappedManyValuedSemantics(
    language=classical_language,
    truth_values=three_valued_truth_values,
    mapping_constraints=three_valued_tolerant_strict_from_all_premises_to_some_conclusions,
    truth_function_dict=three_valued_truth_functions,
    sentential_constant_values_dict=three_valued_sentential_constants_values,
    use_molecular_valuation_fast_version=True,
    name='TS_all_some')

three_valued_tolerant_tolerant_from_all_premises_to_some_conclusions_logic = MappedManyValuedSemantics(
    language=classical_language,
    truth_values=three_valued_truth_values,
    mapping_constraints=three_valued_tolerant_tolerant_from_all_premises_to_some_conclusions,
    truth_function_dict=three_valued_truth_functions,
    sentential_constant_values_dict=three_valued_sentential_constants_values,
    use_molecular_valuation_fast_version=True,
    name='TT_all_some')

three_valued_strict_tolerant_from_all_premises_to_some_conclusions_logic = MappedManyValuedSemantics(
    language=classical_language,
    truth_values=three_valued_truth_values,
    mapping_constraints=three_valued_strict_tolerant_from_all_premises_to_some_conclusions,
    truth_function_dict=three_valued_truth_functions,
    sentential_constant_values_dict=three_valued_sentential_constants_values,
    use_molecular_valuation_fast_version=True,
    name='ST_all_some')

three_valued_strict_strict_from_all_premises_to_some_conclusions_logic = MappedManyValuedSemantics(
    language=classical_language,
    truth_values=three_valued_truth_values,
    mapping_constraints=three_valued_strict_strict_from_all_premises_to_some_conclusions,
    truth_function_dict=three_valued_truth_functions,
    sentential_constant_values_dict=three_valued_sentential_constants_values,
    use_molecular_valuation_fast_version=True,
    name='SS_all_some')

intersective_mixed_logic_between_ss_and_tt_relations_all_some_logic = MappedManyValuedSemantics(
    language=classical_language,
    truth_values=three_valued_truth_values,
    mapping_constraints=intersective_mixed_logic_between_ss_and_tt_relations_all_some,
    truth_function_dict=three_valued_truth_functions,
    sentential_constant_values_dict=three_valued_sentential_constants_values,
    use_molecular_valuation_fast_version=True,
    name='SS_int_TT_all_some')
