from copy import deepcopy

from logics.classes.propositional.semantics import MixedManyValuedSemantics, MixedMetainferentialSemantics
from logics.instances.propositional.languages import classical_infinite_language_with_sent_constants \
    as classical_language


# ----------------------------------------------------------------------------------------------------------------------
# Classical logic (with sentential constants)

classical_truth_functions = {
    '~': ['0', '1'],
    '∧': [ #1   #0
          ['1', '0'],    # 1
          ['0', '0']],   # 0
    '∨': [ #1   #0
          ['1', '1'],    # 1
          ['1', '0']],   # 0
    '→': [ #1   #0
          ['1', '0'],    # 1
          ['1', '1']],   # 0
    '↔': [ #1   #0
          ['1', '0'],    # 1
          ['0', '1']],   # 0
    }
classical_sentential_constants_values = {'⊥': '0', '⊤': '1'}

classical_mvl_semantics = MixedManyValuedSemantics(language=classical_language,
                                                   truth_values=['1', '0'],
                                                   # I use strings for consistency, logics like FDE will have 'b', 'n'
                                                   premise_designated_values=['1'],
                                                   conclusion_designated_values=['1'],
                                                   truth_function_dict=classical_truth_functions,
                                                   sentential_constant_values_dict=
                                                   classical_sentential_constants_values,
                                                   use_molecular_valuation_fast_version=True,
                                                   name='CL')


# ----------------------------------------------------------------------------------------------------------------------
# LP, K3, ST, TS (with sentential constants)

trivalued_truth_values = ['1', 'i', '0']
strict_designated_values = ['1']
tolerant_designated_values = ['1', 'i']

trivalued_truth_functions = {
    '~': ['0', 'i', '1'],
    '∧': [ #1   #i   #0
          ['1', 'i', '0'],    # 1
          ['i', 'i', '0'],    # i
          ['0', '0', '0']],   # 0
    '∨': [ #1   #i   #0
          ['1', '1', '1'],    # 1
          ['1', 'i', 'i'],    # i
          ['1', 'i', '0']],   # 0
    '→': [ #1   #i   #0
          ['1', 'i', '0'],    # 1
          ['1', 'i', 'i'],    # i
          ['1', '1', '1']],   # 0
    '↔': [ #1   #i   #0
          ['1', 'i', '0'],    # 1
          ['i', 'i', 'i'],    # i
          ['0', 'i', '1']],   # 0
    }

K3_mvl_semantics = MixedManyValuedSemantics(language=classical_language,
                                            truth_values=trivalued_truth_values,
                                            premise_designated_values=strict_designated_values,
                                            conclusion_designated_values=strict_designated_values,
                                            truth_function_dict=trivalued_truth_functions,
                                            sentential_constant_values_dict=classical_sentential_constants_values,
                                            use_molecular_valuation_fast_version=True,
                                            name='K3')
LP_mvl_semantics = MixedManyValuedSemantics(language=classical_language,
                                            truth_values=trivalued_truth_values,
                                            premise_designated_values=tolerant_designated_values,
                                            conclusion_designated_values=tolerant_designated_values,
                                            truth_function_dict=trivalued_truth_functions,
                                            sentential_constant_values_dict=classical_sentential_constants_values,
                                            use_molecular_valuation_fast_version=True,
                                            name='LP')
ST_mvl_semantics = MixedManyValuedSemantics(language=classical_language,
                                            truth_values=trivalued_truth_values,
                                            premise_designated_values=strict_designated_values,
                                            conclusion_designated_values=tolerant_designated_values,
                                            truth_function_dict=trivalued_truth_functions,
                                            sentential_constant_values_dict=classical_sentential_constants_values,
                                            use_molecular_valuation_fast_version=True,
                                            name='ST')
TS_mvl_semantics = MixedManyValuedSemantics(language=classical_language,
                                            truth_values=trivalued_truth_values,
                                            premise_designated_values=tolerant_designated_values,
                                            conclusion_designated_values=strict_designated_values,
                                            truth_function_dict=trivalued_truth_functions,
                                            sentential_constant_values_dict=classical_sentential_constants_values,
                                            use_molecular_valuation_fast_version=True,
                                            name='TS')


# ----------------------------------------------------------------------------------------------------------------------
# WK and PWK (Weak-Kleene logic and its paraconsistent version, three valued, different truth tables)

WK_truth_values = ['1', 'e', '0']
WK_designated_values = ['1']
PWK_designated_values = ['1', 'e']

WK_truth_functions = {
    '~': ['0', 'e', '1'],
    '∧': [ #1   #e   #0
          ['1', 'e', '0'],    # 1
          ['e', 'e', 'e'],    # e
          ['0', 'e', '0']],   # 0
    '∨': [ #1   #e   #0
          ['1', 'e', '1'],    # 1
          ['e', 'e', 'e'],    # e
          ['1', 'e', '0']],   # 0
    '→': [ #1   #e   #0
          ['1', 'e', '0'],    # 1
          ['e', 'e', 'e'],    # e
          ['1', 'e', '1']],   # 0
    '↔': [ #1   #e   #0
          ['1', 'e', '0'],    # 1
          ['e', 'e', 'e'],    # e
          ['0', 'e', '1']],   # 0
    }

WK_mvl_semantics = MixedManyValuedSemantics(language=classical_language,
                                            truth_values=WK_truth_values,
                                            premise_designated_values=WK_designated_values,
                                            conclusion_designated_values=WK_designated_values,
                                            truth_function_dict=WK_truth_functions,
                                            sentential_constant_values_dict=classical_sentential_constants_values,
                                            use_molecular_valuation_fast_version=False,
                                            name='WK')
PWK_mvl_semantics = MixedManyValuedSemantics(language=classical_language,
                                             truth_values=WK_truth_values,
                                             premise_designated_values=PWK_designated_values,
                                             conclusion_designated_values=PWK_designated_values,
                                             truth_function_dict=WK_truth_functions,
                                             sentential_constant_values_dict=classical_sentential_constants_values,
                                             use_molecular_valuation_fast_version=False,
                                             name='WK')


# ----------------------------------------------------------------------------------------------------------------------
# RM3 and Cooper-Cantwell (Same language and values but change some tables)

RM3_truth_functions = deepcopy(trivalued_truth_functions)
RM3_truth_functions['→'] = [ #1   #i   #0
                            ['1', '0', '0'],    # 1
                            ['1', 'i', '0'],    # i
                            ['1', '1', '1']]    # 0
RM3_truth_functions['↔'] = [ #1   #i   #0
                            ['1', '0', '0'],    # 1
                            ['0', 'i', '0'],    # i
                            ['0', '0', '1']]    # 0
RM3_mvl_semantics = MixedManyValuedSemantics(language=classical_language,
                                             truth_values=trivalued_truth_values,
                                             premise_designated_values=tolerant_designated_values,
                                             conclusion_designated_values=tolerant_designated_values,
                                             truth_function_dict=RM3_truth_functions,
                                             sentential_constant_values_dict=classical_sentential_constants_values,
                                             use_molecular_valuation_fast_version=False,
                                             name='RM3')


# ----------------------------------------------------------------------------------------------------------------------
# FDE (four-valued logic)

FDE_truth_values = ['1', 'b', 'n', '0']
FDE_designated_values = ['1', 'b']

FDE_truth_functions = {
          #1   #b   #n   #0
    '~': ['0', 'b', 'n', '1'],
    '∧': [ #1   #b   #n   #0
          ['1', 'b', 'n', '0'],    # 1
          ['b', 'b', '0', '0'],    # b
          ['n', '0', 'n', '0'],    # n
          ['0', '0', '0', '0']],   # 0
    '∨': [ #1   #b   #n   #0
          ['1', '1', '1', '1'],    # 1
          ['1', 'b', '1', 'b'],    # b
          ['1', '1', 'n', 'n'],    # n
          ['1', 'b', 'n', '0']],   # 0
    '→': [ #1   #b   #n   #0                # This is just ~(A ∨ B)
          ['1', 'b', 'n', '0'],    # 1
          ['1', 'b', '1', 'b'],    # b
          ['1', '1', 'n', 'n'],    # n
          ['1', '1', '1', '1']],   # 0
    '↔': [ #1   #b   #n   #0
          ['1', 'b', 'n', '0'],    # 1
          ['b', 'b', '1', 'b'],    # b
          ['n', '1', 'n', 'n'],    # n
          ['0', 'b', 'n', '1']],   # 0
    }


FDE_mvl_semantics = MixedManyValuedSemantics(language=classical_language,
                                             truth_values=FDE_truth_values,
                                             premise_designated_values=FDE_designated_values,
                                             conclusion_designated_values=FDE_designated_values,
                                             truth_function_dict=FDE_truth_functions,
                                             sentential_constant_values_dict=classical_sentential_constants_values,
                                             use_molecular_valuation_fast_version=False,
                                             name='FDE')


# ----------------------------------------------------------------------------------------------------------------------
# Mixed metainferential logics


def classical_logic_up_to_level(n):
    """Returns a mixed metainferential system that will validate every classically valid inference and metainference
        up to level `n`. Will fail to do that for levels above.

        The recursive definition of this function is as follows:

        .. code-block:: python

            if n == 1:
                return ST_mvl_semantics
            else:
                return MixedMetainferentialSemantics([empty_logic_up_to_level(n-1),
                                                      classical_logic_up_to_level(n-1)])

        By looking at the function below, we see that, for example, ``classical_logic_up_to_level(2)`` the same as
        ``MixedMetainferentialSemantics([TS, ST])``, and ``classical_logic_up_to_level(3)``

        Parameters
        ----------
        n: int
            The level up to which all classical inferences and metainferences will be validated.

        Returns
        -------
        logics.classes.propositional.semantics.MixedMetainferentialSemantics
            Classical logic up to level `n`

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.many_valued_semantics import classical_logic_up_to_level
        >>> ST = classical_logic_up_to_level(1)
        >>> ST.is_locally_valid(classical_parser.parse('(A then B), (B then C) / (A then C)'))
        True
        >>> ST.is_locally_valid(classical_parser.parse('(A / B), (B / C) // (A / C)'))
        False
        >>> TSST = classical_logic_up_to_level(2)
        >>> TSST.is_locally_valid(classical_parser.parse('(A / B), (B / C) // (A / C)'))
        True

        In fact, we can check that:

        >>> from logics.classes.propositional.semantics import MixedManyValuedSemantics
        >>> from logics.instances.propositional.many_valued_semantics import ST_mvl_semantics as ST, TS_mvl_semantics as TS
        >>> classical_logic_up_to_level(2) == MixedMetainferentialSemantics([TS, ST])
        True
        >>> classical_logic_up_to_level(3) == MixedMetainferentialSemantics([[ST, TS], [TS, ST]])
        True
    """
    if n == 1:
        return ST_mvl_semantics
    else:
        return MixedMetainferentialSemantics([empty_logic_up_to_level(n-1), classical_logic_up_to_level(n-1)])


def empty_logic_up_to_level(n):
    """Returns a mixed metainferential system that will validate every classically valid inference and metainference
        up to level `n`. Will fail to do that for levels above.

        The recursive definition of this function is as follows:

        .. code-block:: python

            if n == 1:
                return TS_mvl_semantics
            else:
                return MixedMetainferentialSemantics([classical_logic_up_to_level(n-1),
                                                      empty_logic_up_to_level(n-1)])

        By looking at the function above, we see that, for example, ``empty_logic_up_to_level(2)`` is ``[ST, TS]``

        Parameters
        ----------
        n: int
            The level up to which all classical inferences and metainferences will be validated.

        Returns
        -------
        logics.classes.propositional.semantics.MixedMetainferentialSemantics
            The empty logic up to level `n`

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.many_valued_semantics import empty_logic_up_to_level
        >>> TS = empty_logic_up_to_level(1)
        >>> TS.is_locally_valid(classical_parser.parse('p / p'))
        False
        >>> TS.is_locally_valid(classical_parser.parse('(p / p) // (p / p)'))
        True
        >>> STTS = empty_logic_up_to_level(2)
        >>> STTS.is_locally_valid(classical_parser.parse('(p / p) // (p / p)'))
        False

        Again, we can check that:

        >>> from logics.classes.propositional.semantics import MixedManyValuedSemantics
        >>> from logics.instances.propositional.many_valued_semantics import ST_mvl_semantics as ST, TS_mvl_semantics as TS
        >>> empty_logic_up_to_level(2) == MixedMetainferentialSemantics([ST, TS])
        True
        >>> empty_logic_up_to_level(3) == MixedMetainferentialSemantics([[TS, ST], [ST, TS]])
        True
        """
    if n == 1:
        return TS_mvl_semantics
    else:
        return MixedMetainferentialSemantics([classical_logic_up_to_level(n-1), empty_logic_up_to_level(n-1)])
