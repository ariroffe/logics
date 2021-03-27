"""Mapped Logics Module

author: Joaquin S. Toranzo Calderon
date: 2021-02-08
"""

from itertools import chain, combinations
from copy import deepcopy

from logics.classes.propositional.formula import Formula
from logics.classes.propositional.inference import Inference
from logics.classes.propositional.semantics import MixedManyValuedSemantics


def powerset(iterable):
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))


class MappingMatrix:
    """Class for matrices representing either what combinations of mappings are allowed for some consequence relations
    or what combinations of mappings are linked to every possible valuation for the propositions in an inference.

    Parameters
    ----------
    truth_values: list
        A list of the truth values (which may be int, str, etc.).
    boolean_matrix: list
        A boolean matrix representing either what combinations of mappings are allowed for some consequence relations
        or what combinations of mappings are linked to every possible valuation for the propositions in an inference.
        The rows are linked to the mapping for premises and the columns to the mapping for conclusions. Rows and
        columns are ordered, such that the initial rows and columns are linked to subsets of `truth_values` with lesser
        values than the final rows and columns. The order between rows or columns linked to equinumerous subsets
        respects the order of the elements of the subsets. A permitted mapping is represented with a one and a
        prohibited mapping with a zero.

    Raises
    ------
    ValueError
        If the matrix has more rows or columns than what is possible to build with `truth_values`.

    Examples
    --------
    Definition of the classical logic constraints with a MappingMatrix

    >>> from logics.classes.propositional.semantics.mapped_logic import MappingMatrix
    >>> two_valued_truth_preservation_from_all_premises_to_some_conclusions = MappingMatrix(
    ... ['1', '0'],
    ... [   #[] ['1'] ['0'] ['1', '0']
    ...     [ 0,  1,    0,       1   ], #[]
    ...     [ 0,  1,    0,       1   ], #['1']
    ...     [ 1,  1,    1,       1   ], #['0']
    ...     [ 1,  1,    1,       1   ], #['1', '0']
    ... ])
    >>> print(two_valued_truth_preservation_from_all_premises_to_some_conclusions)
    [
      [0, 1, 0, 1]
      [0, 1, 0, 1]
      [1, 1, 1, 1]
      [1, 1, 1, 1]
    ]

    Definition of the constraints for the non-classical 3-valued system `ST`

    >>> three_valued_strict_tolerant_from_all_premises_to_some_conclusions = MappingMatrix(
    ... ['1', 'i', '0'],
    ... [   #[] ['1'] ['i'] ['0'] ['1', 'i'] ['1', '0'] ['i', '0'] ['1', 'i', '0']
    ...     [ 0,  1,    1,    0,      1,         1,         1,            1      ], #[]
    ...     [ 0,  1,    1,    0,      1,         1,         1,            1      ], #['1']
    ...     [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['i']
    ...     [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['0']
    ...     [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['1', 'i']
    ...     [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['1', '0']
    ...     [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['i', '0']
    ...     [ 1,  1,    1,    1,      1,         1,         1,            1      ], #['1', 'i', '0']
    ... ])
    >>> print(three_valued_strict_tolerant_from_all_premises_to_some_conclusions)
    [
      [0, 1, 1, 0, 1, 1, 1, 1]
      [0, 1, 1, 0, 1, 1, 1, 1]
      [1, 1, 1, 1, 1, 1, 1, 1]
      [1, 1, 1, 1, 1, 1, 1, 1]
      [1, 1, 1, 1, 1, 1, 1, 1]
      [1, 1, 1, 1, 1, 1, 1, 1]
      [1, 1, 1, 1, 1, 1, 1, 1]
      [1, 1, 1, 1, 1, 1, 1, 1]
    ]
    """

    def __init__(self, truth_values, boolean_matrix=None):
        if boolean_matrix is None:
            boolean_matrix = []

        self.mappings = []
        for truth_value in powerset(truth_values):
            self.mappings.append(list(truth_value))

        if len(boolean_matrix) > len(self.mappings):
            raise ValueError(f'There are too many rows on the matrix.')
        for row in boolean_matrix:
            if len(row) > len(self.mappings):
                raise ValueError(f'There are too many columns on the matrix.')

        self.truth_values = truth_values
        self.boolean_matrix = boolean_matrix

    def _fill_matrix(self, value):
        """Builds, with a given value, a matrix for every possible combination of subsets of the truth values."""
        self.boolean_matrix = []
        for row in range(len(self.mappings)):
            row = []
            for column in range(len(self.mappings)):
                row.append(value)
            self.boolean_matrix.append(row)

    def is_included_in(self, other):
        """Checks if the calling MappingMatrix is included in the given MappingMatrix.

        Parameters
        ----------
        other: MappingMatrix
            The MappingMatrix to be compared with.

        Raises
        ------
        ValueError
            If the quantities of rows or columns are not the same.

        Examples
        --------
        >>> from logics.instances.propositional.mapped_logic_semantics import \
        ... three_valued_strict_tolerant_from_all_premises_to_some_conclusions as ST, \
        ... three_valued_tolerant_strict_from_all_premises_to_some_conclusions as TS
        >>> TS.is_included_in(ST)
        True
        >>> ST.is_included_in(TS)
        False
        """
        if len(self.boolean_matrix) != len(other.boolean_matrix):
            raise ValueError(f'The matrices cannot be compared: quantity of rows.')

        for i in range(len(self.boolean_matrix)):
            if len(self.boolean_matrix[i]) != len(other.boolean_matrix[i]):
                raise ValueError(f'The matrices cannot be compared: quantity of columns.')

        for i in range(len(self.boolean_matrix)):
            for j in range(len(self.boolean_matrix[i])):
                if self.boolean_matrix[i][j] > other.boolean_matrix[i][j]:
                    return False
        return True

    def matrix_negation(self):
        """Returns a MappingMatrix representing the complement matrix.

        Examples
        --------
        >>> from logics.classes.propositional.semantics.mapped_logic import MappingMatrix
        >>> from logics.instances.propositional.mapped_logic_semantics import \
        ...     two_valued_truth_preservation_from_all_premises_to_some_conclusions as CL
        >>> print(CL)
        [
          [0, 1, 0, 1]
          [0, 1, 0, 1]
          [1, 1, 1, 1]
          [1, 1, 1, 1]
        ]
        >>> print(CL.matrix_negation())
        [
          [1, 0, 1, 0]
          [1, 0, 1, 0]
          [0, 0, 0, 0]
          [0, 0, 0, 0]
        ]
        """
        negation = MappingMatrix(deepcopy(self.truth_values), deepcopy(self.boolean_matrix))
        for i in range(len(self.boolean_matrix)):
            for j in range(len(self.boolean_matrix[i])):
                if self.boolean_matrix[i][j] == 0:
                    negation.boolean_matrix[i][j] = 1
                if self.boolean_matrix[i][j] == 1:
                    negation.boolean_matrix[i][j] = 0
        return negation

    def matrix_conjunction(self, other):
        """Returns a MappingMatrix representing the conjunction between the calling matrix and the given matrix.

        Parameters
        ----------
        other: MappingMatrix
            The MappingMatrix to be operated with.

        Raises
        ------
        ValueError
            If the quantities of rows or columns are not the same.

        Examples
        --------
        >>> from logics.classes.propositional.semantics.mapped_logic import MappingMatrix
        >>> from logics.instances.propositional.mapped_logic_semantics import \
        ...     two_valued_truth_preservation_from_all_premises_to_some_conclusions, \
        ...     two_valued_falsity_preservation_from_all_premises_to_some_conclusions
        >>> print(two_valued_truth_preservation_from_all_premises_to_some_conclusions.matrix_conjunction(
        ...     two_valued_falsity_preservation_from_all_premises_to_some_conclusions))
        [
          [0, 0, 0, 1]
          [0, 1, 0, 1]
          [0, 0, 1, 1]
          [1, 1, 1, 1]
        ]
        """
        if len(self.boolean_matrix) != len(other.boolean_matrix):
            raise ValueError(f'The matrices cannot be operated: quantity of rows.')
        for i in range(len(self.boolean_matrix)):
            if len(self.boolean_matrix[i]) != len(other.boolean_matrix[i]):
                raise ValueError(f'The matrices cannot be operated: quantity of columns.')

        conjunction = MappingMatrix(self.truth_values)
        conjunction._fill_matrix(0)
        for i in range(len(self.boolean_matrix)):
            for j in range(len(self.boolean_matrix[i])):
                if self.boolean_matrix[i][j] and other.boolean_matrix[i][j]:
                    conjunction.boolean_matrix[i][j] = 1
                else:
                    conjunction.boolean_matrix[i][j] = 0
        return conjunction

    def matrix_disjunction(self, other):
        """Returns a MappingMatrix representing the disjunction between the calling matrix and the given matrix.

        Parameters
        ----------
        other: MappingMatrix
            The MappingMatrix to be operated with.

        Raises
        ------
        ValueError
            If the quantities of rows or columns are not the same.

        Examples
        --------
        >>> from logics.classes.propositional.semantics.mapped_logic import MappingMatrix
        >>> from logics.instances.propositional.mapped_logic_semantics import \
        ...     two_valued_truth_preservation_from_all_premises_to_some_conclusions, \
        ...     two_valued_falsity_preservation_from_all_premises_to_some_conclusions
        >>> print(two_valued_truth_preservation_from_all_premises_to_some_conclusions.matrix_disjunction(
        ...     two_valued_falsity_preservation_from_all_premises_to_some_conclusions))
        [
          [0, 1, 1, 1]
          [1, 1, 1, 1]
          [1, 1, 1, 1]
          [1, 1, 1, 1]
        ]
        """
        if len(self.boolean_matrix) != len(other.boolean_matrix):
            raise ValueError(f'The matrices cannot be operated: quantity of rows.')
        for i in range(len(self.boolean_matrix)):
            if len(self.boolean_matrix[i]) != len(other.boolean_matrix[i]):
                raise ValueError(f'The matrices cannot be operated: quantity of columns.')

        disjunction = MappingMatrix(self.truth_values)
        disjunction._fill_matrix(0)
        for i in range(len(self.boolean_matrix)):
            for j in range(len(self.boolean_matrix[i])):
                if self.boolean_matrix[i][j] or other.boolean_matrix[i][j]:
                    disjunction.boolean_matrix[i][j] = 1
                else:
                    disjunction.boolean_matrix[i][j] = 0
        return disjunction

    def __repr__(self):
        representation = "[\n"
        for row in self.boolean_matrix:
            representation += "  " + str(row) + "\n"
        representation += "]"
        return representation


class MappedManyValuedSemantics(MixedManyValuedSemantics):
    """Class for many-valued semantics, with a consequence relation constrained by a set of allowed combinations of
    mappings for premises and conclusions. It extends the class MixedManyValuedSemantics.

    Parameters
    ----------
    language: language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
        Instance of Language or InfiniteLanguage.
    truth_values: list
        A list of the truth values (which may be int, str, etc.).
    mapping_constraints: MappingMatrix
        A boolean matrix representing the allowed combinations of mappings for premises (rows) and mapping for
        conclusions (columns). Rows and columns are ordered, such that the initial rows and columns are linked to
        subsets of truth_values with lesser values than the final rows and columns. The order between rows or columns
        linked to equinumerous subsets respects the order of the elements of the subsets. A permitted mapping is
        represented with a one and a prohibited mapping with a zero.
    truth_function_dict: dict
        Dict containing the logical constants (str) as keys, and n-dimensional lists as values (for constants of arity
        n). Will also accept any indexable (things with a `__getitem__` method, e.g. numpy arrays)
        and any n-ary callable.
    sentential_constant_values_dict: dict
        Dict containing the sentential constants (str) as keys, and their truth values (members of `truth_values`) as
        values.
    use_molecular_valuation_fast_version: bool
        Implements a faster version of the molecular valuation function (e.g. if asked for a disjunction will return
        '1' with one true disjunct, without evaluating the other). In counterpart, it is less general, since it assumes
        the Kleene truth matrices. Defaults to False.
    name: str
        Name of the system (only for prettier printing to the console).

    Notes
    -----
    As in MixedManyValuedSemantics, the order of `truth_values` is the order in which the rows and columns will be read
    in the truth functions.
    For defining `mapping_constraints`, you must also use a set of truth values: It must be the same set.

    Raises
    ------
    ValueError
        If some logical constant of the language does not receive a truth function (or receives something that is
        neither a callable nor an indexible), or some sentential constant does not receive a truth value (or gets a
        truth value not present in `truth_values`).

    Examples
    --------
    >>> from logics.instances.propositional.languages import classical_infinite_language_with_sent_constants \
    ...     as classical_language
    >>> from logics.instances.propositional.mapped_logic_semantics import \
    ...     two_valued_truth_preservation_from_all_premises_to_some_conclusions, classical_truth_functions, \
    ...     classical_sentential_constants_values
    >>> two_valued_truth_preservation_from_all_premises_to_some_conclusions_logic = MappedManyValuedSemantics(
    ...     language=classical_language,
    ...     truth_values=['1', '0'],
    ...     mapping_constraints=two_valued_truth_preservation_from_all_premises_to_some_conclusions,
    ...     truth_function_dict=classical_truth_functions,
    ...     sentential_constant_values_dict=classical_sentential_constants_values,
    ...     use_molecular_valuation_fast_version=True,
    ...     name='CL_2V_all_some')
    >>> from logics.instances.propositional.mapped_logic_semantics import \
    ...     three_valued_truth_values, three_valued_truth_functions, three_valued_sentential_constants_values, \
    ...     three_valued_strict_tolerant_from_all_premises_to_some_conclusions
    >>> three_valued_strict_tolerant_from_all_premises_to_some_conclusions_logic = MappedManyValuedSemantics(
    ...     language=classical_language,
    ...     truth_values=three_valued_truth_values,
    ...     mapping_constraints=three_valued_strict_tolerant_from_all_premises_to_some_conclusions,
    ...     truth_function_dict=three_valued_truth_functions,
    ...     sentential_constant_values_dict=three_valued_sentential_constants_values,
    ...     use_molecular_valuation_fast_version=True,
    ...     name='ST_all_some')
    """

    def __init__(self, language, truth_values, mapping_constraints, truth_function_dict,
                 sentential_constant_values_dict, use_molecular_valuation_fast_version=False,
                 name='MappedManyValuedSemantics object'):
        super().__init__(language, truth_values, [], [], truth_function_dict, sentential_constant_values_dict,
                         use_molecular_valuation_fast_version, name)
        self.mappings = []
        for truth_value in powerset(truth_values):
            self.mappings.append(list(truth_value))
        self.mapping_constraints = mapping_constraints

    def mapped_standard_to_formulae(self, formulae, atomic_valuation_dict=None, coordinate=False):
        """Gets, for a given a valuation, the subset of `truth_values` mapped to the set of formulae.

        When `coordinate` is True, gets the index of `mappings` linked to the mapped subset.

        Examples
        --------
        >>> from logics.classes.propositional.formula import Formula
        >>> from logics.instances.propositional.mapped_logic_semantics import \
        ...    three_valued_strict_tolerant_from_all_premises_to_some_conclusions_logic as ST
        >>> ST.mapped_standard_to_formulae([Formula(['p']), Formula(['q'])],
        ...                                  {'p': '0', 'q':'0'})
        ['0']
        >>> ST.mapped_standard_to_formulae([Formula(['p']), Formula(['q'])],
        ...                                  {'p': '0', 'q':'1'})
        ['1', '0']
        >>> ST.mapped_standard_to_formulae([Formula(['p']), Formula(['q'])],
        ...                                  {'p': '1', 'q':'0'})
        ['1', '0']
        >>> print(ST.mappings)
        [[], ['1'], ['i'], ['0'], ['1', 'i'], ['1', '0'], ['i', '0'], ['1', 'i', '0']]
        >>> ST.mapped_standard_to_formulae([Formula(['p']), Formula(['q'])],
        ...                                  {'p': '0', 'q':'0'}, coordinate=True)
        3
        """
        listed_valuations = [self.valuation(formula, atomic_valuation_dict) for formula in formulae]
        if coordinate:
            for i in range(len(self.mappings)):
                if set(self.mappings[i]) == set(listed_valuations):
                    return i
            print("Warning. The mapping does not correspond to a subset of the truth values of the system.")
            return (-1)
        else:
            for mapping in self.mappings:
                if set(mapping) == set(listed_valuations):
                    return mapping
            print("Warning. The mapping does not correspond to a subset of the truth values of the system.")
            return list(set(listed_valuations))

    def mapped_standard_to_inferences(self, inference, atomic_valuation_dict=None, coordinate=False):
        """Gets, for a given a valuation, the subset of `truth_values` mapped to a pair of sets of formulae, one for
        premises and one for conclusions.

        When `coordinate` is True, gets the index of `mappings` linked to the premises and the index linked to the
        conclusions.

        Examples
        --------
        >>> from logics.classes.propositional.formula import Formula
        >>> from logics.classes.propositional.inference import Inference
        >>> from logics.instances.propositional.mapped_logic_semantics import \
        ...    three_valued_strict_tolerant_from_all_premises_to_some_conclusions_logic as ST
        >>> ST.mapped_standard_to_inferences(Inference([Formula(['p']), Formula(['q'])], [Formula(['p'])]),
        ...                                  {'p': '1', 'q': '0'})
        [['1', '0'], ['1']]
        >>> print(ST.mappings)
        [[], ['1'], ['i'], ['0'], ['1', 'i'], ['1', '0'], ['i', '0'], ['1', 'i', '0']]
        >>> ST.mapped_standard_to_inferences(Inference([Formula(['p']), Formula(['q'])], [Formula(['p'])]),
        ...                                  {'p': '1', 'q': '0'},
        ...                                  coordinate=True)
        [5, 1]
        """
        mapping_for_premises = self.mapped_standard_to_formulae(inference.premises, atomic_valuation_dict,
                                                                coordinate)
        mapping_for_conclusions = self.mapped_standard_to_formulae(inference.conclusions, atomic_valuation_dict,
                                                                   coordinate)
        return [mapping_for_premises, mapping_for_conclusions]

    def valuation_matrix(self, inference):
        """Gets a valuation matrix (MappingMatrix) for a given inference.

        Parameters
        ----------
        inference: logics.classes.propositional.Inference
            The inference needed for constructing the matrix.

        Returns
        -------
        MappingMatrix
            It represents (with a one) for each possible valuation v, what combination of mappings gets linked to v.
            For every other combinations, it represents they are not linked to the inference with zeros.

        Examples
        --------
        >>> from logics.classes.propositional.inference import Inference
        >>> from logics.instances.propositional.mapped_logic_semantics import \
        ... two_valued_truth_preservation_from_all_premises_to_some_conclusions_logic as TrueTrue_AllSome
        >>> TrueTrue_AllSome.valuation_matrix(Inference([Formula(['p']), Formula(['q'])], [Formula(['p'])]))
        [
          [0, 0, 0, 0]
          [0, 1, 0, 0]
          [0, 0, 1, 0]
          [0, 1, 1, 0]
        ]
        >>> from logics.instances.propositional.mapped_logic_semantics import \
        ...    three_valued_strict_tolerant_from_all_premises_to_some_conclusions_logic as ST
        >>> ST.valuation_matrix(Inference([Formula(['p']), Formula(['q'])], [Formula(['p'])]))
        [
          [0, 0, 0, 0, 0, 0, 0, 0]
          [0, 1, 0, 0, 0, 0, 0, 0]
          [0, 0, 1, 0, 0, 0, 0, 0]
          [0, 0, 0, 1, 0, 0, 0, 0]
          [0, 1, 1, 0, 0, 0, 0, 0]
          [0, 1, 0, 1, 0, 0, 0, 0]
          [0, 0, 1, 1, 0, 0, 0, 0]
          [0, 0, 0, 0, 0, 0, 0, 0]
        ]
        """
        val_matrix = MappingMatrix(self.truth_values)
        val_matrix._fill_matrix(0)
        truth_value_combinations = self._get_truth_value_combinations(inference)
        for combination in truth_value_combinations:
            atomic_valuation_dict = self._get_atomic_valuation_dict(inference, combination)
            coord = self.mapped_standard_to_inferences(inference, atomic_valuation_dict, coordinate=True)
            val_matrix.boolean_matrix[coord[0]][coord[1]] = 1
        return val_matrix

    def satisfies(self, formula_or_inference, atomic_valuation_dict=None):
        """Returns True if the valuation satisfies the inference; False otherwise.

        For a single formula, it assumes it is the single conclusion of an empty-premises inference.

        Parameters
        ----------
        formula_or_inference: logics.classes.propositional.Formula or logics.classes.propositional.Inference
            The formula or inference to evaluate for satisfaction.
        atomic_valuation_dict: dict, optional
            A dict containing the valuations for the atomics within the formula. The keys must be strings (the atomic
            letters) and values are in `truth_values`.

        Returns
        -------
        bool
            True if the valuation satisfies the inference; False otherwise.

        Examples
        --------
        >>> from logics.classes.propositional.inference import Inference
        >>> from logics.instances.propositional.mapped_logic_semantics import \
        ... two_valued_truth_preservation_from_all_premises_to_some_conclusions_logic as TrueTrue_AllSome
        >>> TrueTrue_AllSome.satisfies(Inference([Formula(['p']), Formula(['→', ['p'], ['q']])], [Formula(['q'])]),
        ...                            {'p': '1', 'q': '0'})
        True
        >>> TrueTrue_AllSome.satisfies(Inference([Formula(['q']), Formula(['→', ['p'], ['q']])], [Formula(['p'])]),
        ...                            {'p': '0', 'q': '1'})
        False

        Notes
        -----
        There is no implementation for metainferences, yet.
        """
        if isinstance(formula_or_inference, Formula):
            return self.satisfies(Inference([], [formula_or_inference]), atomic_valuation_dict)

        if isinstance(formula_or_inference, Inference):
            coord = self.mapped_standard_to_inferences(formula_or_inference, atomic_valuation_dict, coordinate=True)
            if self.mapping_constraints.boolean_matrix[coord[0]][coord[1]] == 1:
                return True
            return False

