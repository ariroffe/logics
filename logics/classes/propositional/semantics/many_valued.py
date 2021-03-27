from itertools import product
from copy import copy

from logics.classes.propositional import Formula
from logics.classes.exceptions import NotWellFormed


class LocalValidityMixin:
    def _get_truth_value_combinations(self, formula_or_inference):
        """Will return an iterator that yields all possible truth value combinations for the number of atomics present
        For example, for ['∧', ['p'], ['q']] the iterator will yield (0, 0), (0, 1), (1, 0), (1, 1)
        For a formula with 3 atomics, (0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), ...
        """
        atomics = list(formula_or_inference.atomics_inside(self.language))
        if atomics:
            truth_value_combinations = product(self.truth_values, repeat=len(atomics))
            return truth_value_combinations
        else:
            # A formula with no atomics is one with only sentential constants.
            # In this case I return a dummy iterable of length 1 so that 1 valuation is considered in is_valid methods
            return [(1,)]

    def _get_atomic_valuation_dict(self, formula_or_inference, combination):
        """Given a Formula or Inference and a combination yielded by an iterator like the above (e.g. (0, 0, 1))
        Will return a dict with the atomic strings as keys and the truth values as values
        e.g, for combination (0,1) {'p': 0, 'q': 1}
        """
        atomics = list(formula_or_inference.atomics_inside(self.language))
        atomic_valuation_dict = {atomics[index]: combination[index] for index in range(len(atomics))}
        return atomic_valuation_dict

    def is_locally_valid(self, formula_or_inference):
        """Determines if a formula or inference is locally valid

        Local validity means the following:

        *A formula or inference is locally valid iff it is satisfied by every valuation*

            * For formulae, since they are evaluated by default with the conclusion standard, this is equivalent to
              claiming that *the formula is a tautology*.
            * For regular inferences this is the standard notion of validity for mixed logics. Since the premises and
              conclusions are formulae, applying the definition of satisfaction (see above) yields the following: *for
              every valuation v, if the valuation of the premises belong to the premise standard, the valuation of some
              conclusion belongs to the conclusion standard*
            * For metainferences things get more interesting. Metainferential local validity is not just
              "if the premises are valid, then the conclusion is valid" (that is the *global* notion of metainferential
              validity, see below). Rather, it means *no valuation satisfies all the premises and none of the
              conclusions*. So, for example, in `CL`, the metainference `(p / q) // (r / s)` is globally valid (since
              the premise is not valid), but locally invalid (there is a valuation that satisfies the premise but not
              the conclusion of the metainference, namely `p=1, q=1, r=1, s=0`)

        Parameters
        ----------
        formula_or_inference: logics.classes.propositional.Formula or logics.classes.propositional.Inference
            The formula or inference to evaluate for local validity. Inferences may be of level > 1

        Returns
        -------
        bool
            True if the formula / inference is locally valid, False otherwise

        Examples
        --------
        >>> from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics as CL, ST_mvl_semantics as ST
        >>> CL.is_locally_valid(classical_parser.parse('p or not p'))
        True
        >>> CL.is_locally_valid(classical_parser.parse('p, p then q / q'))
        True
        >>> CL.is_locally_valid(classical_parser.parse('q, p then q / p'))
        False
        >>> CL.is_locally_valid(classical_parser.parse('(p / q) // (r / s)'))
        False
        >>> CL.is_locally_valid(classical_parser.parse('(A / B), (B / C) // (A / C)'))
        True
        >>> ST.is_locally_valid(classical_parser.parse('(A / B), (B / C) // (A / C)'))
        False
        """
        truth_value_combinations = self._get_truth_value_combinations(formula_or_inference)
        for combination in truth_value_combinations:
            atomic_valuation_dict = self._get_atomic_valuation_dict(formula_or_inference, combination)
            if not self.satisfies(formula_or_inference, atomic_valuation_dict):
                return False
        return True

    def is_locally_antivalid(self, formula_or_inference):
        """Determines if a formula or inference is locally antivalid

        Local antivalidity means the following:

        *A formula or inference is locally antivalid iff no valuation satisfies it*

            * Since formulae are evaluated by default with the conclusion standard, this is equivalent to claiming that
              *the formula is a contradiction*
            * A (meta)inference `Γ / Δ` will be antivalid iff every valuation satisfies all the premises an none of the
              conclusions. One may think of it as an inferential equivalent of the notion of contradiction for formulae.
              Note that anti-vality is a stronger notion than invalidity.

        The parameters and return value are similar to the method above.

        Examples
        --------
        >>> from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics as CL
        >>> CL.is_locally_antivalid(classical_parser.parse('q, p then q / p'))
        False
        >>> CL.is_locally_antivalid(classical_parser.parse('p or not p / p and not p'))
        True
        """
        truth_value_combinations = self._get_truth_value_combinations(formula_or_inference)
        for combination in truth_value_combinations:
            atomic_valuation_dict = self._get_atomic_valuation_dict(formula_or_inference, combination)
            # e.g, for combination (0,1) {'p': 0, 'q': 1}
            if self.satisfies(formula_or_inference, atomic_valuation_dict):
                return False
        return True

    def is_contingent(self, formula_or_inference):
        """Returns True if the Formula / Inference is neither locally valid nor antivalid, False otherwise

        Examples
        --------
        >>> from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics as CL
        >>> CL.is_contingent(classical_parser.parse('p'))
        True
        >>> CL.is_contingent(classical_parser.parse('p, p then q / q'))
        False
        >>> CL.is_contingent(classical_parser.parse('p or not p / p and not p'))
        False
        >>> CL.is_contingent(classical_parser.parse('q, p then q / p'))
        True
        """
        return not self.is_locally_valid(formula_or_inference) and \
            not self.is_locally_antivalid(formula_or_inference)


class ValidityShortcutsMixin:
    """Some shortcut methods for the classes below, makes them more legible"""
    def is_valid(self, inference):
        """Shortcut for ``is_locally_valid(inference)``"""
        return self.is_locally_valid(inference)

    def is_antivalid(self, inference):
        """Shortcut for ``is_locally_antivalid(inference)``"""
        return self.is_locally_antivalid(inference)

    def is_tautology(self, formula):
        """Shortcut for ``is_locally_valid(formula)``"""
        return self.is_locally_valid(formula)

    def is_contradiction(self, formula):
        """Shortcut for ``is_locally_antivalid(formula)``"""
        return self.is_locally_antivalid(formula)


class MixedManyValuedSemantics(LocalValidityMixin, ValidityShortcutsMixin):
    """Class for many-valued semantics, which may contain different standards for premises and conclusions (e.g. ST, TS)

    Parameters
    ----------
    language: language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
        Instance of Language or InfiniteLanguage
    truth_values: list
        A list of the truth values (which may be int, str, etc.). In the instances below I use strings.
    premise_designated_values: list
        Must be a sublist of `truth_values`, representing the premise standard
    conclusion_designated_values: list
        Must be a sublist of `truth_values`, representing the conclusion standard
    truth_function_dict: dict
        Dict containing the logical constants (str) as keys, and n-dimensional lists as values (for constants of arity
        n). Will also accept any indexable (things with a `__getitem__` method, e.g. numpy arrays)
        and any n-ary callable .
    sentential_constant_values_dict: dict
        Dict containing the sentential constans (str) as keys, and their truth values (members of `truth_values`) as
        values
    use_molecular_valuation_fast_version: bool, optional
        Implements a faster version of the molecular valuation function (e.g. if asked for a disjunction will return
        '1' with one true disjunct, without evaluating the other). In counterpart, it is less general, since it assumes
        the Kleene truth matrices. Defaults to ``False``.
    name: str
        Name of the system (only for prettier printing to the console)

    Notes
    -----
    The order of `truth_values` is the order in which the rows and columns will be read in the truth functions.
    For instance, if `truth_values` is ``['0', 'i', '1']``, the truth function:

    .. code:: python

        {
        # (...)
        '$':
            [[v1, v2, v3],
             [v4, v5, v6],
             [v7, v8, v9]],
        # (...)
        }

    for a constant $ will be intepreted as saying that

        * $('0', '0') = v1
        * $('i', '1') = v6
        * $('1', '1') = v9
        * etc.

    However, if `truth_values` is entered as ``['1', 'i', '0']``, then

        * $('0', '0') = v9
        * $('i', '1') = v4
        * $('1', '1') = v1
        * etc.

    Raises
    ------
    ValueError
        If the premise or conclusion designated values are not a sublist of the truth values, some logical constant of
        the language does not receive a truth function (or receives something that is neither a callable nor an
        indexible), or some sentential constant does not receive a truth value (or gets a truth value not present in
        `truth_values`)

    Examples
    --------
    Definition of classical logic `CL`

    >>> from logics.instances.propositional.languages import classical_infinite_language_with_sent_constants
    >>> from logics.classes.propositional.semantics import MixedManyValuedSemantics
    >>> bivalued_truth_values = ['1', '0']  # The order is important for the lines below
    >>> classical_truth_functions = {
    ...     '~': ['0', '1'],
    ...     '∧': [ #1   #0
    ...           ['1', '0'],    # 1
    ...           ['0', '0']],   # 0
    ...     '∨': [ #1   #0
    ...           ['1', '1'],    # 1
    ...           ['1', '0']],   # 0
    ...     '→': [ #1   #0
    ...           ['1', '0'],    # 1
    ...           ['1', '1']],   # 0
    ...     '↔': [ #1   #0
    ...           ['1', '0'],    # 1
    ...           ['0', '1']],   # 0
    ...     }
    >>> CL = MixedManyValuedSemantics(language=classical_infinite_language_with_sent_constants,
    ...                               truth_values=bivalued_truth_values,
    ...                               premise_designated_values=['1'],
    ...                               conclusion_designated_values=['1'],
    ...                               truth_function_dict=classical_truth_functions,
    ...                               sentential_constant_values_dict= {'⊥': '0', '⊤': '1'},
    ...                               name='CL')

    Example of a non-classical 3-valued system: the many-valued system `ST`

    >>> from logics.instances.propositional.languages import classical_infinite_language_with_sent_constants
    >>> from logics.classes.propositional.semantics import MixedManyValuedSemantics
    >>> trivalued_truth_values = ['1', 'i', '0']  # The order is important for the lines below
    >>> trivalued_truth_functions = {
    ...     '~': ['0', 'i', '1'],
    ...     '∧': [ #1   #i   #0
    ...           ['1', 'i', '0'],    # 1
    ...           ['i', 'i', '0'],    # i
    ...           ['0', '0', '0']],   # 0
    ...     '∨': [ #1   #i   #0
    ...           ['1', '1', '1'],    # 1
    ...           ['1', 'i', 'i'],    # i
    ...           ['1', 'i', '0']],   # 0
    ...     '→': [ #1   #i   #0
    ...           ['1', 'i', '0'],    # 1
    ...           ['1', 'i', 'i'],    # i
    ...           ['1', '1', '1']],   # 0
    ...     '↔': [ #1   #i   #0
    ...           ['1', 'i', '0'],    # 1
    ...           ['i', 'i', 'i'],    # i
    ...           ['0', 'i', '1']],   # 0
    ...     }
    >>> ST = MixedManyValuedSemantics(language=classical_infinite_language_with_sent_constants,
    ...                               truth_values=trivalued_truth_values,
    ...                               premise_designated_values=['1'],
    ...                               conclusion_designated_values=['1', 'i'],
    ...                               truth_function_dict=trivalued_truth_functions,
    ...                               sentential_constant_values_dict={'⊥': '0', '⊤': '1'},
    ...                               name='ST')

    Note that since both `CL` and `ST` use the Kleene truth matrices (represented above) we could also have specified
    ``use_molecular_valuation_fast_version=True`` (would have been faster than what we did). Also note that, as stated
    above, the values of the `trivalued_truth_functions` could also be callables. For example:

    >>> def trivalued_disjunction(val1, val2):
    ...     if val1 == '1' or val2 == '1':
    ...         return '1'
    ...     elif val1 == 'i' or val2 == 'i':
    ...         return 'i'
    ...     return '0'
    >>> trivalued_truth_functions = {
    ...     '~': ['0', 'i', '1'],
    ...     '∧': [ #1   #i   #0
    ...           ['1', 'i', '0'],    # 1
    ...           ['i', 'i', '0'],    # i
    ...           ['0', '0', '0']],   # 0
    ...     '∨': trivalued_disjunction
    ...     # (...)
    ...     }

    Note that both classical logic and ST are already defined as instances in the `instances` modules, so there is no
    need to redefine them if you need them. You can just import them via:

    >>> from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics as CL, ST_mvl_semantics as ST
    """
    def __init__(self, language, truth_values, premise_designated_values, conclusion_designated_values,
                 truth_function_dict, sentential_constant_values_dict, use_molecular_valuation_fast_version=False,
                 name='MixedManyValuedSemantics object'):
        # Check that premise_designated and conclusion_designated are sublists of truth_values
        for value in premise_designated_values:
            if value not in truth_values:
                raise ValueError(f'Value {value} is not in truth_values. '
                                 f'premise_designated_values must be a sublist of truth_values')
        for value in conclusion_designated_values:
            if value not in truth_values:
                raise ValueError(f'Value {value} is not in truth_values. '
                                 f'conclusion_designated_values must be a sublist of truth_values')

        # Check that every constant of the language receives a truth function
        for constant in language.constants():
            if constant not in truth_function_dict:
                raise ValueError(f'Constant {constant} did not receive a truth function')
            if not callable(truth_function_dict[constant]) and \
                    not hasattr(truth_function_dict[constant], '__getitem__'):
                raise ValueError(f'Constant {constant} received a truth function that is neither a callalbe '
                                 f'nor an indexible')

        # Check that every sentential constant of the language gets a value in truth_values
        for sc in language.sentential_constants:
            if sc not in sentential_constant_values_dict:
                raise ValueError(f'Sentential constant {sc} did not receive a truth value')
            if sentential_constant_values_dict[sc] not in truth_values:
                raise ValueError(f'Sentential constant {sc} received a value not in truth_values')

        self.name = name  # For prettier printing in the console, especially in the classes below
        self.language = language
        self.truth_values = truth_values
        self.premise_designated_values = premise_designated_values
        self.conclusion_designated_values = conclusion_designated_values
        self.truth_function_dict = truth_function_dict
        self.sentential_constant_values_dict = sentential_constant_values_dict
        self.use_molecular_valuation_fast_version = use_molecular_valuation_fast_version

    def apply_truth_function(self, constant, *args):
        """Gets the value of a truth function applied to a given set of arguments.

        Works independently of whether the truth function for the constant is a callable or an indexible.

        Examples
        --------
        >>> from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics as CL, ST_mvl_semantics as ST
        >>> CL.apply_truth_function('~', '0')
        '1'
        >>> CL.apply_truth_function('~', '1')
        '0'
        >>> CL.apply_truth_function('∨', '0', '1')
        '1'
        >>> ST.apply_truth_function('∨', 'i', '0')
        'i'
        """
        # If the truth function is a callable (e.g. a Python function), simply pass the args
        if callable(self.truth_function_dict[constant]):
            return self.truth_function_dict[constant](*args)

        # If it is not a callable but is an indexable
        else:
            args = tuple(self.truth_values.index(x) for x in args)  # e.g. if values is [1, 0], (0, 1) turns into (1, 0)
            truth_table = copy(self.truth_function_dict[constant])
            for value_index in args:
                # If the tt is [[1, 1], [1, 0]] for the values [1, 0], calling with (0, 0) first turns into (1, 1) above
                # and then we get [1, 0] in the first run through this loop, and 0 in the second run
                truth_table = truth_table[value_index]
            return truth_table

    def valuation(self, formula, atomic_valuation_dict=None):
        """Returns the valuation of a formula, given some valuations for the atomics.

        Parameters
        ----------
        formula: logics.classes.propositional.Formula
            The formula of which you want to know the valuation
        atomic_valuation_dict: dict, optional
            A dict containing the valuations for the atomics within the formula. The keys must be strings (the atomic
            letters) and values are in `truth_values`

        Raises
        ------
        KeyError
            If some atomic present in `formula` does not get a valuation in `atomic_valuation_dict`

        Examples
        --------
        >>> from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics as CL, ST_mvl_semantics as ST
        >>> from logics.utils.parsers import classical_parser
        >>> CL.valuation(classical_parser.parse('p'), {'p': '1'})
        '1'
        >>> CL.valuation(classical_parser.parse('p then q'), {'p': '1'})
        Traceback (most recent call last):
        ...
        KeyError: 'Valuation for atomic q was not given in the atomic dict
        >>> CL.valuation(classical_parser.parse('p then q'), {'p': '1', 'q': '0'})
        '0'
        >>> ST.valuation(classical_parser.parse('p then q'), {'p': '1', 'q': 'i'})
        'i'
        >>> CL.valuation(classical_parser.parse('Bottom'))  # No atomic dict here
        '0'

        See Also
        --------
        logics.utils.parsers.classical_parser
        """
        if formula.is_atomic:
            # Propositional letter
            if self.language.is_atomic_string(formula[0]) or self.language.is_metavariable_string(formula[0]):
                try:
                    return atomic_valuation_dict[formula[0]]
                except KeyError:
                    raise KeyError(f'Valuation for atomic {formula[0]} was not given in the atomic dict')
            # Sentential constant
            elif self.language.is_sentential_constant_string(formula[0]):
                return self.sentential_constant_values_dict[formula[0]]
            else:
                raise NotWellFormed(f'{formula} is not a well-formed formula')

        else:
            # Molecular sentence
            if self.use_molecular_valuation_fast_version:
                return self._molecular_valuation_fast_version(formula, atomic_valuation_dict)

            subvaluations = tuple(self.valuation(subformula, atomic_valuation_dict) for subformula in formula.arguments())
            return self.apply_truth_function(formula.main_symbol, *subvaluations)

    def _molecular_valuation_fast_version(self, formula, atomic_valuation_dict):
        """Fast version of valuation for molecular sentences (Takes about half the time in my preliminary tests)"""
        if formula.main_symbol == '~':
            inside_val = self.valuation(formula[1], atomic_valuation_dict)
            if inside_val == '1':
                return '0'
            elif inside_val == 'i':
                return 'i'
            elif inside_val == '0':
                return '1'

        elif formula.main_symbol == '∧':
            val1 = self.valuation(formula[1], atomic_valuation_dict)
            if val1 == '0':
                return '0'
            val2 = self.valuation(formula[2], atomic_valuation_dict)
            if val2 == '0':
                return '0'
            elif val1 == '1' and val2 == '1':
                return '1'
            return 'i'

        elif formula.main_symbol == '∨':
            val1 = self.valuation(formula[1], atomic_valuation_dict)
            if val1 == '1':
                return '1'
            val2 = self.valuation(formula[2], atomic_valuation_dict)
            if val2 == '1':
                return '1'
            elif val1 == '0' and val2 == '0':
                return '0'
            return 'i'

        elif formula.main_symbol == '→':
            val1 = self.valuation(formula[1], atomic_valuation_dict)
            if val1 == '0':
                return '1'
            val2 = self.valuation(formula[2], atomic_valuation_dict)
            if val2 == '1':
                return '1'
            elif val1 == '1' and val2 == '0':
                return '0'
            return 'i'

        elif formula.main_symbol == '↔':
            val1 = self.valuation(formula[1], atomic_valuation_dict)
            if val1 == 'i':
                return 'i'
            val2 = self.valuation(formula[2], atomic_valuation_dict)
            if val2 == 'i':
                return 'i'
            elif val1 == val2:
                return '1'
            return '0'

    def satisfies(self, formula_or_inference, atomic_valuation_dict=None, evaluate_premise=False):
        """Returns True if the valuation satisfies the inference / formula, False otherwise.

        For formulae, being satisfied by a valuation according to a standard (i.e. a subset of truth values) means
        that the valuation belongs to that standard. By default formulae are evaluated using the conclusion standard
        of the logic.

        For (meta)inferences, satisfaction is defined recursively: *Γ / Δ is satisfied according to valuation v iff
        (if every premise is satisfied according to v then some conclusion is satisfied according to v)*. More
        intuitively, what this means is that a valuation satisfies an inference when *it is not a counterexample to it*
        (i.e. all premises in the premise standard but no conclusion in the conclusion standard)

        Parameters
        ----------
        formula_or_inference: logics.classes.propositional.Formula or logics.classes.propositional.Inference
            The formula or inference to evaluate for satisfaction. The inference may be of level > 1
        atomic_valuation_dict: dict, optional
            A dict containing the valuations for the atomics within the formula. The keys must be strings (the atomic
            letters) and values are in `truth_values`
        evaluate_premise: bool
            Formulae are evaluated by default with the conclusion standard. If `evaluate_premise` is True they will be
            evaluated with the premise standard. If you pass an inference, the correct standard will automatically be
            used, and you should leave the value by default

        Returns
        -------
        bool
            True if the valuation satisfies the formula / inference, False otherwise

        Raises
        ------
        KeyError
            If some atomic present in `formula` does not get a valuation in `atomic_valuation_dict`

        Examples
        --------
        >>> from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics as CL, ST_mvl_semantics as ST
        >>> from logics.utils.parsers import classical_parser
        >>> CL.satisfies(classical_parser.parse('p'), {'p': '1'})
        True
        >>> ST.satisfies(classical_parser.parse('p'), {'p': 'i'})
        True
        >>> ST.satisfies(classical_parser.parse('p'), {'p': 'i'}, evaluate_premise=True)
        False
        >>> CL.satisfies(classical_parser.parse('p then q, q / p'), {'p': '1', 'q': '1'})
        True
        >>> CL.satisfies(classical_parser.parse('p then q, q / p'), {'p': '0', 'q': '1'})
        False
        >>> CL.satisfies(classical_parser.parse('(A / B), (B / C) // (A / C)'),
        ...                                     {'A': '1', 'B': '1', 'C': '0'})
        True
        >>> ST.satisfies(classical_parser.parse('(A / B), (B / C) // (A / C)'),
        ...                                     {'A': '1', 'B': 'i', 'C': '0'})
        False
        """
        # Formulae
        if isinstance(formula_or_inference, Formula):
            if evaluate_premise:
                if self.valuation(formula_or_inference, atomic_valuation_dict) in self.premise_designated_values:
                    return True
                return False
            else:
                if self.valuation(formula_or_inference, atomic_valuation_dict) in self.conclusion_designated_values:
                    return True
                return False

        # Inferences
        else:
            for premise in formula_or_inference.premises:
                # For inferences of level 1 (regular inferences) we have to tell it to evaluate the premises with the
                # premise designated value
                if isinstance(premise, Formula):
                    evaluate_premise = True
                if not self.satisfies(premise, atomic_valuation_dict, evaluate_premise=evaluate_premise):
                    return True  # If some premise is not satisfied, the inference is

            for conclusion in formula_or_inference.conclusions:
                if self.satisfies(conclusion, atomic_valuation_dict):
                    return True  # If one conclusion is satisfied, the inference is

            # If you get to here it is because the premises are satisfied and the conclusions are not
            return False

    def is_globally_valid(self, inference):
        """Determines if an inference is globally valid.

        Global validity means:

        *A metainference Γ / Δ is globally valid iff (if every premise in Γ is valid, then some conclusion in Δ is
        valid)*. Note that the *is valid* expressions in the right conditional may be interpreted locally or globally.

        This method does the following (which I think is the standard way of reading global validity):

            * For formulae and level 1 inferences, the *is valid* on the right is read *locally*
            * For metainferences (level > 1), it is read *globally*

        Notes
        -----
        Evaluating global validity of schematic metainferences can lead to (conceptual) problems, and should be avoided.
        For instance *(A / B) // (C / D)* will come out as globally valid in CL, but it may have invalid instances,
        e.g. *(p → p / p → p) // (p → p / p ∧ ~p)*

        Examples
        --------
        >>> from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics as CL
        >>> CL.is_globally_valid(classical_parser.parse('(p / q) // (r / s)'))
        True
        >>> CL.is_globally_valid(classical_parser.parse('((p / p) // (p / p)) /// ((p / q) // (r / s))'))
        True
        """
        if isinstance(inference, Formula) or inference.level == 1:
            return self.is_locally_valid(inference)

        for premise in inference.premises:
            if premise.level == 0:
                raise ValueError("Global validity 1 not defined for formulae")
            if not self.is_globally_valid(premise):
                return True  # If some premise is globally invalid, the inference is globally valid

        for conclusion in inference.conclusions:
            if conclusion.level == 0:
                raise ValueError("Global validity 1 not defined for formulae")
            if self.is_globally_valid(conclusion):
                return True  # If some conclusion is globally valid, the inference is globally valid

        # If you got to here, all premises are globally valid and all conclusions globally invalid
        return False

    def is_globally_valid2(self, inference):
        """Determines if an inference is globally valid (in a second, different sense).

        Same as the method above, but for inferences of level 2 and above evaluates the conditional:

        *If all the premises are locally valid then the conclusion is locally valid*

        Examples
        --------
        >>> from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics as CL
        >>> CL.is_globally_valid2(classical_parser.parse('(p / q) // (r / s)'))
        True
        >>> CL.is_globally_valid2(classical_parser.parse('((p / p) // (p / p)) /// ((p / q) // (r / s))'))
        False
        """
        if isinstance(inference, Formula) or inference.level == 1:
            return self.is_locally_valid(inference)

        for premise in inference.premises:
            if not self.is_locally_valid(premise):
                return True  # If some premise is locally invalid, the inference is globally valid

        for conclusion in inference.conclusions:
            if self.is_locally_valid(conclusion):
                return True  # If some conclusion is locally valid, the inference is globally valid

        # If you got to here, all premises are locally valid and all conclusions locally invalid
        return False

    def is_globally_valid3(self, inference):
        """Determines if an inference is globally valid (in a third, different sense).

        Same as the two above but does global validity all the way down, i.e. a level 1 inference is globally valid iff
        if the premises globally valid (i.e. are tautologies), some conclusion is globally valid (is a tautology)

        Examples
        --------
        >>> from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics as CL
        >>> CL.is_globally_valid3(classical_parser.parse('(p / q)'))
        True
        >>> CL.is_globally_valid3(classical_parser.parse('(p / q) // (r / s)'))
        True
        """
        for premise in inference.premises:
            if not self.is_locally_valid(premise):  # For formulae this is equivalent to is_tautology
                return True  # If some premise is locally invalid, the inference is globally valid

        for conclusion in inference.conclusions:
            if self.is_locally_valid(conclusion):  # For formulae this is equivalent to is_tautology
                return True  # If some conclusion is locally valid, the inference is globally valid

        # If you got to here, all premises are locally valid and all conclusions locally invalid
        return False

    def truth_table(self, formula):
        """Returns a representation of a truth table for a formula.

        Takes an instance of Formula as input, and returns 2-list where the first member is a list of subformulae
        (ordered by depth) and the second member is a 2-dimensional list with the valuations of those subformulae
        (in that order)

        Examples
        --------
        >>> from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics as CL
        >>> CL.truth_table(classical_parser.parse('p'))
        [[['p']], [['1'], ['0']]]
        >>> subformulae, table = CL.truth_table(classical_parser.parse('p then q'))
        >>> subformulae
        [['p'], ['q'], ['→', ['p'], ['q']]]
        >>> for row in table:
        ...     print(row)
        ['1', '1', '1']
        ['0', '1', '1']
        ['1', '0', '0']
        ['0', '0', '1']

        In each row above, the three values correspond to the values
        of `p`, `q`, and `p → q` respectively
        """
        ordered_subformulae = sorted(formula.subformulae, key=lambda x: x.depth)
        truth_value_combinations = self._get_truth_value_combinations(formula)
        truth_table = list()
        for combination in truth_value_combinations:
            atomic_valuation_dict = self._get_atomic_valuation_dict(formula, combination)
            truth_table_row = list()
            for subformula in ordered_subformulae:
                truth_table_row.append(self.valuation(subformula, atomic_valuation_dict))
            truth_table.append(truth_table_row)
        return [ordered_subformulae, truth_table]

    def __repr__(self):
        return self.name


# ----------------------------------------------------------------------------------------------------------------------
# ----------------------------------------------------------------------------------------------------------------------


class MixedMetainferentialSemantics(LocalValidityMixin, ValidityShortcutsMixin, list):
    """Class for mixed *metainferential* logics, where the premises and conclusions standards are themselves mixed.

    This class extends list, so you should just pass a 2-list with the mixed standards you want to combine. The given
    logics should have the same language and truth values, otherwise things may fail.

    Raises
    ------
    ValueError
        If you pass less or more than two arguments

    Examples
    --------
    >>> from logics.utils.parsers import classical_parser
    >>> from logics.classes.propositional.semantics import MixedMetainferentialSemantics
    >>> from logics.instances.propositional.many_valued_semantics import ST_mvl_semantics as ST, TS_mvl_semantics as TS
    >>> # TS invalidates identity (and every other inference) but validates meta-identity
    >>> TS.is_locally_valid(classical_parser.parse('p / p'))
    False
    >>> TS.is_locally_valid(classical_parser.parse('(p / p) // (p / p)'))
    True
    >>> # ST invalidates Cut
    >>> ST.is_locally_valid(classical_parser.parse('(A / B), (C / D) // (A / C)'))
    False
    >>> # ST/TS and TS/ST go empty and classical one level more
    >>> STTS = MixedMetainferentialSemantics([ST, TS])
    >>> STTS.is_locally_valid(classical_parser.parse('(p / p) // (p / p)'))
    False
    >>> TSST = MixedMetainferentialSemantics([TS, ST])
    >>> TSST.is_locally_valid(classical_parser.parse('(A / B), (B / C) // (A / C)'))
    True

    Each of the two arguments of MixedMetainferentialSemantics may be 2-lists, and the __init__ method will
    automatically turn them into MixedMetainferentialSemantics. For example:

    >>> STTS_TSST = MixedMetainferentialSemantics([[ST, TS], [TS, ST]])
    >>> type(STTS_TSST[0])
    <class 'logics.classes.propositional.semantics.many_valued.MixedMetainferentialSemantics'>
    """
    def __init__(self, *args, **kwargs):
        """
        Must be a 2-list where the first member and second members are instances of either MixedManyValuedSemantics or
        MixedMetainferentialLogic. If they are regular 2-lists, turns them into a MML
        """
        super().__init__(*args, **kwargs)
        if len(self) != 2:
            raise ValueError('Can only slice two logics')

        if type(self[0]) == list and len(self[0]) == 2:
            self[0] = MixedMetainferentialSemantics(self[0])
        if type(self[1]) == list and len(self[1]) == 2:
            self[1] = MixedMetainferentialSemantics(self[1])
        # Made like this, extending list, so that you can do things like [[TS, ST], [ST, TS]]

        self.premise_standard = self[0]
        self.conclusion_standard = self[1]
        # Both have the same language and truth values, so pick one
        self.language = self.premise_standard.language
        self.truth_values = self.premise_standard.truth_values

    def satisfies(self, inference, atomic_valuation_dict=None, evaluate_premise=False):
        """Unlike the class above, this method only accepts instances of Inference
        Returns False if all premises are satisfied by the premise standard and the conclusion is not by the conclusion
        standard. Otherwise returns True
        """
        for premise in inference.premises:
            # If the inference given is of level 1, we have to tell the premise semantics to evaluate it with its
            # premise designated value
            if isinstance(premise, Formula):
                evaluate_premise = True
            if not self.premise_standard.satisfies(premise, atomic_valuation_dict, evaluate_premise):
                return True
        for conclusion in inference.conclusions:
            if self.conclusion_standard.satisfies(conclusion, atomic_valuation_dict):
                return True
        return False

    def is_globally_valid(self, inference):
        """
        Same as in the class above
        """
        if inference.level == 1:
            return self.conclusion_standard.is_locally_valid(inference)

        for premise in inference.premises:
            if not self.premise_standard.is_globally_valid(premise):
                return True

        for conclusion in inference.conclusions:
            if self.conclusion_standard.is_globally_valid(conclusion):
                return True

        return False

    def is_globally_valid2(self, inference):
        """
        Same as in the class above
        """
        if inference.level == 1:
            return self.conclusion_standard.is_locally_valid(inference)

        for premise in inference.premises:
            if not self.premise_standard.is_locally_valid1(premise):
                return True

        for conclusion in inference.conclusions:
            if self.conclusion_standard.is_locally_valid1(conclusion):
                return True

        return False

    def is_globally_valid3(self, inference):
        """
        Same as in the class above
        """
        for premise in inference.premises:
            if not self.premise_standard.is_locally_valid(premise):
                return True

        for conclusion in inference.conclusions:
            if self.conclusion_standard.is_locally_valid(conclusion):
                return True

        return False


# ----------------------------------------------------------------------------------------------------------------------
# ----------------------------------------------------------------------------------------------------------------------
# INTERSECTION AND UNION BETWEEN LOGICS

class IntersectionLogic(LocalValidityMixin, ValidityShortcutsMixin, list):
    """A list of logics intersected.

    An inference will be valid (satisfied) iff valid (satisfied) in all of them

    Examples
    --------
    >>> from logics.utils.parsers import classical_parser
    >>> from logics.instances.propositional.many_valued_semantics import ST_mvl_semantics as ST, TS_mvl_semantics as TS
    >>> I_TS_ST = IntersectionLogic([TS, ST])
    >>> I_TS_ST.is_valid(classical_parser.parse('p / p'))  # Valid in ST, invalid in TS
    False
    >>> I_TS_ST.is_locally_valid(classical_parser.parse('(A / B), (B / C) // (A / C)'))  # Valid in TS, invalid in ST
    False

    It is also possible to put more than two systems in intersection, for example:

    >>> from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics as CL
    >>> I_TS_ST_CL = IntersectionLogic([TS, ST, CL])

    In this case, this system will be equal to I_TS_ST, since CL is stronger inferentially and metainferentially
    than both ST and TS.
    """
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        # All have the same language and truth values, so pick one
        self.language = self[0].language
        self.truth_values = self[0].truth_values

    def satisfies(self, inference, atomic_valuation_dict=None, evaluate_premise=False):
        for logic in self:
            if not logic.satisfies(inference, atomic_valuation_dict, evaluate_premise=evaluate_premise):
                return False
        return True

    def is_globally_valid(self, inference):
        for logic in self:
            if not logic.is_globally_valid(inference):
                return False
        return True

    def is_globally_valid2(self, inference):
        for logic in self:
            if not logic.is_globally_valid2(inference):
                return False
        return True

    def is_globally_valid3(self, inference):
        for logic in self:
            if not logic.is_globally_valid3(inference):
                return False
        return True

    def __repr__(self):
        return '⋂' + super().__repr__()


class UnionLogic(LocalValidityMixin, ValidityShortcutsMixin, list):
    """A list of logics put in union.

    An inference will be valid (satisfied) iff valid (satisfied) in at leas one of them

    Examples
    --------
    >>> from logics.utils.parsers import classical_parser
    >>> from logics.instances.propositional.many_valued_semantics import ST_mvl_semantics as ST, TS_mvl_semantics as TS
    >>> U_TS_ST = UnionLogic([TS, ST])
    >>> U_TS_ST.is_valid(classical_parser.parse('p / p'))  # Valid in ST, invalid in TS
    True
    >>> U_TS_ST.is_locally_valid(classical_parser.parse('(A / B), (B / C) // (A / C)'))  # Valid in TS, invalid in ST
    True

    It is also possible to put more than two systems in intersection, for example:

    >>> from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics as CL
    >>> U_TS_ST_CL = UnionLogic([TS, ST, CL])

    In this case, this system will be equal to CL, since it is stronger inferentially and metainferentially
    than both ST and TS.
    """
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        # All have the same language and truth values, so pick one
        self.language = self[0].language
        self.truth_values = self[0].truth_values

    def satisfies(self, inference, atomic_valuation_dict=None, evaluate_premise=False):
        for logic in self:
            if logic.satisfies(inference, atomic_valuation_dict, evaluate_premise):
                return True
        return False

    def is_globally_valid(self, inference):
        for logic in self:
            if logic.is_globally_valid(inference):
                return True
        return False

    def is_globally_valid2(self, inference):
        for logic in self:
            if logic.is_globally_valid2(inference):
                return True
        return False

    def is_globally_valid3(self, inference):
        for logic in self:
            if logic.is_globally_valid3(inference):
                return True
        return False

    def __repr__(self):
        return '⋃' + super().__repr__()
