from copy import copy
from itertools import product, combinations

from logics.classes.predicate import PredicateFormula
from logics.classes.exceptions import DenotationError
from logics.utils.parsers.parser_utils import godel_decode
from logics.utils.parsers.predicate_parser import arithmetic_truth_parser


class Model(dict):
    """Class for representing classical models

    Extends ``dict``. The keys should be:

    * ``m['domain'] = {d1, ..., dn}`` for the domain
    * ``m['item'] = ...`` for the language items

    Note that:

    * Individual constants must denote members of the domain
    * Monadic predicate letters must denote a set of members of the domain
    * n(>1)-adic predicates must denote a set of n-tuples of members of the domain
    * Function symbols must denote ordered pairs (len 2-tuples) consisting of ``((argument1, ..., argumentn), value)``,
      where the first element is a tuple of the arguments and the second the value for those arguments.

    The domain can be any iterable (useful for infinite domains, e.g. for arithmetic, use ``itertools.count(0)``)
    since the domain only takes a role in a loop (as the quantifier bound in unbounded quantified formulae).
    Predicates and function symbols can also denote callables (predicates must return truth values). See below.

    Attributes
    ----------
    fixed_denotations: dict
        Class attribute (an empty dict by default). For theories that have expressions with fixed denotations (for
        individual constants, predicates and/or function symbols), you can subclass ``Model`` and add those default
        denotations here. The way to do so is to use the symbol string as a key and give an element or a callable
        as value. See below for some examples.

    Examples
    --------
    A model of an abstract logical theory:

    >>> from logics.classes.predicate.semantics import Model
    >>> model = Model({
    ...     'domain': {1, 2},
    ...     'a': 1,
    ...     'b': 2,
    ...     'P': {1},
    ...     'R': {(1,1), (1,2)},
    ...     'f': {((1,), 2), ((2,), 1)},
    ...     'g': {((1, 1), 1), ((1, 2), 2), ((2, 1), 1), ((2, 2), 2)}
    ... })

    If your theory has some expressions with fixed default denotations, you can subclass ``Model`` and specify a
    different ``fixed_denotations`` dict. For instance:

    >>> class ArithmeticModel(Model):
    ...     def __init__(self, *args, **kwargs):
    ...         super().__init__(*args, **kwargs)
    ...         self.fixed_denotations.update({
    ...             '0': 0,
    ...             's': lambda x: x + 1,  # note that the denotations below are all callables
    ...             '+': lambda x, y: x + y,
    ...             '*': lambda x, y: x * y,
    ...             '**': lambda x, y: x ** y,
    ...             '=': lambda x, y: '1' if x == y else '0',
    ...             '>': lambda x, y: '1' if x > y else '0',
    ...             '<': lambda x, y: '1' if x < y else '0',
    ...         })

    As done above, it can be better to update the ``fixed_denotations`` in the ``__init__`` method instead of
    overriding it completely, since then someone else will be able to subclass ArithmeticModel without repeating
    the definitions of all the arithmetical fixed denotations terms.
    """
    fixed_denotations = dict()

    @property
    def domain(self):
        """Property that returns the domain of the model

        Is just syntactic sugar for ``model['domain']``

        Examples
        --------
        >>> from logics.classes.predicate.semantics import Model
        >>> model = Model({
        ...     'domain': {1, 2},
        ...     'a': 1,
        ...     'P': {1},
        ...     'R': {(1,1), (1,2)},
        ... })
        >>> model.domain
        {1, 2}
        """
        return self['domain']

    def denotation(self, term, free_variable_denotation_dict=None):
        """Takes a (possibly complex) term and returns its denotation

        *Always call* ``model.denotation(term)`` *instead of* ``model[term]``. The second might not work properly,
        especially for terms containing function symbols.

        Parameters
        ----------
        term: str or tuple
            A simple or complex term
        free_variable_denotation_dict: dict, optional
            You can pass an asignation (a dict specifying the denotations of variables).

        Raises
        ------
        logics.classes.exceptions.DenotationError
            If the term given as input does not have a denotation assigned

        Examples
        --------
        >>> from logics.classes.predicate.semantics import Model
        >>> model = Model({
        ...     'domain': {1, 2},
        ...     'a': 1,
        ...     'b': 2,
        ...     'P': {1},
        ...     'R': {(1,1), (1,2)},
        ...     'f': {((1,), 2), ((2,), 1)},
        ...     'g': {((1, 1), 1), ((1, 2), 2), ((2, 1), 1), ((2, 2), 2)}
        ... })
        >>> model.denotation('a')
        1
        >>> model.denotation('P')
        {1}
        >>> model.denotation('f')
        {((2,), 1), ((1,), 1)}
        >>> model.denotation(('f', 'a'))
        2
        >>> model.denotation(('f', ('f', 'a')))
        1
        >>> model.denotation(('g', ('f', 'a'), ('f', 'b')))
        1
        >>> model.denotation('1')
        Traceback (most recent call last):
        ...
        logics.classes.exceptions.DenotationError: Term 1 does not have a denotation assigned

        Giving a free variable denotation dict

        >>> model.denotation(('f', 'x'))  # variable without assignment
        Traceback (most recent call last):
        ...
        logics.classes.exceptions.DenotationError: Term x does not have a denotation assigned
        >>> model.denotation(('f', 'x'), {'x': 1})  # variable with assignment
        2

        Note that fixed denotations of the model class will be respected

        >>> from logics.instances.predicate.model_subclasses import ArithmeticModel
        >>> from itertools import count
        >>> arithmetic_model = ArithmeticModel({'domain': count(0)})
        >>> # The instance is empty except for the domain because every term has a default denotation in arithmetic
        >>> arithmetic_model.denotation('0')
        0
        >>> arithmetic_model.denotation(('s', '0'))
        1
        >>> arithmetic_model.denotation(('+', ('s', '0'), ('s', '0')))
        2
        """
        if free_variable_denotation_dict is None:
            free_variable_denotation_dict = dict()

        if type(term) == str:
            # Fixed denotation items
            if term in self.fixed_denotations:
                return self.fixed_denotations[term]
            # Language items
            if term in self:
                return self[term]
            # Denotations for free variables (passed in the valuation function)
            elif term in free_variable_denotation_dict:
                return free_variable_denotation_dict[term]
            raise DenotationError(f'Term {term} does not have a denotation assigned')

        # If not a string, must be a tuple and is a complex term
        return self._complex_term_denotation(term, free_variable_denotation_dict)

    def _complex_term_denotation(self, term, free_variable_denotation_dict):
        # Complex terms (function symbol applied to a number of terms)
        # They come in a tuple. E.g. for g(x, f(y)), the formula will contain ('g', 'x', ('f', 'y'))
        # where the first element is the function symbol and the rest are the arguments
        function_symbol = term[0]
        arguments = term[1:]
        argument_denotations = tuple(self.denotation(arg, free_variable_denotation_dict) for arg in arguments)

        # The function denotation is a callable
        if callable(self.denotation(function_symbol)):
            return self.denotation(function_symbol)(*argument_denotations)
        # Otherwise it is a set of 2-tuples
        function_value = next(func_denot[1] for func_denot in self.denotation(function_symbol)
                              if func_denot[0] == argument_denotations)  # No dict bc we just need the function denot
        return function_value

    def predicate_variable_quantification_range(self, variable_arity):
        """Returns the quantification range of a predicate variable *as an iterator*

        If monadic, returns the powerset of the domain. If n-adic returns returns the powerset of D^2, etc.
        Note that it won't actually return a set but an iterator (makes it much faster for computing valuations).

        Examples
        --------
        >>> from logics.classes.predicate.semantics import Model
        >>> model = Model({'domain': {1, 2}})
        >>> iter1 = model.predicate_variable_quantification_range(variable_arity=1)
        >>> type(iter1)
        <class 'generator'>
        >>> for x in iter1:
        ...     print(x)
        set()
        {1}
        {2}
        {1, 2}
        >>> iter2 = model.predicate_variable_quantification_range(variable_arity=2)
        >>> for x in iter2:
        ...     print(x)
        set()
        {(1, 1)}
        {(1, 2)}
        {(2, 1)}
        {(2, 2)}
        {(1, 1), (1, 2)}
        {(1, 1), (2, 1)}
        {(1, 1), (2, 2)}
        {(1, 2), (2, 1)}
        {(1, 2), (2, 2)}
        {(2, 1), (2, 2)}
        {(1, 1), (1, 2), (2, 1)}
        {(1, 1), (1, 2), (2, 2)}
        {(1, 1), (2, 1), (2, 2)}
        {(1, 2), (2, 1), (2, 2)}
        {(1, 1), (1, 2), (2, 1), (2, 2)}
        """
        if variable_arity == 1:
            base_set = self.domain
        else:
            base_set = product(self.domain, repeat=variable_arity)

        def range_generator(base_set):
            yield set()
            num_elements = 0
            base_set2 = copy(base_set)
            for elem in base_set2:
                num_elements += 1
                base_set3 = copy(base_set)
                for combination in combinations(base_set3, num_elements):
                    yield set(combination)
        return range_generator(base_set)
        # This was shorter but had problems with len(base_set) when base_set was a generator
        # I could have changed above base_set = set(...) but that would be much slower:
        # return (set(subset) for subset in
        #         chain.from_iterable(combinations(base_set, r) for r in range(len(base_set)+1)))


# ----------------------------------------------------------------------------------------------------------------------
# ----------------------------------------------------------------------------------------------------------------------

class ModelTheory:
    """Classical model theory

    Parameters
    ----------
    language: language: logics.classes.predicate.PredicateLanguage or logics.classes.predicate.InfinitePredicateLanguage
        Instance of PredicateLanguage or InfinitePredicateLanguage
    truth_values: list
        A list of the truth values (which may be int, str, etc.). In the instances below I use strings.
    designated_value:
        a member of `truth_values`, should be the one that represents truth
    truth_function_dict: dict
        Dict containing the logical constants (str) as keys, and n-dimensional lists as values (for constants of arity
        n). Will also accept any indexable (things with a `__getitem__` method, e.g. numpy arrays)
        and any n-ary callable. The clause for atomic formulae must be given with the key ``'atomic'``, and take two
        parameters, for the predicate denotation and the term denotations (see below)
    sentential_constant_values_dict: dict
        Dict containing the sentential constans (str) as keys, and their truth values (members of `truth_values`) as
        values
    use_molecular_valuation_fast_version: bool, optional
        Implements a faster version of the molecular valuation function (e.g. if asked for a disjunction will return
        '1' with one true disjunct, without evaluating the other). In counterpart, it is less general, since it assumes
        the Kleene truth matrices. Defaults to ``False``.
    use_quantifier_fast_version: bool, optional
        Same as above for quantifiers. Assumes that the universal quantifier behaves as the K3 conjunction, and the
        existential quantifier as the K3 disjunction. Defaults to ``False``.

    Examples
    --------
    We define a model theory for second-order classical logic with 2 function symbols and sentential constants
    (also present as a predefined instance, see below)

    >>> from logics.classes.predicate.semantics.models import ModelTheory
    >>> from logics.instances.predicate.languages import classical_function_language
    >>> bivalued_truth_values = ['1', '0']
    >>> # The order is important for the lines below, see many-valued semantics
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
    ...     '∀': lambda *args: '0' if '0' in args else '1',  # remember that the value can be a callable
    ...     '∃': lambda *args: '1' if '1' in args else '0',
    ...     'atomic': lambda pred_denotation, term_denotations: '1' if term_denotations in pred_denotation else '0'
    ... }
    >>> model_theory = ModelTheory(language=classical_function_language,
    ...                            truth_values=['1', '0'],
    ...                            designated_value='1',
    ...                            truth_function_dict=classical_truth_functions,
    ...                            sentential_constant_values_dict={'⊥': '0', '⊤': '1'},
    ...                            use_molecular_valuation_fast_version=True,
    ...                            use_quantifier_fast_version=True)
    """
    def __init__(self, language, truth_values, designated_value, truth_function_dict,
                 sentential_constant_values_dict=None, use_molecular_valuation_fast_version=False,
                 use_quantifier_fast_version=False):
        if sentential_constant_values_dict is None:
            sentential_constant_values_dict = dict()
        # Check that the designated value is in truth values
        if designated_value not in truth_values:
            raise ValueError(f'Value {designated_value} is not in truth_values')
        # Check that every constant of the language receives a truth function
        for constant in language.constants():
            if constant not in truth_function_dict:
                raise ValueError(f'Constant {constant} did not receive a truth function')
        # Same for every quantifier
        for quantifier in language.quantifiers:
            if quantifier not in truth_function_dict:
                raise ValueError(f'Quantifier {quantifier} did not receive a truth function')
        # Same for every sentential constant
        for sc in language.sentential_constants:
            if sc not in sentential_constant_values_dict:
                raise ValueError(f'Sentential constant {sc} did not receive a truth value')

        self.language = language
        self.truth_values = truth_values
        self.designated_value = designated_value
        self.truth_function_dict = truth_function_dict
        self.sentential_constant_values_dict = sentential_constant_values_dict
        self.use_molecular_valuation_fast_version = use_molecular_valuation_fast_version
        self.use_quantifier_fast_version = use_quantifier_fast_version

    def apply_truth_function(self, constant, *args):
        """Gets the value of a truth function applied to a given set of arguments.

        Works independently of whether the truth function for the constant is a callable or an indexible.

        Examples
        --------
        >>> from logics.instances.predicate.model_semantics import classical_functional_model_semantics
        >>> classical_functional_model_semantics.apply_truth_function('~', '0')
        '1'
        >>> classical_functional_model_semantics.apply_truth_function('~', '1')
        '0'
        >>> classical_functional_model_semantics.apply_truth_function('∃', '0', '1', '0')
        '1'
        >>> classical_functional_model_semantics.apply_truth_function('∀', '0', '1', '0')
        '0'
        >>> classical_functional_model_semantics.apply_truth_function('atomic', {1, 2, 3}, 1)
        '1'
        >>> classical_functional_model_semantics.apply_truth_function('atomic', {(1, 1),(2, 1)}, (1, 2))
        '0'
        """
        # If the truth function is a callable (e.g. a Python function), simply pass the args
        if callable(self.truth_function_dict[constant]):
            return self.truth_function_dict[constant](*args)

        # If it is not a callable but is an indexible
        else:
            args = tuple(self.truth_values.index(x) for x in args)  # e.g. if values is [1, 0], (0, 1) turns into (1, 0)
            truth_table = copy(self.truth_function_dict[constant])
            for value_index in args:
                # If the tt is [[1, 1], [1, 0]] for the values [1, 0], calling with (0, 0) first turns into (1, 1) above
                # and then we get [1, 0] in the first run through this loop, and 0 in the second run
                truth_table = truth_table[value_index]
            return truth_table

    def valuation(self, formula, model, free_variable_denotation_dict=None):
        """Returns the valuation of a formula, given some valuations for the atomics.

        Parameters
        ----------
        formula: logics.classes.predicate.PredicateFormula
            The formula of which you want to know the valuation
        model: logics.classes.predicate.semantics.Model
            The model to use
        free_variable_denotation_dict: dict, optional
            You can pass an asignation (a dict specifying the denotations of variables). Most often you will want to
            leave this as ``None`` in this method.

        Raises
        ------
        logics.classes.exceptions.DenotationError
            If some term or variable within the formula given as input does not have a denotation assigned in the model

        Examples
        --------
        >>> from logics.classes.predicate.semantics import Model
        >>> from logics.utils.parsers.predicate_parser import classical_predicate_parser as parser
        >>> from logics.instances.predicate.model_semantics import classical_functional_model_semantics
        >>> model = Model({
        ...     'domain': {1, 2},
        ...     'a': 1,
        ...     'b': 2,
        ...     'P': {1},
        ...     'R': {(1,1), (1,2)},
        ...     'f': {((1,), 2), ((2,), 1)},
        ...     'g': {((1, 1), 1), ((1, 2), 2), ((2, 1), 1), ((2, 2), 2)}
        ... })
        >>> classical_functional_model_semantics.valuation(parser.parse("P(a)"), model)
        '1'
        >>> classical_functional_model_semantics.valuation(parser.parse("R(a, b)"), model)
        '1'
        >>> classical_functional_model_semantics.valuation(parser.parse("R(f(a), g(f(a), b))"), model)
        '0'
        >>> classical_functional_model_semantics.valuation(parser.parse("exists x (P(f(x)))"), model)
        '1'
        >>> classical_functional_model_semantics.valuation(parser.parse("forall X (exists x (X(f(x))))"), model)
        '0'

        Once again, if you have fixed denotations, the method will respect them

        >>> from itertools import count
        >>> from logics.instances.predicate.model_subclasses import ArithmeticModel
        >>> from logics.utils.parsers.predicate_parser import arithmetic_parser
        >>> from logics.instances.predicate.model_semantics import arithmetic_model_semantics
        >>> arithmetic_model = ArithmeticModel({'domain': count(0)})
        >>> arithmetic_model_semantics.valuation(arithmetic_parser.parse("s(0) > 0"), arithmetic_model)
        '1'
        >>> arithmetic_model_semantics.valuation(arithmetic_parser.parse("s(0) + s(0) = s(s(0))"), arithmetic_model)
        '1'
        >>> arithmetic_model_semantics.valuation(arithmetic_parser.parse("exists x (x = s(0))"), arithmetic_model)
        '1'  [Note that it returns because use_quantifier_fast_version is enabled. Otherwise it would get stuck]
        >>> arithmetic_model_semantics.valuation(arithmetic_parser.parse("exists x (s(x) = 0)"), arithmetic_model)
        [The program freezes, as it keeps looping through the natural numbers...]
        """
        if free_variable_denotation_dict is None:
            free_variable_denotation_dict = dict()

        # Atomic
        if formula.is_atomic:
            # Sentential constant
            if self.language.is_sentential_constant_string(formula[0]):
                return self.sentential_constant_values_dict[formula[0]]

            # n-ary predicate followed by n terms
            predicate = formula[0]
            predicate_denotation = model.denotation(predicate, free_variable_denotation_dict)
            # Denotations of the terms
            # 1-ary predicate
            if len(formula) == 2:
                term_denotations = model.denotation(formula[1], free_variable_denotation_dict)
                # Callable
                if callable(predicate_denotation):
                    return predicate_denotation(term_denotations)
            # >1-ary predicate
            else:
                term_denotations = tuple(model.denotation(x, free_variable_denotation_dict) for x in formula[1:])
                # Callable
                if callable(predicate_denotation):
                    return predicate_denotation(*term_denotations)
            # Non callable, apply the atomic valuation clause
            return self.apply_truth_function('atomic', predicate_denotation, term_denotations)

        # Molecular
        elif formula.main_symbol in self.language.constants():
            if self.use_molecular_valuation_fast_version:
                return self._molecular_valuation_fast_version(formula, model, free_variable_denotation_dict)

            subvaluations = tuple(self.valuation(subformula, model, free_variable_denotation_dict)
                                  for subformula in formula.arguments())
            return self.apply_truth_function(formula.main_symbol, *subvaluations)

        # Quantified
        else:
            quantifier = formula[0]
            variable = formula[1]

            # Quantification range
            if formula[2] == '∈':
                quantifier_range = model.denotation(formula[3], free_variable_denotation_dict)
                quantified_formula = formula[4]
            else:
                # Individual variable
                if self.language._is_valid_variable(variable, only_individual=True):
                    quantifier_range = model.domain
                # Predicate variable
                else:
                    variable_arity = self.language.arity(variable)
                    quantifier_range = model.predicate_variable_quantification_range(variable_arity)
                quantified_formula = formula[2]

            # Fast version (less general)
            if self.use_quantifier_fast_version:
                return self._quantifier_valuation_fast_version(quantifier, variable, quantifier_range,
                                                               quantified_formula, model, free_variable_denotation_dict)
            # Slow version (more general)
            else:
                subvaluations = list()
                for element in quantifier_range:
                    free_variable_denotation_dict[variable] = element  # Assign the element to the variable
                    subvaluations.append(self.valuation(quantified_formula, model, free_variable_denotation_dict))
                return self.apply_truth_function(quantifier, *subvaluations)

    def _molecular_valuation_fast_version(self, formula, model, free_variable_denotation_dict):
        """
        Fast version of valuation for molecular sentences.
        Faster but less general method (will not work for some systems) - see the comment above.
        """
        if formula.main_symbol == '~':
            inside_val = self.valuation(formula[1], model, free_variable_denotation_dict)
            if inside_val == '1':
                return '0'
            elif inside_val == 'i':
                return 'i'
            elif inside_val == '0':
                return '1'

        elif formula.main_symbol == '∧':
            val1 = self.valuation(formula[1], model, free_variable_denotation_dict)
            if val1 == '0':
                return '0'
            val2 = self.valuation(formula[2], model, free_variable_denotation_dict)
            if val2 == '0':
                return '0'
            elif val1 == '1' and val2 == '1':
                return '1'
            return 'i'

        elif formula.main_symbol == '∨':
            val1 = self.valuation(formula[1], model, free_variable_denotation_dict)
            if val1 == '1':
                return '1'
            val2 = self.valuation(formula[2], model, free_variable_denotation_dict)
            if val2 == '1':
                return '1'
            elif val1 == '0' and val2 == '0':
                return '0'
            return 'i'

        elif formula.main_symbol == '→':
            val1 = self.valuation(formula[1], model, free_variable_denotation_dict)
            if val1 == '0':
                return '1'
            val2 = self.valuation(formula[2], model, free_variable_denotation_dict)
            if val2 == '1':
                return '1'
            elif val1 == '1' and val2 == '0':
                return '0'
            return 'i'

        elif formula.main_symbol == '↔':
            val1 = self.valuation(formula[1], model, free_variable_denotation_dict)
            if val1 == 'i':
                return 'i'
            val2 = self.valuation(formula[2], model, free_variable_denotation_dict)
            if val2 == 'i':
                return 'i'
            elif val1 == val2:
                return '1'
            return '0'

    def _quantifier_valuation_fast_version(self, quantifier, variable, quantifier_range, quantified_formula,
                                           model, free_variable_denotation_dict):
        if free_variable_denotation_dict is None:
            free_variable_denotation_dict = dict()

        if quantifier == '∀':
            valuation = '1'
            for element in quantifier_range:
                free_variable_denotation_dict[variable] = element  # Assign the element to the variable
                subval = self.valuation(quantified_formula, model, free_variable_denotation_dict)
                if subval == '0':
                    return '0'
                elif subval == 'i':
                    valuation = 'i'
            return valuation

        if quantifier == '∃':
            valuation = '0'
            for element in quantifier_range:
                free_variable_denotation_dict[variable] = element  # Assign the element to the variable
                subval = self.valuation(quantified_formula, model, free_variable_denotation_dict)
                if subval == '1':
                    return '1'
                elif subval == 'i':
                    valuation = 'i'
            return valuation


# ----------------------------------------------------------------------------------------------------------------------
# ARITHMETIC TRUTH THEORY

class TruthPredicateModelTheory(ModelTheory):
    """Model theory class for systems with a truth predicate

    Subclasses from ModelTheory. Has two changes from it:

    * Sentential constants can now denote formulae instead of truth values. If it finds a constant like that,
      the valuation of the constant will equal the valuation of the denoted sentence
    * Modifies the atomic valuation clause in case of an atomic beginning with Tr. In that case it will decode the
      sentence using the parser provided and evaluate it

    Parameters
    ----------
    parser: logics.utils.parsers.predicate_parser.ArithmeticTruthParser
        The parser you wish to use, to decode sentences inside Tr predicates
    everything_else_in_ModelTheory
        Everything else in ModelTheory

    Attributes
    ----------
    liar_sentence: logics.classes.predicate.PredicateFormula
        The predicate formula representing the liar sentence (for convenience, so that you can do
        ``model_theory.liar_sentence``). By default it is ``PredicateFormula(['λ'])``

    Examples
    --------
    >>> from logics.utils.parsers.predicate_parser import arithmetic_truth_parser
    >>> from logics.instances.predicate.languages import arithmetic_truth_language
    >>> from logics.instances.predicate.model_semantics import predicate_classical_truth_functions
    >>> from logics.classes.predicate.semantics.models import TruthPredicateModelTheory
    >>> # Sentence λ denotes its own negation
    >>> sent_constants = {'λ': arithmetic_truth_parser.parse('~Tr(⌜λ⌝)')}
    >>> arithmetic_truth_model_semantics = TruthPredicateModelTheory(parser=arithmetic_truth_parser,
    ...                                                 language=arithmetic_truth_language,
    ...                                                 truth_values=['1', '0'], designated_value='1',
    ...                                                 truth_function_dict=predicate_classical_truth_functions,
    ...                                                 sentential_constant_values_dict=sent_constants,
    ...                                                 use_molecular_valuation_fast_version=True,
    ...                                                 use_quantifier_fast_version=True)

    With this, we can evaluate sentences containing the truth predicate:

    >>> from itertools import count
    >>> from logics.instances.predicate.model_subclasses import ArithmeticModel
    >>> standard_model = ArithmeticModel({'domain': count(0)})
    >>> arithmetic_truth_model_semantics.valuation(arithmetic_truth_parser.parse('Tr(⌜0=0+0⌝)'), standard_model)
    '1'
    >>> arithmetic_truth_model_semantics.valuation(arithmetic_truth_parser.parse('Tr(⌜Tr(⌜0=0⌝)⌝)'), standard_model)
    '1'

    And what you are now surely wondering:

    >>> arithmetic_truth_model_semantics.valuation(arithmetic_truth_model_semantics.liar_sentence, standard_model)
    Fatal Python error: Cannot recover from stack overflow.

    Basically what happens is:

    * The atomic clause for ``valuation`` is called with the sentence λ
    * It sees that it is a sentential constant so it looks up what it denotes
    * It sees that it denotes a formula, namely, ~Tr(⌜λ⌝), so it recursively calls ``valuation`` with it
    * ``valuation`` is called with ~Tr(⌜λ⌝). It enters the negation clause, which calls ``valuation`` recursively in
      order to return the flipped value
    * ``valuation`` is called with Tr(⌜λ⌝). It enters the truth predicate clause of the atomic case.
      This decodes ⌜λ⌝ (which it internally sees as '79999') to λ, and evaluates it
    * Goes back to step 1 of the process

    This should raise a ``RecursionError`` but is currently giving me a stack overflow (I'm not sure why). But even if
    that worked, it wouldn't be very satisfactory, because it would give us the same error with any self-referential
    sentence even if it is not a problematic one. One thing we could try is to build some sort of kripkean fixed-point
    apparatus to deal with this. I leave it as future work.
    """
    liar_sentence = PredicateFormula(['λ'])

    def __init__(self, parser, *args, **kwargs):
        self.parser = parser
        super().__init__(*args, **kwargs)

    def valuation(self, formula, model, free_variable_denotation_dict=None):
        """ Two changes:
        - Sentential constants can now denote formulae, so return their valuation
        - Truth predicate sentences get evaluated differently
        """
        if formula.is_atomic:
            if self.language.is_sentential_constant_string(formula[0]):
                # Constant denotes a truth value
                if self.sentential_constant_values_dict[formula[0]] in self.truth_values:
                    return self.sentential_constant_values_dict[formula[0]]
                # Constant denotes a formula
                return self.valuation(self.sentential_constant_values_dict[formula[0]], model,
                                      free_variable_denotation_dict)

            if formula[0] == 'Tr':
                argument_code = formula[1]
                argument_formula_unparsed = self.parser.godel_decode(argument_code)
                argument_formula_parsed = self.parser.parse(argument_formula_unparsed)
                return self.valuation(argument_formula_parsed, model)  # No dict, the argument is isolated

        return super().valuation(formula, model, free_variable_denotation_dict)


# ----------------------------------------------------------------------------------------------------------------------
# ----------------------------------------------------------------------------------------------------------------------
# CLASSES FOR MANY-VALUED PREDICATE SEMANTICS

# class ManyValuedModel(Model):
#     todo MODIFY THIS AND THE FOLLWING CLASSES
#     Extends the class from above. There are two main differences:
#
#     - Each predicate is assigned an extension and anti-extension (set of things that do not satisfy it)
#     In some systems, an element of the domain may belong to both the extension and anti-extension, or to neither
#     An anti-extension for a predicate P is introduced by adding a - to the key, e.g. model['P-']
#
#     - Terms may fail to denote. If a term fails to denote, model.denotation(term) will return None.
#     This may happen because:
#         - The language item is assigned None at initialization (e.g. model.denotation('a') = None)
#         - You ask for the denotation of a complex term f(a, b, c) and one of a, b, c... fails to denote
#         - All arguments denote but the function doesn't have a value assigned for that tuple of args (partial func)
#     def antiextension(self, predicate_string):
#         """Takes a predicate and returns its antiextension"""
#         return self[predicate_string + '-']
#
#     def _complex_term_denotation(self, term, **kwargs):
#         function_symbol = term[0]
#         function_denotation = self.denotation(function_symbol)  # no kwargs necessary
#         if function_denotation is None:
#             return None
#
#         arguments = term[1:]
#         # Get the argument denotations. If one of the arguments fails to denote, return None
#         argument_denotations = list()
#         for arg in arguments:
#             arg_denotation = self.denotation(arg, **kwargs)
#             if arg_denotation is None:
#                 # No need to keep processing, return now
#                 return None
#             argument_denotations.append(arg_denotation)
#         argument_denotations = tuple(argument_denotations)
#
#         for argument_value in function_denotation:
#             if argument_value[0] == argument_denotations:
#                 return argument_value[1]
#         # If you looked at the entire function denotation and did not find the argument tuple, partial function
#         return None
#
#
# class MixedManyValuedModelTheory:
#     def __init__(self, language, truth_values, premise_designated_values, conclusion_designated_values,
#                  truth_function_dict, sentential_constant_values_dict):
#         pass
