"""
Classes for defining a predicate language
"""
from itertools import chain

from logics.classes.propositional.language import Language, InfiniteLanguage


class PredicateLanguage(Language):
    """Class for predicate languages with a finite number of predicates and individual constants.

    Extends `logics.classes.propositional.Language`, adding some extra parameters and methods.
    It is safer to use single character strings for each of the parameters. In the parser you will be able to use longer
    strings. Needless to say, do not repeat any strings among the parameters.

    Parameters
    ----------
    individual_constants: list of str, optional
        A list of strings (valid letters for individual constants). Can also be a callable (a function).
    variables: list of str, optional
        A list of strings (valid letters for variables). Will consider any variable + a digit a valid variable. Are part
        of the base language, can appear quantified over in non-schematic formulae.
    individual_metavariables: list of str, optional
        A list of strings. Can be instantiated with either variables or ind cts. Are part of the metalanguage, any
        formula containing them is schematic. Useful for formulating rules.
    quantifiers: list of str, optional
        A list of strings (valid letters for quantifiers)
    metavariables: list of str, optional
        A list of strings (valid letters for atomic metavariables)
    constant_arity_dict: dict, optional
        a dictionary that contains `str` (logical cosntant symbols) as keys, and positive `int` (arities) as values
    predicate_letters: dict, optional
        a dictionary that contains `str` (predicate letter symbols) as keys, and positive `int` (arities) as values
    predicate_variables: dict, optional
        a dictionary that contains `str` (predicate variable symbols) as keys, and positive `int` (arities) as values.
        Will consider any variable + a digit a valid variable. Are part of the base language, , can appear quantified
        over in non-schematic formulae.
    predicate_metavariables: dict, optional
        a dictionary that contains `str` (predicate variable symbols) as keys, and positive `int` (arities) as values.
        Can be instantiated with either predicate letters or predicate variables. Are part of the metalanguage, any
        formula containing them is schematic. Useful for formulating rules.
    function_symbols: dict, optional
        a dictionary that contains `str` (function symbols) as keys, and positive `int` (arities) as values
    sentential_constants: list of str, optional
        A list of strings (representing sentential constants)
    allow_predicates_as_terms: bool, optional
        If true, if P is a predicate, allows one to say things like ∀x ∈ P (Formula). Defaults to ``False``

    Examples
    --------
    Example language containing all of the above

    >>> from logics.classes.predicate import PredicateLanguage
    >>> language = PredicateLanguage(individual_constants=['a', 'b', 'c', 'd'],
    ...                              variables=['x', 'y', 'z'],
    ...                              quantifiers=['∀', '∃'],
    ...                              metavariables=['A', 'B', 'C'],
    ...                              constant_arity_dict={'~': 1, '∧': 2, '∨': 2, '→': 2, '↔': 2},
    ...                              predicate_letters={'P': 1, 'Q': 1, 'R': 2, 'S': 3},
    ...                              predicate_variables={'X': 1, 'Y': 1, 'Z': 2},
    ...                              sentential_constants=['⊥', '⊤'],
    ...                              function_symbols={'f': 1, 'g': 2})

    Language of second-order arithmetic

    >>> arithmetic_language = PredicateLanguage(individual_constants=['0'],
    ...                                         variables=['x', 'y', 'z'],
    ...                                         quantifiers=['∀', '∃'],
    ...                                         metavariables=['A', 'B', 'C'],
    ...                                         constant_arity_dict={'~': 1, '∧': 2, '∨': 2, '→': 2, '↔': 2},
    ...                                         predicate_letters={'=': 2, '>': 2, '<': 2},
    ...                                         predicate_variables={'X': 1, 'Y': 1, 'Z': 2},
    ...                                         function_symbols={'s': 1, '+': 2, '*': 2, '**': 2})

    Examples of methods present because we are extending the propositional Language class

    >>> arithmetic_language.constants(1)
    {'~'}
    >>> arithmetic_language.is_metavariable_string('A')
    True
    >>> from logics.classes.predicate import PredicateFormula
    >>> arithmetic_language.is_well_formed(PredicateFormula(['~', ['=', ('s', '0'), '0']]))
    True
    >>> arithmetic_language.is_well_formed(PredicateFormula(['~', '~', ['=', ('s', '0'), '0']]))
    False
    >>> arithmetic_language.is_well_formed(PredicateFormula(['~', '~', ['=', ('s', '0'), '0']]), return_error=True)
    (False, "['~', '~', ['=', ('s', '0'), '0']] is not well-formed: Number of arguments does not coincide with the arity of the logical constant")

    Even in finite ``PredicateLanguage``'s there is always an infinite supply of both individual and predicate variables

    >>> language.is_well_formed(PredicateFormula(['P', 'x']))
    True
    >>> language.is_well_formed(PredicateFormula(['P', 'x23']))
    True
    >>> language.is_well_formed(PredicateFormula(['X', 'x23']))
    True
    >>> language.is_well_formed(PredicateFormula(['X1', 'x23']))
    True

    Parameter `individual_constants` can also be a callable. For instance:

    >>> # The arithmetic language defined above has only '0' as its individual constant
    >>> arithmetic_language.is_well_formed(PredicateFormula(['=', '0', '0']))
    True
    >>> arithmetic_language.is_well_formed(PredicateFormula(['=', '1', '1']))
    False
    >>> # To define an arithmetical language with all numerals, we can pass a function to individual_constants
    >>> arithmetic_numeral_language = PredicateLanguage(individual_constants=lambda x: x.isdigit(),
    ...                                                 # Not the best way to do it, but simple for illustration
    ...                                                 variables=['x', 'y', 'z'],
    ...                                                 quantifiers=['∀', '∃'],
    ...                                                 metavariables=['A', 'B', 'C'],
    ...                                                 constant_arity_dict={'~': 1, '∧': 2, '∨': 2, '→': 2, '↔': 2},
    ...                                                 predicate_letters={'=': 2, '>': 2, '<': 2},
    ...                                                 predicate_variables={'X': 1, 'Y': 1, 'Z': 2},
    ...                                                 function_symbols={'s': 1, '+': 2, '*': 2, '**': 2})
    >>> arithmetic_numeral_language.is_well_formed(PredicateFormula(['=', '0', '0']))
    True
    >>> arithmetic_numeral_language.is_well_formed(PredicateFormula(['=', '1', '1']))
    True
    """


    def __init__(self, individual_constants=None, variables=None, individual_metavariables=None, quantifiers=None,
                 metavariables=None, constant_arity_dict=None, predicate_letters=None, predicate_variables=None,
                 predicate_metavariables=None, function_symbols=None, sentential_constants=None,
                 allow_predicates_as_terms=False):
        self.atomics = None  # Used in (propositional) Language but not here
        self.individual_constants = individual_constants or []
        self.variables = variables or []
        self.individual_metavariables = individual_metavariables or []
        self.quantifiers = quantifiers
        self.metavariables = metavariables or []
        self.constant_arity_dict = constant_arity_dict or {}
        self.predicate_letters = predicate_letters or {}
        self.predicate_variables = predicate_variables or {}
        self.predicate_metavariables = predicate_metavariables or {}
        self.function_symbols = function_symbols or {}
        self.sentential_constants = sentential_constants or []
        self.allow_predicates_as_terms = allow_predicates_as_terms  # To be able to say things like ∀x ∈ P (Formula)

    def predicates(self, arity=None):
        """Returns the set of predicates of a given arity. If `arity` is ``None``, will return the set of all predicates

        Examples
        --------
        >>> from logics.instances.predicate.languages import classical_predicate_language
        >>> classical_predicate_language.predicates(1)
        {'P', 'Q'}
        >>> classical_predicate_language.predicates()
        {'R', 'S', 'P', 'Q'}
        """
        if arity is None:
            return set(self.predicate_letters)
        else:
            return {c for c in self.predicate_letters if self.predicate_letters[c] == arity}

    def arity(self, string):
        """Overriden from the base class to include the arities of predicate letters/variables/metavariables and
        function symbols

        Raises
        ------
        KeyError
            If the string is not present in any of those parameters

        Examples
        --------
        >>> from logics.instances.predicate.languages import classical_function_language
        >>> classical_function_language.arity('~')
        1
        >>> classical_function_language.arity('∧')
        2
        >>> classical_function_language.arity('P')  # predicate letter
        1
        >>> classical_function_language.arity('Z')  # predicate variable
        2
        >>> classical_function_language.arity('f')  # function symbol
        1
        >>> classical_function_language.arity('Π')  # predicate metavariable
        1
        """
        if string in self.constant_arity_dict:
            return self.constant_arity_dict[string]
        elif string in self.predicate_letters:
            return self.predicate_letters[string]
        elif string in self.predicate_metavariables:
            return self.predicate_metavariables[string]
        elif string in self.function_symbols:
            return self.function_symbols[string]
        # Predicate variables can contain a digit afterwards
        for v in self.predicate_variables:
            if string == v:
                return self.predicate_variables[v]
            # We assume that X1 has the same arity as X
            if string[:len(v)] == v and string[len(v):].isdigit():
                return self.predicate_variables[v]
        raise ValueError(f'Incorrect symbol {string}, does not have arity')

    def _is_term_well_formed(self, term):
        # Strings (can be either individual constants or variables)
        if type(term) == str:
            if self.allow_predicates_as_terms and \
                    (term in self.predicate_letters or term in self.predicate_variables or
                     term in self.function_symbols):
                return True
            return self._is_valid_individual_constant_or_variable(term)  # includes individual metavariables

        # If not a string, it must be a tuple, of the form ('f', term, term, ...)
        else:
            # Check that the first element is a function symbol
            function_symbol = term[0]
            if not self._is_valid_function_symbol(function_symbol):
                return False
            # Check the arity
            arity = self.arity(function_symbol)
            if len(term) != arity + 1:
                return False
            # Check the subterms
            for subterm in term[1:]:
                if not self._is_term_well_formed(subterm):
                    return False
            return True

    def _is_atomic_well_formed(self, formula, return_error):
        # Sentential metavariables and constants
        if formula[0] in self.metavariables or self.is_sentential_constant_string(formula[0]):
            if not return_error:
                return True
            return True, ''

        # n-ary predicate followed by n valid terms
        predicate = formula[0]
        if not self._is_valid_predicate(predicate):
            if not return_error:
                return False
            return False, f'{formula} is not well-formed: {predicate} is not a valid predicate'
        arity = self.arity(predicate)
        if len(formula) != arity + 1:
            if not return_error:
                return False
            return False, f'{formula} is not well-formed: Incorrect number of arguments ' \
                          f'for {arity}-ary predicate {predicate}'
        for term in formula[1:]:
            if not self._is_term_well_formed(term):
                if not return_error:
                    return False
                return False, f'{formula} is not well-formed: Term {term} is not well-formed'

        if not return_error:
            return True
        return True, ''

    def _is_molecular_well_formed(self, formula, return_error):
        # We only need to take into account the case of quantified formulae, the rest is the same
        if formula.main_symbol in self.quantifiers:
            if not self._is_valid_variable(formula[1], allow_metavariables=True):  # includes ind and pred metavariables
                if not return_error:
                    return False
                return False, f'{formula} is not well-formed: {formula[1]} is not a valid variable'
            # Bounded quantifier
            if formula[2] == '∈':
                if not self._is_term_well_formed(formula[3]):
                    if not return_error:
                        return False
                    return False, f'{formula} is not well-formed: Quantifier bound {formula[3]} is not a term'
                return self.is_well_formed(formula[4], return_error)
            # Non-bounded quantifier
            else:
                return self.is_well_formed(formula[2], return_error)

        # Non-quantified cases, call the super method
        return super()._is_molecular_well_formed(formula, return_error)

    def is_atomic_string(self, string):
        raise ValueError('Method only available in propositional languages')

    def _is_valid_predicate(self, string):
        return self._is_valid_variable(string, only_predicate=True, allow_metavariables=True) or \
            string in self.predicate_letters or \
            string in self.predicate_metavariables

    def _is_valid_function_symbol(self, string):
        return string in self.function_symbols

    def is_valid_individual_constant(self, string):
        if string in self.individual_metavariables:
            return True
        if callable(self.individual_constants):
            return self.individual_constants(string)
        return string in self.individual_constants

    def _is_valid_variable(self, string, only_individual=False, only_predicate=False, allow_metavariables=True):
        """There is always an infinite supply of both individual and predicate variables"""
        if only_individual and only_predicate:
            raise ValueError("only_individual and only_predicate parameters cannot be both True")
        elif only_individual:
            bound = self.variables
            meta_bound = self.individual_metavariables
        elif only_predicate:
            bound = self.predicate_variables
            meta_bound = self.predicate_metavariables
        else:
            bound = chain(self.variables, self.predicate_variables)
            meta_bound = chain(self.individual_metavariables, self.predicate_metavariables)
        for vv in bound:
            if string == vv:
                return True
            if string[:len(vv)] == vv and string[len(vv):].isdigit():
                return True
        if allow_metavariables:
            for mv in meta_bound:
                if string == mv:
                    return True
                # these canot have digits after
        return False

    def _is_valid_individual_constant_or_variable(self, string):
        return self.is_valid_individual_constant(string) or self._is_valid_variable(string, only_individual=True,
                                                                                    allow_metavariables=True)

    def is_metavariable_string(self, string):
        """Determines if a string is among the (individual/predicate/formula) metavariables of the language."""
        return string in self.metavariables or \
            string in self.individual_metavariables or \
            string in self.predicate_metavariables


class InfinitePredicateLanguage(PredicateLanguage, InfiniteLanguage):
    """Language that also considers expressions to be well-formed in case a variable, individual
    constant or metavariable is followed by a digit

    Examples
    --------
    >>> from logics.classes.predicate import InfinitePredicateLanguage, PredicateFormula
    >>> language = InfinitePredicateLanguage(individual_constants=['a', 'b', 'c', 'd'],
    ...                                      variables=['x', 'y', 'z'],
    ...                                      quantifiers=['∀', '∃'],
    ...                                      metavariables=['A', 'B', 'C'],
    ...                                      constant_arity_dict={'~': 1, '∧': 2, '∨': 2, '→': 2, '↔': 2},
    ...                                      predicate_letters={'P': 1, 'Q': 1, 'R': 2, 'S': 3},
    ...                                      predicate_variables={'X': 1, 'Y': 1, 'Z': 2})
    >>> language.is_well_formed(PredicateFormula(['P', 'a']))
    True
    >>> language.is_well_formed(PredicateFormula(['P', 'a23']))
    True
    >>> language.is_well_formed(PredicateFormula(['P1', 'a23']))
    True
    >>> language.is_well_formed(PredicateFormula(['A1']))
    True
    """
    # Inherits from InfiniteLanguage only to have the overloaded is_metavariable_string method

    def arity(self, string):
        # We consider only the case of predicate letters
        for v in self.predicate_letters:
            if string == v:
                return self.predicate_letters[v]
            # We assume that P1 has the same arity as P
            if string[:len(v)] == v and string[len(v):].isdigit():
                return self.predicate_letters[v]
        return super().arity(string)

    def _is_valid_predicate(self, string):
        if string in self.predicate_metavariables:
            return True
        for pred in chain(self.predicate_letters, self.predicate_variables):
            if string == pred:
                return True
            if string[:len(pred)] == pred and string[len(pred):].isdigit():
                return True
        return False

    def _is_valid_individual_constant_or_variable(self, string):
        if super()._is_valid_individual_constant_or_variable(string):
            return True
        if not callable(self.individual_constants):
            for c in self.individual_constants:
                if string[:len(c)] == c and string[len(c):].isdigit():
                    return True
        return False


class TruthPredicateLanguage(PredicateLanguage):
    """Language for arithmetic containing a truth predicate

    Subclasses PredicateLanguage but has a special clause for ``is_well_formed``, which states that atomic formulae that
    begin with predicate ``'Tr'`` must have a numeral as its only argument. I.e. truth predicate atomics must be of the
    form ``PredicateFormula(['Tr', '514951'])``
    """
    def _is_atomic_well_formed(self, formula, return_error):
        if formula[0] == 'Tr':
            if len(formula) != 2:
                if not return_error:
                    return False
                return False, f'{formula} is not well-formed: Incorrect number of arguments for 1-ary predicate Tr'
            # Check that the argument is a numeral
            try:
                int(formula[1])
                if not return_error:
                    return True
                return True, ''
            except ValueError:
                if not return_error:
                    return False
                return False, f'Argument in {formula} is not a numeral'
        return super()._is_atomic_well_formed(formula, return_error)
