from logics.classes.exceptions import NotWellFormed


class Language:
    """Class for propositional languages with a finite number of atomics.

    Parameters
    ----------
    atomics: list of str, optional
        A list of strings (valid letters for atomics)
    constant_arity_dict: dict, optional
        a dictionary that contains `str` (logical cosntant symbols) as keys, and positive `int` (arities) as values
    sentential_constants: list of str, optional
        A list of strings (representing sentential constants)
    metavariables: list of str, optional
        A list of strings (valid letters for atomic metavariables)
    context_variables: list of str, optional
        A list of strings (representing context variables, i.e. sequences of formulae). Used mainly in sequent calculi

    Notes
    -----
    Do not repeat symbols among any of the parameters above.
    It is preferable to use single character strings for each.
    If you want longer strings, you will be able to use them in the parser

    Examples
    --------
    A propositional language containing 3 atomics, negation and conjunction, and some context variables:

    >>> from logics.classes.propositional import Language
    >>> language = Language(atomics=['p', 'q', 'r'],
    ...                     constant_arity_dict={'~': 1, '∧': 2},
    ...                     sentential_constants=['⊥', '⊤'],
    ...                     metavariables=['A', 'B', 'C'],
    ...                     context_variables=['Γ', 'Δ', 'Σ', 'Λ', 'Π', 'Θ'])
    """
    def __init__(self, atomics=None, constant_arity_dict=None, sentential_constants=None, metavariables=None,
                 context_variables=None):
        self.atomics = atomics or []
        self.metavariables = metavariables or []
        self.constant_arity_dict = constant_arity_dict or {}
        self.sentential_constants = sentential_constants or []
        self.context_variables = context_variables or []
        self.quantifiers = []  # Necessary to avoid bugs when subclassing this with PredicateLanguage

    def arity(self, constant):
        """Returns the arity of a logical constant.

        Raises
        ------
        KeyError
            If the string is not present in `constant_arity_dict`

        Examples
        --------
        >>> from logics.instances.propositional.languages import classical_language
        >>> classical_language.arity('~')
        1
        >>> classical_language.arity('∧')
        2
        """
        return self.constant_arity_dict[constant]

    def constants(self, arity=None):
        """Returns the set of logical constants of a given arity. If `arity` is ``None``, will return the set of all
        logical constants

        Examples
        --------
        >>> from logics.instances.propositional.languages import classical_language
        >>> classical_language.constants(1)
        {'~'}
        >>> classical_language.constants()
        {'∧', '→', '∨', '~', '↔'}
        """
        if arity is None:
            return set(self.constant_arity_dict)
        else:
            return {c for c in self.constant_arity_dict if self.constant_arity_dict[c] == arity}

    def is_well_formed(self, formula, return_error=False):
        """Determines if a formula is well-formed for the Language.

        Parameters
        ----------
        formula: logics.classes.propositional.Formula
            an instance of Formula
        return_error: bool
            If ``True``, will return a tuple containing (`bool`, `str`). The `str` contains an informative message
            detailing why the formula is not well-formed, in case it isn't. Otherwise the `str` is ``''`` . If ``False``
            (default value) the method will just return a boolean.

        Examples
        --------
        >>> from logics.instances.propositional.languages import classical_language
        >>> from logics.classes.propositional import Formula
        >>> classical_language.is_well_formed(Formula(['p']))
        True
        >>> classical_language.is_well_formed(Formula(['~', ['p']]))
        True
        >>> classical_language.is_well_formed(Formula(['~', ['~', ['p']]]))
        True
        >>> classical_language.is_well_formed(Formula(['~', ['~', ['p']]]), return_error=True)
        (True, '')
        >>> classical_language.is_well_formed(Formula(['~', '~', ['p']]))
        False
        >>> classical_language.is_well_formed(Formula(['~', '~', ['p']]), return_error=True)
        (False, "['~', '~', ['p']] is not well-formed: Number of arguments does not coincide with the arity of the logical constant")

        See Also
        --------
        logics.classes.propositional.Formula
        """
        # Atomic formulae
        if formula.is_atomic:
            return self._is_atomic_well_formed(formula, return_error)
        # Molecular formulae
        return self._is_molecular_well_formed(formula, return_error)

    def _is_atomic_well_formed(self, formula, return_error):
        if not self.is_atomic_string(formula[0]) and not self.is_metavariable_string(formula[0]) and \
                not self.is_sentential_constant_string(formula[0]):
            if not return_error:
                return False
            return False, f'{formula} is not well-formed: {formula[0]} is not an atomic nor a ' \
                          f'sentential constant of the language'
        if not return_error:
            return True
        return True, ''

    def _is_molecular_well_formed(self, formula, return_error):
        if formula.main_symbol not in self.constants():
            if not return_error:
                return False
            return False, f'{formula} is not well-formed: ' \
                          f'First member of the list is not a logical constant of the language'

        arity = self.arity(formula.main_symbol)
        if len(formula.arguments()) != arity:
            if not return_error:
                return False
            return False, f'{formula} is not well-formed: ' \
                          f'Number of arguments does not coincide with the arity of the logical constant'

        for argument in formula.arguments():
            if not isinstance(argument, formula.__class__):
                if not return_error:
                    return False
                return False, f'{formula} is not well-formed: Argument {argument} is not a formula'
            if not self.is_well_formed(argument, return_error):
                if not return_error:
                    return False
                return False, f'{formula} is not well-formed: Argument {argument} is not a well-formed formula'

        if not return_error:
            return True
        return True, ''

    def is_atomic_string(self, string):
        """Determines if a string is among the atomics of the language. See below for some examples."""
        return string in self.atomics

    def is_sentential_constant_string(self, string):
        """Determines if a string is among the sentential constants of the language. See below for some examples."""
        return string in self.sentential_constants

    def is_metavariable_string(self, string):
        """Determines if a string is among the metavariables of the language. See below for some examples."""
        return string in self.metavariables

    def is_context_variable_string(self, string):
        """Determines if a string is among the context variables of the language

        Examples
        --------
        >>> from logics.instances.propositional.languages import classical_language_with_sent_constants
        >>> classical_language_with_sent_constants.is_atomic_string('p')
        True
        >>> classical_language_with_sent_constants.is_atomic_string('b')
        False
        >>> classical_language_with_sent_constants.is_sentential_constant_string('⊥')
        True
        >>> classical_language_with_sent_constants.is_metavariable_string('A')
        True
        >>> classical_language_with_sent_constants.is_metavariable_string('F')
        False
        >>> classical_language_with_sent_constants.is_context_variable_string('Γ')
        True
        """
        return string in self.context_variables


class InfiniteLanguage(Language):
    """Same as Language but with an indefinite supply of atomics and metavariables.

    Will consider a string in `atomics` + a digit a well-formed formula. Same with metavariables.

    Examples
    --------
    >>> from logics.classes.propositional import InfiniteLanguage
    >>> infinite_language = InfiniteLanguage(atomics=['p', 'q', 'r'],
    ...                                      constant_arity_dict={'~': 1, '∧': 2},
    ...                                      sentential_constants=['⊥', '⊤'],
    ...                                      metavariables=['A', 'B', 'C'])

    >>> infinite_language.is_atomic_string('p')
    True
    >>> infinite_language.is_atomic_string('p1')
    True
    >>> infinite_language.is_atomic_string('p234')
    True
    >>> infinite_language.is_metavariable_string('A')
    True
    >>> infinite_language.is_metavariable_string('A234')
    True

    >>> from logics.classes.propositional import Formula
    >>> infinite_language.is_well_formed(Formula(['p']))
        True
    >>> infinite_language.is_well_formed(Formula(['p234']))
        True
    >>> infinite_language.is_well_formed(Formula(['~', ['p234']]))
        True
    """
    def is_atomic_string(self, string):
        for at in self.atomics:
            if string == at:
                return True
            if string[:len(at)] == at and string[len(at):].isdigit():
                return True
        return False

    def is_metavariable_string(self, string):
        for mt in self.metavariables:
            if string == mt:
                return True
            if string[:len(mt)] == mt and string[len(mt):].isdigit():
                return True
        return False
