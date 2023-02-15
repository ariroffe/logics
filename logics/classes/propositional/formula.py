"""
Classes for handling propositional formulae.
"""
from copy import deepcopy


class Formula(list):
    """Class for representing propositional formulae.

    The class Formula extends `list`. Every subformula within a Formula must also be a Formula.

        * Atomic formulae contain a single string element, e.g. ``Formula(['p'])``; ``Formula(['A'])``; ``Formula(['⊥'])``
        * Molecular formulae are always written in prefix notation, e.g. ``Formula(['∧', ['p'], ['~', ['q']]])``, which is read as `p ∧ ~q`

    Note that the `__init__` method of Formula will automatically turn lists within a Formula into Formula. Thus,
    you can write ``Formula(['~', ['p']])`` instead of ``Formula(['~', Formula(['p'])])``

    Examples
    --------
    >>> from logics.classes.propositional import Formula
    >>> f = Formula(['~', ['p']])
    >>> f[1]
    ['p']
    >>> type(f[1])
    <class 'logics.classes.propositional.formula.Formula'>

    Notes
    -----
    Working with Formula elements directly is somewhat uncomfortable and cumbersome. You may instead want to take a
    look at :doc:`parsers`. For random generation of formulae, see :doc:`formula_generators`
    """
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        for index in range(len(self)):
            argument = self[index]
            if type(argument) == list:
                argument = self.__class__(argument)
                self[index] = argument

    @property
    def is_atomic(self):
        """Returns ``True`` if the formula is atomic.

        Will consider a formula as an atomic if it is of length 1 (so as to not have to pass a Language as parameter).

        Examples
        --------
        >>> from logics.classes.propositional import Formula
        >>> Formula(['p']).is_atomic
        True
        >>> Formula(['~', ['p']]).is_atomic
        False
        """
        return len(self) == 1

    def arguments(self, quantifiers=None):
        """Returns a list of the arguments of a molecular formula, ``[]`` if it is an atomic.

        Examples
        --------
        >>> from logics.classes.propositional import Formula
        >>> Formula(['p']).arguments()
        []
        >>> Formula(['∧', ['p'], ['~', ['A']]]).arguments()
        [['p'], ['~', ['A']]]

        Notes
        -----
        `quantifiers` parameter is necessary because of how PredicateFormula works. Leave it as ``None`` here.
        """
        return self[1:]

    def is_schematic(self, language):
        """Returns ``True`` if the formula contains a metavariable of the language, ``False`` otherwise

        Examples
        --------
        >>> from logics.classes.propositional import Formula
        >>> from logics.instances.propositional.languages import classical_language
        >>> Formula(['p']).is_schematic(classical_language)
        False
        >>> Formula(['A']).is_schematic(classical_language)
        True
        >>> Formula(['∧', ['p'], ['~', ['A']]]).is_schematic(classical_language)
        True
        """
        if self.is_atomic:
            return language.is_metavariable_string(self[0])
        else:
            for argument in self.arguments():
                if argument.is_schematic(language):
                    return True
            return False

    @property
    def main_symbol(self):
        """Returns the first element if the formula is molecular, ``None`` if it is an atomic.

        Examples
        --------
        >>> from logics.classes.propositional import Formula
        >>> Formula(['p']).main_symbol is None
        True
        >>> Formula(['∧', ['p'], ['~', ['A']]]).main_symbol
        '∧'
        """
        if self.is_atomic:
            return None
        return self[0]

    @property
    def depth(self):
        """Depth of the formula.

        Examples
        --------
        >>> from logics.classes.propositional import Formula
        >>> Formula(['p']).depth
        0
        >>> Formula(['∧', ['p'], ['~', ['A']]]).depth
        2
        """
        if self.is_atomic:
            return 0
        return max(x.depth for x in [x for x in self if type(x) == type(self)]) + 1

    @property
    def level(self):
        # This is for calculating the level of metainferences, does nothing here
        return 0

    def is_well_formed(self, language):
        """Shortcut for ``language.is_well_formed(formula)``"""
        return language.is_well_formed(self)

    @property
    def subformulae(self):
        """Returns a list of the subformulae of the formula, without repetitions.

        Examples
        --------
        >>> from logics.classes.propositional import Formula
        >>> Formula(['p']).subformulae
        [['p']]
        >>> Formula(['∧', ['p'], ['~', ['A']]]).subformulae
        [['p'], ['A'], ['~', ['A']], ['∧', ['p'], ['~', ['A']]]]
        >>> Formula(["∧", ["p"], ["p"]]).subformulae  # p will only appear once
        [['p'], ['∧', ['p'], ['p']]]
        """
        return self._get_subformulae()

    def _get_subformulae(self, prev_sf=None):
        sf = prev_sf or []
        if not self.is_atomic:
            for argument in self:
                if type(argument) == self.__class__:
                    sf = argument._get_subformulae(sf)
        if self not in sf:
            sf.append(self)
        return sf

    def atomics_inside(self, language, prev_at=None):
        """Returns the set of the atomic letter strings (both propositional letters and metavariables) inside a formula.
        Sentential constants do not count.

        Examples
        --------
        >>> from logics.classes.propositional import Formula
        >>> from logics.instances.propositional.languages import classical_language
        >>> Formula(['∧', ['p'], ['~', ['A']]]).atomics_inside(classical_language)
        {'A', 'p'}
        """
        at = prev_at or set()
        if self.is_atomic:
            if not language.is_sentential_constant_string(self[0]):
                at.add(self[0])
            return at
        else:
            for argument in self[1:]:
                if type(argument) == self.__class__:
                    at = argument.atomics_inside(language, prev_at=at)
            return at

    def substitute(self, sf_to_substitute, sf_with):
        """Substitutes a subformula for another subformula.

        Will return a different ``Formula`` object, and not modify the original.

        The substituted one must match exactly, for example, calling ``Formula(['∧', ['p'], ['B']]).substitute``
        with arguments
        ``sf_to_substitute=Formula(['∧', ['A'], ['B']])`` and ``sf_with=Formula(['∧', ['B'], ['B']]`` will do nothing.
        See below for a different method that will do something with that.
        This method is also different from the ``PredicateFormula`` free variable substitution method.

        Parameters
        ----------
        sf_to_substitute: logics.classes.propositional.Formula
            The subformula you wish to substitute
        sf_with: logics.classes.propositional.Formula
            The subformula you wish to substitute it with

        Returns
        -------
        logics.classes.propositional.Formula
            A *different* formula instance from the original

        Examples
        --------
        >>> from logics.classes.propositional import Formula
        >>> f = Formula(['∧', ['p'], ['~', ['A']]])
        >>> f.substitute(Formula(['~', ['A']]), Formula(['~', ['p']]))
        ['∧', ['p'], ['~', ['p']]]
        >>> f
        ['∧', ['p'], ['~', ['A']]]
        """
        # If the entire formula is the one you want to substitute (e.g. you wish to substitute ['p'] for ['q'] in ['p'])
        if self == sf_to_substitute:
            return deepcopy(sf_with)  # This is just in case the user does something like f.substitute(..., f)

        substitution = self.__class__([self[0]])  # Leave [0] instead of .main_symbol bc it may be atomic
        # For molecular formulae, substitute the arguments
        for subelement in self[1:]:
            if isinstance(subelement, self.__class__):
                substitution.append(subelement.substitute(sf_to_substitute, sf_with))
            else:
                substitution.append(subelement)  # This will happen with the variables next to a quantifier in predicate
        return substitution

    def instantiate(self, language, subst_dict):
        """Given a schematic Formula, a language and a substitution dict, returns the schema instantiated with the dict.

        Will return a different Formula object, and not modify the original.

        Parameters
        ----------
        language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
            Instance of Language or InfiniteLanguage
        subst_dict: dict
            The susbstitution dict must have form ``{'A': someformula, 'B': someformula}``

        Returns
        -------
        logics.classes.propositional.Formula
            A *different* formula instance from the original

        Raises
        ------
        ValueError
            if some schematic propositional within the formula has no substitution assigned in the dictionary

        Examples
        --------
        >>> from logics.classes.propositional import Formula
        >>> from logics.instances.propositional.languages import classical_language
        >>> f = Formula(['∧', ['A'], ['B']])
        >>> f.instantiate(classical_language, {'A': Formula(['B']),
        ...                                    'B': Formula(['∧', ['~', ['B']], ['C']])})
        ['∧', ['B'], ['∧', ['~', ['B']], ['C']]]
        >>> f
        ['∧', ['A'], ['B']]
        >>> Formula(['∧', ['A'], ['B']]).instantiate(classical_language, {'A': Formula(['p'])})
        Traceback (most recent call last):
        ...
        ValueError: Metavariable B not present in substitution dict given
        """
        # Atomic
        if self.is_atomic:
            # Schematic atomic
            if language.is_metavariable_string(self[0]):
                if self[0] in subst_dict:
                    return subst_dict[self[0]]
                raise ValueError(f'Metavariable {self[0]} not present in substitution dict given')
            # Non-schematic atomic
            return deepcopy(self)

        # Molecular
        instantiation = self.__class__([self.main_symbol])
        for subelement in self[1:]:
            if isinstance(subelement, self.__class__):
                instantiation.append(subelement.instantiate(language, subst_dict))
            else:
                instantiation.append(subelement)
        return instantiation

    def schematic_substitute(self, language, schema_to_substitute, schema_with):
        """Takes a Formula and two schematic Formula, and substitutes any subformula instance of the first schema for
        the corresponding instance of the second schema.

        Will return a different Formula object, and not modify the original.

        Parameters
        ----------
        language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
            Instance of Language or InfiniteLanguage
        schema_to_substitute: logics.classes.propositional.Formula
            The schema of the subformula you wish to substitute
        schema_with: logics.classes.propositional.Formula
            The schema of the subformula you wish to substitute it with

        Returns
        -------
        logics.classes.propositional.Formula
            A *different* formula instance from the original

        Examples
        --------
        >>> from logics.classes.propositional import Formula
        >>> from logics.instances.propositional.languages import classical_language
        >>> f = Formula(['→', ['p'], ['→', ['p'], ['q']]])
        >>> f.schematic_substitute(classical_language, Formula(['→', ['A'], ['B']]),
        ...                                            Formula(['∨', ['~', ['A']], ['B']]))
        ['∨', ['~', ['p']], ['∨', ['~', ['p']], ['q']]]
        >>> f
        ['→', ['p'], ['→', ['p'], ['q']]]
        """
        if self.is_atomic:
            new_formula = deepcopy(self)  # Atomic PredicateFormula are not equal to self[0]
        else:
            new_formula = self.__class__([self[0]])

        # Molecular
        if not self.is_atomic:
            # First substitute the subformulae
            for subelement in self[1:]:
                if isinstance(subelement, self.__class__):
                    new_formula.append(subelement.schematic_substitute(language, schema_to_substitute, schema_with))
                else:
                    new_formula.append(subelement)

        # Once arguments have been substituted (or if the formula is atomic), substitute it
        instance, subst_dict = new_formula.is_instance_of(schema_to_substitute, language, return_subst_dict=True)
        if instance:
            new_formula = schema_with.instantiate(language, subst_dict)

        return new_formula

    def is_instance_of(self, formula, language, subst_dict=None, return_subst_dict=False, order=None):
        """Determines if a Formula is an instance of another (tipically schematic) Formula.

        For two non-schematic formulae, one is considered an instance of another iff they are equal.

        Has two optional parameters:

            * `return_subst_dict`: defaults to ``False``. If True, will return the substitution dict for `formula`'s
              metavariables. See below for an example.
            * `subst_dict`: defaults to ``None``. Can be given a substitution dict if some metavariable(s) are to be
              interpreted in some specific way.

        These parameters are useful in other modules, e.g. for checking correct instantiation of rules,
        where you tipically first check the conclusion, return a susbstitution dict, and use that substitution dict to
        check the premises of the rule. See below for some examples.

        Parameters
        ----------
        formula: logics.classes.propositional.Formula
            The (schematic) Formula of which we want to know if it is instance
        language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
            Instance of Language or InfiniteLanguage
        subst_dict: dict, optional
            A susbstitution dict of the form ``{'A': someformula, 'B': someformula}``
        return_subst_dict: bool, optional
            If True will additionally return a substitution dict.
        order: NoneType, optional
            Is for the is_instance_of method of Inference. Does nothing here, you should not alter it.

        Examples
        --------
        >>> from logics.classes.propositional import Formula
        >>> from logics.instances.propositional.languages import classical_language
        >>> Formula(['~', ['p']]).is_instance_of(Formula(['A']), classical_language)
        True
        >>> Formula(['~', ['p']]).is_instance_of(Formula(['∨', ['A'], ['B']]), classical_language)
        False
        >>> Formula(['∨', ['~', ['p']], ['q']]).is_instance_of(Formula(['∨', ['A'], ['B']]),
        ...                                                    classical_language)
        True

        If we give it some substitution dict beforehand:

        >>> Formula(['p']).is_instance_of(Formula(['A']), classical_language,
        ...                               subst_dict={'A': Formula(['q'])})
        False
        >>> Formula(['p']).is_instance_of(Formula(['A']), classical_language,
        ...                               subst_dict={'A': Formula(['p'])})
        True

        If we ask it to return the substitution dict:

        >>> Formula(['∨', ['~', ['p']], ['q']]).is_instance_of(Formula(['∨', ['A'], ['B']]),
        ...                                                    classical_language,
        ...                                                    return_subst_dict=True)
        (True, {'A': ['~', ['p']], 'B': ['q']})
        """
        if subst_dict is None:
            subst_dict = dict()

        # Instance of a non-schematic formulae?
        # If they are equal return true (will happen, e.g. in the right disjunct of 'p v q' and 'A v q')
        if not formula.is_schematic(language):
            if self == formula:
                if not return_subst_dict:
                    return True
                return True, subst_dict

            else:
                if not return_subst_dict:
                    return False
                return False, subst_dict

        # Atomic metavariable
        if formula.is_atomic:
            return self._is_atomic_instance_of(formula, language, subst_dict, return_subst_dict)
        # Molecular metavariable
        return self._is_molecular_instance_of(formula, language, subst_dict, return_subst_dict)

    def _is_atomic_instance_of(self, formula, language, subst_dict, return_subst_dict):
        # The case of atomic non-schematic formulae is handled above. Here we can assume the atomic is schematic
        # Check if there was a previous substitution of the same metavariable
        if formula[0] in subst_dict:
            if not return_subst_dict:
                return subst_dict[formula[0]] == self
            return subst_dict[formula[0]] == self, subst_dict

        # If there is no previous substitution, it is an instance
        if not return_subst_dict:
            return True
        # If you have to return a substitution dict, add this substitution instance
        subst_dict[formula[0]] = self
        return True, subst_dict

    def _is_molecular_instance_of(self, formula, language, subst_dict, return_subst_dict):
        # Check that the main symbol is the same, and that the arguments are instances
        if self.main_symbol == formula.main_symbol and len(self) == len(formula):
            for argument_index in range(len(self.arguments(language.quantifiers))):
                self_argument = self.arguments(language.quantifiers)[argument_index]
                formula_argument = formula.arguments(language.quantifiers)[argument_index]
                result = self_argument.is_instance_of(formula_argument, language, subst_dict, return_subst_dict=True)
                # The argument is not instance of the formula schema's argument
                if not result[0]:
                    if not return_subst_dict:
                        return False
                    return False, subst_dict
                # It is an instance, update the substitution dict
                subst_dict.update(result[1])

            # If the loop finishes, every argument is an instance
            if not return_subst_dict:
                return True
            return True, subst_dict

        # If you did not return up to now, it is because it is not an instance
        if not return_subst_dict:
            return False
        return False, subst_dict
