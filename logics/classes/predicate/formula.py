from logics.classes.propositional import Formula


class PredicateFormula(Formula):
    """Class for representing predicate formulae.

    Extends the propositional class ``Formula``, but has some differences:

    * Atomics are now of the form ``['R', 'a', 'x']``
    * When the terms are applied function symbols, they must come as tuples, where the first element of the tuple is the
      function symbol, and the following are its arguments, e.g. ``['R', ('f', ('f', 'x')), 'a']`` represents the
      formula ``R(f(f(x)), a)``
    * Now we have quantified formulae of the form ``['∀', 'x', PredicateFormula]``
    * Will also accept bounded quantified formulae of the form ``['∀', 'x', '∈', term, PredicateFormula]``

    As in ``Formula``, the ``__init__`` method will turn inner lists into ``PredicateFormula``, so you can write
    ``PredicateFormula(['~', ['P', 'x']])`` instead of ``PredicateFormula(['~', PredicateFormula(['P', 'x'])])``

    Examples
    --------
    >>> from logics.classes.predicate import PredicateFormula

    The following are examples of predicate formulae (and are well-formed for
    `logics.instances.predicate.languages.classical_function_language`):

    >>> PredicateFormula(['P', 'x'])
    >>> PredicateFormula(['∧', ['~', ['P', 'a']],['X', 'a']])
    >>> PredicateFormula(['R', 'a', 'b'])
    >>> PredicateFormula(['P', ('f', ('g', 'a', 'x'))])
    >>> PredicateFormula(['∀', 'x', ['P', 'x']])
    >>> PredicateFormula(['∃', 'x', ['∀', 'X', ['X', 'x']]])
    >>> PredicateFormula(['∀', 'x', '∈', ('f', 'a'), ['P', 'x']])

    Some properties and methods are available because we are extending ``Formula``

    >>> from logics.instances.predicate.languages import classical_function_language
    >>> PredicateFormula(['P', 'x']).is_schematic(classical_function_language)
    False
    >>> PredicateFormula(['∧', ['P', 'x'], ['A']]).is_schematic(classical_function_language)
    True
    >>> PredicateFormula(['∧', ['P', 'x'], ['A']]).main_symbol
    '∧'
    >>> PredicateFormula(['∃', 'x', ['∀', 'X', ['X', 'x']]]).depth
    2
    >>> PredicateFormula(['∃', 'x', ['∀', 'X', ['X', 'x']]]).subformulae
    [['X', 'x'], ['∀', 'X', ['X', 'x']], ['∃', 'x', ['∀', 'X', ['X', 'x']]]]
    >>> f = PredicateFormula(['∧', ['P', 'x'], ['A']])
    >>> f.substitute(PredicateFormula(['P', 'x']), PredicateFormula(['Q', 'x']))
    ['∧', ['Q', 'x'], ['A']]
    >>> f
    ['∧', ['P', 'x'], ['A']]
    >>> f.instantiate(classical_function_language, {'A': PredicateFormula(['P', 'a'])})
    ['∧', ['P', 'x'], ['P', 'a']]
    >>> f2 = PredicateFormula(['∧', ['P', 'x'], ['Q', 'x']])
    >>> f2.schematic_substitute(classical_function_language,
    ...                         PredicateFormula(['∧', ['A'], ['B']]),
    ...                         PredicateFormula(['∧', ['B'], ['A']]))
    ['∧', ['Q', 'x'], ['P', 'x']]
    """
    @property
    def is_atomic(self):
        """Same as in propositional ``Formula``. Overriden to work with this class.

        Examples
        --------
        >>> from logics.classes.predicate import PredicateFormula
        >>> PredicateFormula(['P', 'x']).is_atomic
        True
        >>> PredicateFormula(['∧', ['~', ['P', 'a']],['X', 'a']]).is_atomic
        False
        """
        #Predicate language atomics are those that have no members of the same class inside
        for subelement in self:
            if isinstance(subelement, self.__class__):
                return False
        return True

    def arguments(self, quantifiers=('∀', '∃')):
        """Same as in propositional ``Formula``. Overriden in order to accomodate quantified formulae.

        Examples
        --------
        >>> from logics.classes.predicate import PredicateFormula
        >>> PredicateFormula(['∧', ['P', 'x'], ['A']]).arguments()
        [['P', 'x'], ['A']]
        >>> PredicateFormula(['∃', 'x', ['∀', 'X', ['X', 'x']]]).arguments()
        [['∀', 'X', ['X', 'x']]]
        >>> PredicateFormula(['∃', 'x', '∈', 'y', ['∀', 'X', ['X', 'x']]]).arguments()
        [['∀', 'X', ['X', 'x']]]

        Notes
        -----
        If your language uses different quantifiers, pass them as a list of strings to the `quantifiers` parameter.
        """
        # Return only the immediate subformulae. Overriden so that ∀x Px returns only [Px], and not [x, Px].
        # By default assumes that the quantifiers are the standard ones, if you need different ones, pass a different
        # second parameter.
        if self[0] in quantifiers:
            if self[2] == '∈':
                return self[4:]
            return self[2:]
        return super().arguments()

    def free_variables(self, language, term=None, _bound_variables=None):
        """Returns the set of free variables inside a predicate formula or term

        if `term` is ``None`` will evaluate the whole formula. Otherwise, will only evaluate the term given.
        `_bound_variables` is internal and should not be altered.

        Examples
        --------
        >>> from logics.classes.predicate import PredicateFormula
        >>> from logics.instances.predicate.languages import classical_function_language
        >>> PredicateFormula(['∀', 'X', ['X', 'x']]).free_variables(classical_function_language)
        {'x'}
        >>> PredicateFormula(['∀', 'x', ['X', 'x']]).free_variables(classical_function_language)
        {'X'}
        >>> PredicateFormula(['∃', 'x', '∈', 'y', ['∀', 'X', ['X', 'x']]]).free_variables(classical_function_language)
        {'y'}
        >>> PredicateFormula(['∀', 'x', ['P', ('f', 'x')]]).free_variables(classical_function_language)
        set()
        >>> PredicateFormula(['∀', 'x', ['P', ('f', 'x')]]).free_variables(classical_function_language, term=('f', 'x'))
        {'x'}
        """
        free = set()
        if _bound_variables is None:
            _bound_variables = set()

        # Term
        if term is not None:
            # If you are evaluating a particular term (e.g. 'a' or ('f', ('g', 'x'))
            # Atomic term, e.g. 'a'
            if type(term) == str:
                if language._is_valid_variable(term) and term not in _bound_variables:
                    return {term}
                return set()
            # Molecular term ('f', ('g', 'x'))
            for subterm in term:
                free |= self.free_variables(language, term=subterm, _bound_variables=_bound_variables)
            return free

        # Atomic
        if self.is_atomic:
            # If you are evaluating the entire atomic formula, evaluate each argument (incl the predicate)
            for argument in self:
                free |= self.free_variables(language, term=argument, _bound_variables=_bound_variables)
            return free

        # Molecular
        if self.main_symbol in language.quantifiers:
            # In case of a bounded quantifier, check for free variables in the bound (before adding to the bounded)
            if self[2] == '∈':
                free |= self.free_variables(language, term=self[3], _bound_variables=_bound_variables)
            # Quantified formula: add the quantified variable to bound_variables
            _bound_variables |= {self[1]}
        # Return the varibles in each immediate subformula
        for subformula in self.arguments():
            free |= subformula.free_variables(language, _bound_variables=_bound_variables)
        return free

    def is_closed(self, language):
        """Determines if a formula is closed (i.e has no free variables)

        Examples
        --------
        >>> from logics.classes.predicate import PredicateFormula
        >>> from logics.instances.predicate.languages import classical_function_language
        >>> PredicateFormula(['∀', 'X', ['X', 'x']]).is_closed(classical_function_language)
        False
        >>> PredicateFormula(['∀', 'X', ['∀', 'x', ['X', 'x']]]).is_closed(classical_function_language)
        True
        """
        return self.free_variables(language) == set()

    def is_open(self, language):
        """Determines if a formula is open (i.e. has free variables)

        Examples
        --------
        >>> from logics.classes.predicate import PredicateFormula
        >>> from logics.instances.predicate.languages import classical_function_language
        >>> PredicateFormula(['∀', 'X', ['X', 'x']]).is_open(classical_function_language)
        True
        >>> PredicateFormula(['∀', 'X', ['∀', 'x', ['X', 'x']]]).is_open(classical_function_language)
        False
        """
        return not self.is_closed(language)

    def vsubstitute(self, variable, substitution, quantifiers=('∀', '∃'), term=None, _bound_variables=None):
        """Variable substitution method.

        Returns the PredicateFormula that results from substituting the free occurences of `variable` for
        `substitution`.

        Parameters
        ----------
        variable: str
            The variable whose free occurrences you wish to substitute
        substitution: str or tuple
            The term you wish to substitute it with
        quantifiers: tuple of str, optional
            By default, assumes that the quantifiers are '∀', '∃', so that you do not have to pass a language as
            argument; If you have different quantifiers, you can call this differently
            (e.g. ``quantifiers = your_language.quantifiers``)
        term: str or tuple, optional
            if you only wish to substitute inside a term, as in the `free_variables` method.
        _bound_variables
            Internal, you should not alter its value

        Examples
        --------
        >>> from logics.classes.predicate import PredicateFormula
        >>> PredicateFormula(['P', 'x']).vsubstitute('x', 'a')
        ['P', 'a']
        >>> PredicateFormula(['∀', 'x', ['P', 'x']]).vsubstitute('x', 'a')
        ['∀', 'x', ['P', 'x']]
        >>> PredicateFormula(['∧', ['P', 'x'], ['∀', 'x', ['P', 'x']]]).vsubstitute('x', 'a')
        ['∧', ['P', 'a'], ['∀', 'x', ['P', 'x']]]
        >>> PredicateFormula(['∀', 'x', ['X', 'x']]).vsubstitute('X', 'P')
        ['∀', 'x', ['P', 'x']]
        >>> PredicateFormula(['∀', 'X', ['X', 'a']]).vsubstitute('X', 'P')
        ['∀', 'X', ['X', 'a']]
        >>> # The bound is not under the scope of the quantifier:
        >>> PredicateFormula(['∀', 'x', '∈', ('f', 'x'), ['P', 'x']]).vsubstitute('x', 'b')
        ['∀', 'x', '∈', ('f', 'b'), ['P', 'x']]
        """
        if _bound_variables is None:
            _bound_variables = set()

        # Term
        if term is not None:
            # If you are substituting a particular term (e.g. 'a' or ('f', ('g', 'x'))
            # Atomic term, e.g. 'a'
            if type(term) == str:
                if term == variable and term not in _bound_variables:
                    return substitution
                return term
            # Molecular term ('f', ('g', 'x'))
            newterm = list()
            for subterm in term:
                newterm.append(self.vsubstitute(variable, substitution, quantifiers=quantifiers,
                                                term=subterm, _bound_variables=_bound_variables))
            return tuple(newterm)
        
        if self.is_atomic:
            # If you are evaluating the entire atomic formula, evaluate each argument (incl the predicate)
            new_formula = self.__class__()
            for argument in self:
                new_formula.append(self.vsubstitute(variable, substitution, quantifiers=quantifiers,
                                                    term=argument,
                                                    _bound_variables=_bound_variables))
            return new_formula

        # Molecular
        # First, copy everything that is not a subformula (connective, quantifier, variable, '∈', bound)
        new_formula = self.__class__([x for x in self if type(x) != self.__class__])
        if self.main_symbol in quantifiers:
            # In case of a bounded quantifier, substitute variables in the bound (before adding to the bounded)
            if self[2] == '∈':
                new_formula[3] = self.vsubstitute(variable, substitution, quantifiers=quantifiers, term=self[3],
                                                  _bound_variables=_bound_variables)
            # Quantified formula: add the quantified variable to bound_variables
            _bound_variables |= {self[1]}
        # Substitute each immediate subformula
        for subformula in self.arguments():
            new_formula.append(subformula.vsubstitute(variable, substitution, quantifiers=quantifiers,
                                                      _bound_variables=_bound_variables))
        return new_formula

    def _is_molecular_instance_of(self, formula, language, subst_dict, return_subst_dict):
        # We only need the quantifier case here, for the rest call the super method
        if self.main_symbol == formula.main_symbol and self.main_symbol in language.quantifiers:
            # Check that the variable is the same
            if self[1] != formula[1]:
                if not return_subst_dict:
                    return False
                return False, subst_dict

            # Bounded quantifier case
            if formula[2] == '∈':
                # The bounds must be equal (we do not presently have metavariables for terms)
                if self[2] != '∈' or self[3] != formula[3]:
                    if not return_subst_dict:
                        return False
                    return False, subst_dict

                # If the above is satisfied, the quantified subformula must be an instance
                result = self[4].is_instance_of(formula[4], language, subst_dict, return_subst_dict=True)
                if not return_subst_dict:
                    return result[0]
                return result

            # Non-bounded quantifier, check the quantified subformula directly after the variable
            else:
                result = self[2].is_instance_of(formula[2], language, subst_dict, return_subst_dict=True)
                if not return_subst_dict:
                    return result[0]
                return result

        return super()._is_molecular_instance_of(formula, language, subst_dict, return_subst_dict)
