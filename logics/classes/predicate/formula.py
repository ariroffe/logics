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

    def is_schematic(self, language):
        """Returns ``True`` if the formula contains an (individual, predicate or sentential) metavariable of the
        language, ``False`` otherwise

        Examples
        --------
        >>> from logics.classes.predicate import PredicateFormula
        >>> from logics.instances.predicate.languages import classical_predicate_language
        >>> PredicateFormula(['P', 'a']).is_schematic(classical_predicate_language)
        False
        >>> PredicateFormula(['P', 'α']).is_schematic(classical_predicate_language)
        True
        >>> PredicateFormula(['∧', ['P', 'x'], ['A']]).is_schematic(classical_predicate_language)
        True
        """
        if self.is_atomic:
            for term in self:
                if self._is_schematic_term(term, language):
                    return True
            return False
        else:
            # Quantified case, check the variable and bound
            if self[0] in language.quantifiers:
                if self[1] in language.variable_metavariables:
                    return True
                if self[2] == '∈' and self._is_schematic_term(self[3], language):
                    return True

            for argument in self.arguments(language.quantifiers):
                if argument.is_schematic(language):
                    return True
            return False

    @staticmethod
    def _is_schematic_term(term, language):
        # base case
        if type(term) == str:
            return language.is_metavariable_string(term)  # will check for ind, var and sentence metavariables
        # nested subterms
        elif type(term) == tuple:
            for subterm in term:
                if PredicateFormula._is_schematic_term(subterm, language):
                    return True
            return False
        raise ValueError("A term should be either a string or a tuple")

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
            # If you are evaluating a particular term, e.g. 'a' or ('f', ('g', 'x'))
            # Atomic term, e.g. 'a'
            if type(term) == str:
                if language._is_valid_variable(term, allow_metavariables=True) and term not in _bound_variables:
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

    def individual_constants_inside(self, language, ind_cts=None):
        """Returns a set of the individual constants that the formula contains"""
        if ind_cts is None:
            ind_cts = set()

        # Atomic
        if self.is_atomic and len(self) > 1:  # if len is 1, it is a sentential mv, has no atomics
            for term in self[1:]:
                ind_cts |= self._term_individual_constants_inside(term, language)

        # Molecular
        else:
            # Check the bound of quantified formulae
            if (self[0] == "∀" or self[0] == "∃") and self[2] == "∈":
                ind_cts |= self._term_individual_constants_inside(self[3], language)

            # Add the constants in the arguments
            for arg in self.arguments(language.quantifiers):
                ind_cts |= arg.individual_constants_inside(language, ind_cts)

        return ind_cts

    def _term_individual_constants_inside(self, term, language, ind_cts=None):
        if type(term) == str:
            if term in language.individual_constants:
                return {term}
            return set()
        elif type(term) == tuple:
            if ind_cts is None:
                ind_cts = set()
            for subterm in term:
                ind_cts |= self._term_individual_constants_inside(subterm, language, ind_cts)
            return ind_cts
        raise ValueError(f"Incorrect term {term}")

    def contains_string(self, string):
        """Determines if a formula constains a given string (useful, e.g., checking arbitrary cts in natural deduction),
        excluding connectives and base language

        Examples
        --------
        >>> from logics.utils.parsers.predicate_parser import classical_predicate_parser as parser
        >>> f = parser.parse("forall x (P(x)) and ~R(a, f(b))")
        >>> f.contains_string('R')
        True
        >>> f.contains_string('a')
        True
        >>> f.contains_string('x')
        True
        >>> f.contains_string('c')
        False
        >>> f.contains_string('y')
        False
        >>> f.contains_string('f')
        True
        """
        if self.is_atomic:
            for term in self:  # the relation itself is counted as a term here
                if self._term_contains_string(term, string):
                    return True
            return False
        else:
            # If the formula is a quantifier
            if self[0] == "∀" or self[0] == "∃":
                # Check the variable
                if self[1] == string:
                    return True

                # If the formula is a bounded quantifier check the bound
                if self[2] == "∈":
                    if self._term_contains_string(self[3], string):
                        return True

            for argument in self.arguments():
                if argument.contains_string(string):
                    return True

            return False

    def _term_contains_string(self, term, string):
        if type(term) == str:
            return term == string
        elif type(term) == tuple:
            for subterm in term:
                if self._term_contains_string(subterm, string):
                    return True
            return False
        raise ValueError(f"Incorrect term {term}")

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

    def _molecular_instantiate(self, language, subst_dict):
        # Handle only the case of quantifiers, the rest is done by the super method
        if self[0] in language.quantifiers:
            instantiation = self.__class__([self[0]])
            instantiation.append(self._term_instantiate(self[1], language, subst_dict))  # variable
            if self[2] == '∈':  # bounded quantifier
                instantiation.extend(['∈', self._term_instantiate(self[3], language, subst_dict)])
                instantiation.append(self[4].instantiate(language, subst_dict))
            else:  # non-bounded
                instantiation.append(self[2].instantiate(language, subst_dict))
            return instantiation
        return super()._molecular_instantiate(language, subst_dict)

    def _atomic_instantiate(self, language, subst_dict):
        # Same as the propositional formula method but includes instantiation of variable and ind constant metavars

        # Instantiate things of the form [α/χ]A, useful for things like ND solver
        if self[0][0] == '[' and self[0][4] == ']':
            ind_mv, var_mv = self[0][1:4].split('/')
            if ind_mv not in subst_dict:
                raise ValueError(f'PredicateFormula {self} has no substitution assigned for {ind_mv}')
            if var_mv not in subst_dict:
                raise ValueError(f'PredicateFormula {self} has no substitution assigned for {var_mv}')
            # First instantiate the A
            f = self.__class__([self[0][5:]]).instantiate(language, subst_dict)
            # Then substitute the free occurences of whatever χ is for whatever α is
            f = f.vsubstitute(subst_dict[var_mv], subst_dict[ind_mv])
            return f

        # Sentential metavar is covered in the super method
        if language.is_metavariable_string(self[0]):
            return super()._atomic_instantiate(language, subst_dict)

        # Else, look for individual or variable metavars
        f = self.__class__([self[0]])
        for term in self[1:]:
            f.append(self._term_instantiate(term, language, subst_dict))  # _term_instantiate returns a deepcopy
        return f

    def _term_instantiate(self, term, language, subst_dict):
        if type(term) == str:
            if language.is_metavariable_string(term):  # is_mv_string checks for both ind and var mvs
                if term in subst_dict:
                    return subst_dict[term]
                raise ValueError(f'Metavariable {term} not present in substitution dict given')
            return term

        elif type(term) == tuple:
            new_terms = list()
            for subterm in term[1:]:
                new_terms.append(self._term_instantiate(subterm, language, subst_dict))
            return (term[0], *new_terms)

        raise ValueError("A term should be either a string or a tuple")

    def _is_atomic_instance_of(self, formula, language, subst_dict, return_subst_dict):
        # We can assume that formula is schematic atomic (may be something like 'A' or like 'R(α, b)')

        # The case of atomic sententials (e.g., 'A') is handled in the superclass
        if len(formula) == 1 and formula[0] in language.metavariables:
            return super()._is_atomic_instance_of(formula, language, subst_dict, return_subst_dict)

        # Here we need to check the case of atomics with a schematic individual and/or predicate metavariable
        # First, check that the formulae have the same length
        if len(self) != len(formula):
            if not return_subst_dict:
                return False
            return False, subst_dict

        # Second, check that the predicate term is the same
        if formula[0] != self[0]:
            if not return_subst_dict:
                return False
            return False, subst_dict

        # Third, check the terms
        for idx in range(len(formula)-1):  # minus one to remove the predicate, plus one below for the same reason
            term_is_instance, subst_dict = self._is_term_instance_of(self[idx+1], formula[idx+1], language, subst_dict)
            if not term_is_instance:
                if not return_subst_dict:
                    return False
                return False, subst_dict

        # If you reach here, all is good
        if not return_subst_dict:
            return True
        return True, subst_dict

    def _is_term_instance_of(self, self_term, formula_term, language, subst_dict):
        # base case, you get a string
        if type(formula_term) == str:
            # If the string is an individual metavariable or variable metavariable, check instance
            if (formula_term in language.individual_metavariables and language.is_valid_individual_constant(self_term)) \
                    or (formula_term in language.variable_metavariables and
                        language._is_valid_variable(self_term, only_individual=True)):
                # There is a previous substitution instance
                if formula_term in subst_dict:
                    if subst_dict[formula_term] == self_term:
                        return True, subst_dict
                    return False, subst_dict
                else:  # not in the subst dict, add it
                    subst_dict[formula_term] = self_term
                    return True, subst_dict

            # If not an individual/variable metavariable, then they have to be equal
            else:
                return formula_term == self_term, subst_dict

        # We got a complex term - e.g. (f, (g, a))
        else:
            # Check that the length of the terms coincides
            if len(formula_term) != len(self_term):
                return False, subst_dict

            # They do coincide, check each member of the tuple recursively
            for idx in range(len(formula_term)):
                term_is_instance, subst_dict = \
                    self._is_term_instance_of(self_term[idx], formula_term[idx], language, subst_dict)
                if not term_is_instance:
                    return False, subst_dict
            return True, subst_dict

    def _is_molecular_instance_of(self, formula, language, subst_dict, return_subst_dict):
        # We only need the quantifier case here, for the rest call the super method
        if self.main_symbol == formula.main_symbol and self.main_symbol in language.quantifiers:
            # Check that the variable is an instance
            instance, subst_dict = self._is_term_instance_of(self[1], formula[1], language, subst_dict)
            if not instance:
                if not return_subst_dict:
                    return False
                return False, subst_dict

            # Bounded quantifier case
            if formula[2] == '∈':
                # The bound must be an instance
                instance, subst_dict = self._is_term_instance_of(self[3], formula[3], language, subst_dict)
                if self[2] != '∈' or not instance:
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
