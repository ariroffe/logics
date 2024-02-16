import random
from copy import copy

from logics.classes.propositional import Formula, Inference
from logics.classes.predicate import PredicateFormula
from logics.classes.exceptions import FormulaGeneratorError


class BiasedPropositionalGenerator:
    """A biased random propositional generator.

    It is biased because it will not return every formula/inference within the space asked with the same probability.
    On the other hand, it is *much* faster than its non-biased counterpart.

    Examples
    --------
    This generator takes no parameters, so to instantiate one you can simply do:

    >>> from logics.utils.formula_generators.generators_biased import BiasedPropositionalGenerator
    >>> random_generator = BiasedPropositionalGenerator()

    There is also a predefined instance so there is even no need to instantiate it

    >>> from logics.utils.formula_generators.generators_biased import random_formula_generator
    """
    # ------------------------------------------------------------------------------------------------------------------
    # FORMULAE

    def random_formula(self, depth, atomics, language, exact_depth=True, all_atomics=False):
        """Generates a random formula for the language given.

        Parameters
        ----------
        depth: int
            A positive integer, representing the depth of the formula to obtain
        atomics: list of str
            The sublist of atomics of the language that the formula will be built of
        language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
            Instance of Language or InfiniteLanguage
        exact_depth: bool
            If true, the resulting formula will have *exactly* the depth given. Otherwise, will have *up to* that depth.
            Defaults to True.
        all_atomics: bool
            If true, the resulting formula will contain *all* the atomics given. Otherwise, can contain *some* of them.
            Defaults to False.

        Returns
        -------
        logics.classes.propositional.Formula
            A randomly generated formula of the given depth, containing some or all the atomics

        Raises
        ------
        NotImplemented
            If exact_depth is False and all_atomics is True
        ValueError
            If exact_depth is True, all_atomics is True and the number of atomics given > the maximum arity constant of
            the language ** depth.
            For example, it is not possible to build a formula of depth 1 with 3 atomics in a language that has
            connectives of at most arity 2.

        Examples
        --------
        Exact depth and not all atomics

        >>> from logics.instances.propositional.languages import classical_language
        >>> from logics.utils.formula_generators.generators_biased import random_formula_generator
        >>> random_formula_generator.random_formula(depth=3, atomics=['p', 'q', 'r'],
        ...                                         language=classical_language,
        ...                                         exact_depth=True, all_atomics=False)
        ['→', ['→', ['p'], ['↔', ['r'], ['p']]], ['~', ['r']]]
        >>> random_formula_generator.random_formula(depth=3, atomics=['p', 'q', 'r'],
        ...                                         language=classical_language,
        ...                                         exact_depth=True, all_atomics=False)
        ['↔', ['∨', ['~', ['r']], ['r']], ['↔', ['p'], ['q']]]

        Not exact depth and not all atomics

        >>> random_formula_generator.random_formula(depth=3, atomics=['p', 'q', 'r'],
        ...                                         language=classical_language,
        ...                                         exact_depth=False, all_atomics=False)
        ['∨', ['r'], ['q']]
        >>> random_formula_generator.random_formula(depth=3, atomics=['p', 'q', 'r'],
        ...                                         language=classical_language,
        ...                                         exact_depth=False, all_atomics=False)
        ['→', ['r'], ['∨', ['p'], ['r']]]

        Exact depth and all atomics

        >>> random_formula_generator.random_formula(depth=3, atomics=['p', 'q', 'r'],
        ...                                         language=classical_language,
        ...                                         exact_depth=True, all_atomics=True)
        ['~', ['∧', ['∧', ['r'], ['q']], ['p']]]
        >>> random_formula_generator.random_formula(depth=3, atomics=['p', 'q', 'r'],
        ...                                         language=classical_language,
        ...                                         exact_depth=True, all_atomics=True)
        ['∨', ['∨', ['∧', ['q'], ['r']], ['→', ['r'], ['q']]], ['p']]
        """

        if exact_depth and all_atomics:
            return self._exact_depth_all_atomics(depth, atomics, language)
        elif exact_depth and not all_atomics:
            return self._exact_depth_some_atomics(depth, atomics, language)
        elif not exact_depth and not all_atomics:
            return self._upto_depth_some_atomics(depth, atomics, language)
        else:
            raise NotImplemented('This method does not yet accept a non-exact depth and all atomics')

    def _exact_depth_some_atomics(self, depth, atomics, language):
        """Generates a random formula of some *exact* depth, which includes *some* of the atomics given."""
        if depth == 0:
            return Formula([random.choice(atomics)])

        else:
            constant = random.choice(tuple(language.constants()))
            arity = language.arity(constant)
            formula = Formula([constant])
            formula.extend([None] * arity)  # By now, formula is something like ['^', None, None]

            # Randomly choose an index and put a formula of depth - 1 there
            # (to ensure the formula reaches the depth given)
            i = random.randint(1, arity)  # index 0 is the constant
            formula[i] = self._exact_depth_some_atomics(depth-1, atomics, language)

            # In the rest of the arguments put a formula of random depth
            for x in set(range(1, arity+1)) - {i}:
                j = random.randint(0, depth-1)
                formula[x] = self._exact_depth_some_atomics(j, atomics, language)

            return formula

    def _upto_depth_some_atomics(self, depth, atomics, language):
        """Generates a random formula of *up to* some depth, which includes *some* of the atomics given.
        Works very similarly to the method above
        """

        # Choose a depth and then call the previous function
        chosen_depth = random.randint(0, depth)
        return self._exact_depth_some_atomics(chosen_depth, atomics, language)

    def _exact_depth_all_atomics(self, depth, atomics, language):
        """Generates a random formula of some *exact* depth, which includes *all* of the atomics given."""
        # Brute force approach, will use g_ES and then check if all the atomics are present
        # Tries up to 100 times, then raises an RuntimeError exception
        # Should be possible to build a better function (see below).

        # Validate that the request is possible
        if len(atomics) > max(language.constant_arity_dict.values()) ** depth:
            raise ValueError("len(atomics) can be at most the maximum arity of a constant of the language ** depth")

        for x in range(100):
            acceptable = True
            formula = self._exact_depth_some_atomics(depth, atomics, language)
            for at in atomics:
                if at not in str(formula):
                    acceptable = False
            if acceptable:
                return formula

        raise FormulaGeneratorError('Could not generate a formula with the desired parameters')

    def exact_depth_all_atomics2(self, depth, atomics, language):
        # todo FIX THIS - for depth 1 and ['p', 'q'] the first part can return ~['$']

        # Validate that the request is possible
        if len(atomics) > max(language.constant_arity_dict.values()) ** depth:
            raise ValueError("len(atomics) can be at most the maximum arity of a constant of the language ** depth")

        # Generate a formula with placeholders where the atomics will be
        formula_with_placeholders = self._exact_depth_some_atomics(depth, ['$'], language)

        # For each atomic, replace at least one placeholder for it (so that every atomic appears at least once)
        formula_string = str(formula_with_placeholders)
        placeholder_indexes = [x for x in range(len(formula_string)) if formula_string[x] == '$']
        for atomic in atomics:
            # Choose an index and remove it from the list
            chosen_index = random.choice(placeholder_indexes)
            placeholder_indexes.remove(chosen_index)
            # Replace the index with the atomic
            formula_string = formula_string[:chosen_index] + atomic + formula_string[chosen_index+1:]

        # The remaining placeholders replace them with a random choice of atomics
        for index in placeholder_indexes:
            chosen_atomic = random.choice(atomics)
            formula_string = formula_string[:index] + chosen_atomic + formula_string[index+1:]

        formula = Formula(eval(formula_string))
        return formula

    # ------------------------------------------------------------------------------------------------------------------
    # INFERENCE

    def random_inference(self, num_premises, num_conclusions, max_depth, atomics, language, level=1,
                         exact_num_premises=True, exact_num_conclusions=True):
        """Generates a random Inference.

        Takes a number of premises and of conclusions (either exact or up to, see the `exact_num_premises` and
        `exact_num_conclusions` parameters below), and populates them with formuale of *up to* the given `max_depth`
        and *some* of the given `atomics`.

        Can also be used to generate metainferences, if given a `level` > 1. In that case, the inferences in the
        premises / conclusions will have *up to* that number of premises and conclusions. That is, if asked for an
        inference of level 2 with exactly two premises, the premises will themselves be inferences, and they may contain
        less than two premises.

        Parameters
        ----------
        num_premises: int
            The exact number of premises the inference will contain
        num_conclusions: int
            The exact number of conclusions the inference will contain
        max_depth: int
            The maximum depth that the formulae within the inference can contain
        atomics: list of str
            The sublist of atomics of the language that the formulae within the inference will be built of
        language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
            Instance of Language or InfiniteLanguage
        level: int, optional
            Level of the inference to be generated (1 is regular inference, 2 is metainference, 3 is metameta, ...).
            level is 1 by default.
        exact_num_premises: bool
            If True, the resulting inference will contain will contain *exactly* that number of premises, otherwise will
            contain *up to* that number of premises. Defaults to True.
        exact_num_conclusions: bool
            If True, the resulting inference will contain will contain *exactly* that number of premises, otherwise will
            contain *up to* that number of premises. Defaults to True.

        Returns
        -------
        logics.classes.propositional.Inference
            A randomly generated inference of the given parameters.

        Examples
        --------
        Random inferences with exactly two premises and one conclusion:

        >>> from logics.instances.propositional.languages import classical_language
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.utils.formula_generators.generators_biased import random_formula_generator
        >>> inf = random_formula_generator.random_inference(num_premises=2, num_conclusions=1,
        ...                                                 max_depth=2, atomics=['p', 'q'],
        ...                                                 language=classical_language, level=1,
        ...                                                 exact_num_premises=True,
        ...                                                 exact_num_conclusions=True)
        >>> classical_parser.unparse(inf)
        '(p ∧ p), ((q ∨ q) ∧ (p ∨ p)) / ~q'
        >>> inf = random_formula_generator.random_inference(num_premises=2, num_conclusions=1,
        ...                                                 max_depth=2, atomics=['p', 'q'],
        ...                                                 language=classical_language, level=1,
        ...                                                 exact_num_premises=True,
        ...                                                 exact_num_conclusions=True)
        >>> classical_parser.unparse(inf)
        '~(q ↔ q), q / (q ∧ (p → p))'

        Random inferences with up to two premises and two conclusions

        >>> inf = random_formula_generator.random_inference(num_premises=2, num_conclusions=2,
        ...                                                 max_depth=2, atomics=['p', 'q'],
        ...                                                 language=classical_language, level=1,
        ...                                                 exact_num_premises=False,
        ...                                                 exact_num_conclusions=False)
        >>> classical_parser.unparse(inf)
        '(p ↔ p) / ~q'
        >>> inf = random_formula_generator.random_inference(num_premises=2, num_conclusions=2,
        ...                                                 max_depth=2, atomics=['p', 'q'],
        ...                                                 language=classical_language, level=1,
        ...                                                 exact_num_premises=False,
        ...                                                 exact_num_conclusions=False)
        >>> classical_parser.unparse(inf)
        '/'

        Random metainferences with up to two premises and two conclusions

        >>> inf = random_formula_generator.random_inference(num_premises=2, num_conclusions=2,
        ...                                                 max_depth=2, atomics=['p', 'q'],
        ...                                                 language=classical_language, level=2,
        ...                                                 exact_num_premises=False,
        ...                                                 exact_num_conclusions=False)
        >>> classical_parser.unparse(inf)
        '((q → (q → q)) /), ((p ↔ p), (q ∧ p) / (q ∨ q), p) //'
        >>> inf = random_formula_generator.random_inference(num_premises=2, num_conclusions=2,
        ...                                                 max_depth=2, atomics=['p', 'q'],
        ...                                                 language=classical_language, level=2,
        ...                                                 exact_num_premises=False,
        ...                                                 exact_num_conclusions=False)
        >>> classical_parser.unparse(inf)
        '(/) //'
        """
        if level == 0:
            raise ValueError('Inferences cannot have level 0')

        # Premises
        premises = list()
        new_num_premises = num_premises
        if not exact_num_premises:
            new_num_premises = random.randint(0, num_premises)

        for _ in range(new_num_premises):
            if level == 1:
                premises.append(self._upto_depth_some_atomics(max_depth, atomics, language))
            else:
                premises.append(self.random_inference(num_premises, num_conclusions, max_depth, atomics, language,
                                                      level=level-1, exact_num_premises=False,
                                                      exact_num_conclusions=False))

        # Conclusions
        conclusions = list()
        new_num_conclusions = num_conclusions
        if not exact_num_conclusions:
            new_num_conclusions = random.randint(0, num_conclusions)

        for _ in range(new_num_conclusions):
            if level == 1:
                conclusions.append(self._upto_depth_some_atomics(max_depth, atomics, language))
            else:
                conclusions.append(self.random_inference(num_premises, num_conclusions,
                                                         max_depth, atomics, language, level=level-1))

        return Inference(premises=premises, conclusions=conclusions, level=level)

    # ------------------------------------------------------------------------------------------------------------------
    # THINGS WITH VALIDITY APPARATUSES

    def random_tautology(self, depth, atomics, language, validity_apparatus, exact_depth=True, all_atomics=False,
                         attempts=100):
        """Generates a random tautogy for the validity apparatus given.

        Will generate a random formula and then test the inference ([] / [formula]) to see if it is valid. If it is,
        returns it, otherwise generates another. Can fail for at most the number of `attempts` given.

        The signature is very similar to that of random_formula but takes two extra parameters:

            * validity_apparatus: any object with an is_valid method (which takes an inference as argument)
            * attempts: an `int`, maximum number of formulae it generates and tests (defaults to 100)

        Returns
        -------
        logics.classes.propositional.Formula
            A randomly generated tautology of the given depth, containing some or all the atomics

        Raises
        ------
        NotImplemented
            If exact_depth is False and all_atomics is True
        ValueError
            If exact_depth is True, all_atomics is True and the number of atomics given > the maximum arity constant of
            the language ** depth.
        FormulaGeneratorError
            If it cannot find a tautology in the given number of `attempts`

        Examples
        --------
        >>> from logics.instances.propositional.languages import classical_language
        >>> from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics
        >>> from logics.utils.formula_generators.generators_biased import random_formula_generator
        >>> random_formula_generator.random_tautology(depth=2, atomics=['p', 'q'],
        ...                                           language=classical_language,
        ...                                           validity_apparatus=classical_mvl_semantics)
        ['→', ['∧', ['q'], ['p']], ['∧', ['q'], ['q']]]
        >>> random_formula_generator.random_tautology(depth=2, atomics=['p', 'q'],
        ...                                           language=classical_language,
        ...                                           validity_apparatus=classical_mvl_semantics)
        ['→', ['p'], ['∨', ['p'], ['p']]]
        """
        for _ in range(attempts):
            if exact_depth and all_atomics:
                formula = self._exact_depth_all_atomics(depth, atomics, language)
            elif exact_depth and not all_atomics:
                formula = self._exact_depth_some_atomics(depth, atomics, language)
            elif not exact_depth and not all_atomics:
                formula = self._upto_depth_some_atomics(depth, atomics, language)
            else:
                raise NotImplemented('Not exact depth and all atomics generator not implemented yet')

            inf = Inference(premises=[], conclusions=[formula])
            if validity_apparatus.is_valid(inf):
                return formula

        raise FormulaGeneratorError('Could not generate tautology with the parameters given')

    def random_valid_inference(self, num_premises, num_conclusions, max_depth, atomics, language, validity_apparatus,
                               level=1, exact_num_premises=True, exact_num_conclusions=True, attempts=100):
        """Generates a random *valid* inference for the validity apparatus given.

        Similar to the random_inference method. The two new parameters are to the method above.
        In particular, The object passed to `validity_apparatus` must have an `is_valid` method.
        If `level` > 1 the validity apparatus must be able to handle metainferential validity.

        Returns
        -------
        logics.classes.propositional.Inference
            A randomly generated valid inference or metainference with the parameters given

        Raises
        ------
        FormulaGeneratorError
            If it cannot find a valid inference in the given number of `attempts`

        Examples
        --------
        >>> from logics.instances.propositional.languages import classical_language
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.many_valued_semantics import classical_mvl_semantics
        >>> from logics.utils.formula_generators.generators_biased import random_formula_generator
        >>> inf = random_formula_generator.random_valid_inference(num_premises=2, num_conclusions=1,
        ...                                                       max_depth=2, atomics=['p', 'q'],
        ...                                                       language=classical_language, level=1,
        ...                                                       validity_apparatus=classical_mvl_semantics)
        >>> classical_parser.unparse(inf)
        '(q ↔ p), p / (p ∨ q)'
        >>> inf = random_formula_generator.random_valid_inference(num_premises=2, num_conclusions=1,
        ...                                                       max_depth=2, atomics=['p', 'q'],
        ...                                                       language=classical_language, level=2,
        ...                                                       validity_apparatus=classical_mvl_semantics)
        >>> classical_parser.unparse(inf)
        '(p / p), (p, ((q → p) ∧ (p ∨ p)) / (p ↔ (q ↔ p))) // (((p ↔ p) ∨ p), ~q / (q ∨ ~p))'
        """
        for _ in range(attempts):
            inf = self.random_inference(num_premises, num_conclusions, max_depth, atomics, language, level,
                                        exact_num_premises, exact_num_conclusions)
            if validity_apparatus.is_valid(inf):
                return inf

        raise FormulaGeneratorError('Could not generate valid inference with the parameters given')

    def random_invalid_inference(self, num_premises, num_conclusions, max_depth, atomics, language, validity_apparatus,
                                 level=1, exact_num_premises=True, exact_num_conclusions=True, attempts=100):
        """Generates a random *invalid* inference for the validity apparatus given.

        Identical to the method above, only that it returns an *invalid* inference.
        """
        for _ in range(attempts):
            inf = self.random_inference(num_premises, num_conclusions, max_depth, atomics, language, level,
                                        exact_num_premises, exact_num_conclusions)
            if not validity_apparatus.is_valid(inf):
                return inf

        raise FormulaGeneratorError('Could not generate valid inference with the parameters given')


random_formula_generator = BiasedPropositionalGenerator()


# ----------------------------------------------------------------------------------------------------------------------
# Predicate formula generator

class BiasedPredicateGenerator:
    """A biased random predicate generator.

        It is biased because it will not return every formula/inference within the space asked with the same probability.
        There is no non-biased generator implemented in this package yet.
        This implementation does not yet work with function symbols.

        Examples
        --------
        This generator takes no parameters, so to instantiate one you can simply do:

        >>> from logics.utils.formula_generators.generators_biased import BiasedPredicateGenerator
        >>> random_generator = BiasedPredicateGenerator()

        There is also a predefined instance so there is even no need to instantiate it

        >>> from logics.utils.formula_generators.generators_biased import random_predicate_formula_generator
        """
    def _random_term(self, ind_constants, variables):
        # We select an ind_constant and a variable with equal probability, even if there is just 1 var and 5 ind_cts
        if not variables or random.choice((True, False)):
            return random.choice(ind_constants)
        else:
            return random.choice(variables)

    def _random_atomic_formula(self, predicates, max_arity, ind_constants, variables, predicate_arities):
        # Firstly, we must choose a predicate and set its arity
        predicate = random.choice(predicates)
        formula = PredicateFormula([predicate])
        if predicate in predicate_arities:
            arity = predicate_arities[predicate]
        else:
            arity = random.randint(1, max_arity)
            predicate_arities[predicate] = arity  # Modify the dict, will be seen by the caller

        for _ in range(arity):
            formula.append(self._random_term(ind_constants, variables))

        return formula

    def random_formula(self, depth, predicates, max_predicate_arity, ind_constants, variables, language,
                       remaining_depth=0, predicate_arities=None):
        """Generates a random formula of some *exact* depth, which uses some of the predicates, variables and ind cts
        provided

        Because of the educational usecases I have in mind, I don't want it to output things like ∀x P(a) or like
        ∀x ∀x P(x). More precisely, Its made so every quantifier binds at least one variable.

        Assumes that the predicate arities can be random (i.e. will not respect the
        predicate_letters={'P': 1, 'Q': 1, 'R': 2, 'S': 3} argument given to PredicateLanguage). If you want it to,
        give it predicate_arities=language.predicate_letters

        Examples
        --------
        >>> from logics.instances.predicate.languages import classical_predicate_language as lang
        >>> from logics.utils.parsers import classical_predicate_parser
        >>> from logics.utils.formula_generators.generators_biased import random_predicate_formula_generator
        >>> for _ in range(5):
        ...     formula = random_predicate_formula_generator.random_formula(depth=2, predicates=['P', 'Q'],
        ...         max_predicate_arity=2, ind_constants=['a', 'b'], variables=['x', 'y'], language=lang)
        ...     print(classical_predicate_parser.unparse(formula))
        Q(b, a) → ∀x Q(x, x)
        ∀y Q(y) ∧ Q(b)
        ∀x (Q(b) ∧ P(x, a))
        ∀y (Q(y, a) ∧ P(y, y))
        ∃x P(x) ∨ P(b)
        """
        if predicate_arities is None:
            predicate_arities = dict()

        if depth == 0:
            # We must make sure that the number of free variables in this atomic is not greater than the
            # remaining depth, otherwise we cannot get to bind them all.
            # E.g. if we originally asked for depth=1, when this clause is reached, remaining_depth==1
            # and variables[:remaining_depth] will be ['x']
            return self._random_atomic_formula(predicates, max_predicate_arity, ind_constants,
                                               variables[:remaining_depth], predicate_arities)

        else:
            # We proceed recursively in the reverse direction than the other generator, that is, we go bottom-up
            # First generate a subformula
            first_argument = self.random_formula(depth-1, predicates, max_predicate_arity, ind_constants, variables,
                                                 language, remaining_depth+1, predicate_arities)

            # Check the free variables in the first arg
            free_vars = first_argument.free_variables(language)
            # If free_vars is ['x', 'y'], rem_depth must be at least 1
            # since one quantifier can be introduced here, and the and another in the remaining top call
            assert remaining_depth + 1 >= len(free_vars)
            # if remaining_depth + 1 < len(free_vars):
            #     print("ERROR", first_argument, depth, remaining_depth, free_vars)
            #     raise ValueError("Fix this")

            # Then choose a logical constant
            if not free_vars:
                # If there are no free variables, do not introduce quantifiers that bind nothing
                constant = random.choice(tuple(language.constants()))
            elif remaining_depth + 1 == len(free_vars):
                # We MUST choose a quantifier
                # e.g.  remaining depth is 0 (this is the last constant introduced) and we have 1 free variable
                # e.g.2 remaining depth is 1 (we will introduce this + 1 ctt) and we have 2 free variables
                constant = random.choice(language.quantifiers)
            else:
                # Otherwise can be either a quantifier or a logical constant, choose with equal prob so that
                # there is no bias for all the quantifiers to be at the beginning of the formula
                if random.choice((True, False)):
                    constant = random.choice(tuple(language.constants()))
                else:
                    constant = random.choice(language.quantifiers)

            arity = language.arity(constant)

            # Quantified formula
            if constant in language.quantifiers:
                variable = random.choice(list(free_vars))
                return PredicateFormula([constant, variable, first_argument])

            # Unary connective formula
            elif arity == 1:
                return PredicateFormula([constant, first_argument])

            # Binary connective formula
            else:
                # We must be careful here bc the second subformula could introduce more free variables
                # We can use the free variables in the first_argument freely, though
                # E.g. if x is already free here, and we have 2 remaining depth (will introduce 2 more cts--do not count
                # this one bc it is not a quantifier) -- then the second subformula can contain one extra var
                new_vars = list(free_vars)
                extra_vars_allowed = remaining_depth - len(free_vars)
                if extra_vars_allowed:
                    extra_vars = [v for v in variables if v not in new_vars]
                    new_vars.extend(extra_vars[:extra_vars_allowed])

                second_argument = self.random_formula(random.randint(0, depth-1), predicates, max_predicate_arity,
                                                      ind_constants, new_vars, language, remaining_depth+1,
                                                      predicate_arities)
                if random.choice((True, False)):
                    return PredicateFormula([constant, first_argument, second_argument])
                else:
                    return PredicateFormula([constant, second_argument, first_argument])


random_predicate_formula_generator = BiasedPredicateGenerator()
