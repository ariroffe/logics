import warnings
from copy import deepcopy
from itertools import permutations

from logics.classes.exceptions import IncorrectLevels, LevelsWarning


class Inference:
    """Class for propositional inferences and metainferences.

    Parameters
    ----------
    premises: list of Formula or list of Inference
        The premises of the inference, may be formulae, inferences or the empty list
    conclusions: list of Formula or list of Inference
        The conclusions of the inference, may be formulae, inferences or the empty list
    level: int, optional
        The level of the inference. Will be detected automatically if you leave it with the default value of  None.
        Useful for building empty metainferences (of level >1)

    Raises
    ------
    IncorrectLevels
        if the declared level of the inference does not coincide with the calculated level

    Examples
    --------
    Regular inferences:

    >>> from logics.classes.propositional import Formula, Inference
    >>> Inference([Formula(['p'])], [Formula(['q'])])  # the inference p / q
    >>> Inference([Formula(['p']), Formula(['→', ['p'], ['q']])], [Formula(['q'])])  # modus ponens, p, p → q / q

    Metainferences (e.g. meta-reflexivity, i.e. p / p // p / p, and an empty metainference):

    >>> i1 = Inference([Inference([Formula(['p'])], [Formula(['p'])])],
    ...                [Inference([Formula(['p'])], [Formula(['p'])])])
    >>> i1.level
    2
    >>> i2 = Inference([], [])
    >>> i2.level
    1
    >>> i3 = Inference([], [], level=2)
    >>> i3.level
    2


    An incorrectly declared level:

    >>> Inference([Formula(['p'])], [Formula(['q'])], level=2)
    Traceback (most recent call last):
    ...
    logics.classes.exceptions.IncorrectLevels: Inference ([['p']] / [['q']]) has a premise of level 0 which conflicts with the declared level 2

    Notes
    -----
    Working with Inference elements directly is somewhat uncomfortable and cumbersome. You may instead want to take a
    look at :doc:`parsers`. For random generation of inferences, look at :doc:`formula_generators`
    """

    def __init__(self, premises, conclusions, level=None):
        self.premises = premises
        self.conclusions = conclusions
        self.declared_level = level

        warn = False

        # The previous level to check against is the declared level, or None if there isnt one
        prev_level = None
        if self.declared_level is not None:
            prev_level = self.declared_level - 1

        # Check the level of the premises
        if prev_level is None and self.premises:
            prev_level = self.premises[0].level
        for premise in self.premises:
            if premise.level != prev_level:
                if self.declared_level is None:
                    warn = True
                else:
                    raise IncorrectLevels(f"Inference {self} has a premise of level {premise.level} "
                                          f"which conflicts with the declared level {self.declared_level}")

        # Check the level of the conclusions
        if prev_level is None and self.conclusions:
            prev_level = self.conclusions[0].level
        for conclusion in self.conclusions:
            if conclusion.level != prev_level:
                if self.declared_level is None:
                    warn = True
                else:
                    raise IncorrectLevels(f"Inference {self} has a conclusion of level {conclusion.level} "
                                          f"which conflicts with the declared level {self.declared_level}")

        if warn:
            warnings.warn(f"The inference {self} has premises and/or conclusions of different levels",
                          LevelsWarning)

    @property
    def conclusion(self):
        """Single conclusion of an Inference.

        For single conclusion arguments, you can use ``inference.conclusion`` instead of ``inference.conclusions[0]``
        If there are either more or less than one conclusions, will raise ValueError
        """
        if len(self.conclusions) != 1:
            raise ValueError(f"There are {len(self.conclusions)} conclusions, not one.")
        return self.conclusions[0]

    @property
    def level(self):
        """Level of a (meta)inference

        0 is formula, 1 is regular inference, 2 is metainference, 3 metametainference, etc.
        See above for some examples.
        """
        # Empty premises and conclusions
        if not self.premises and not self.conclusions:
            if self.declared_level:
                return self.declared_level
            return 1
        # Otherwise it returns the level of the conclusions (or premises) + 1
        elif self.conclusions:
            # If there is at least one conclusion, return the level of the first conclusion + 1
            return self.conclusions[0].level + 1
        elif self.premises:
            # If there are no conclusions but there is a premise, return the level of the first premise + 1
            return self.premises[0].level + 1

    @property
    def is_metainference(self):
        """True if the level > 1, False otherwise"""
        return self.level > 1

    def atomics_inside(self, language, prev_at=None):
        """Returns the set of the atomic letter strings (both propositional letters and metavariables)
        inside an inference.

        Similar to the atomics_inside method of :doc:`formula`

        Examples
        --------
        >>> from logics.classes.propositional import Formula, Inference
        >>> from logics.instances.propositional.languages import classical_language
        >>> Inference([Formula(['~', ['p']])], [Formula(['q'])]).atomics_inside(classical_language)
        {'p', 'q'}
        """
        at = prev_at or set()
        for premise in self.premises:
            at = premise.atomics_inside(language, prev_at=at)
        for conclusion in self.conclusions:
            at = conclusion.atomics_inside(language, prev_at=at)
        return at

    def is_schematic(self, language):
        """True if at least one Formula inside the Inference is schematic (contains a schematic Formula),
        False otherwise"""
        for atomic in self.atomics_inside(language):
            if language.is_metavariable_string(atomic):
                return True
        return False

    def substitute(self, sf_or_inf_to_substitute, sf_or_inf_with):
        """Substitutes either a formula or an inference for another inside an inference

        The substituted formula or inference must match exactly. Does not modify the original inference.
        Similar to the substitute method of :doc:`formula`

        Parameters
        ----------
        sf_or_inf_to_substitute: Formula or Inference
        sf_or_inf_with: Formula or Inference

        Examples
        --------
        Substitute a formula for another:

        >>> from logics.classes.propositional import Formula, Inference
        >>> i1 = Inference([Formula(['p'])], [Formula(['q'])])
        >>> i1.substitute(Formula(['q']), Formula(['~', ['q']]))
        ([['p']] / [['~', ['q']]])
        >>> i1
        ([['p']] / [['q']])

        Substitute an inference for another:

        >>> i1 = Inference([Formula(['p'])], [Formula(['q'])])
        >>> i1.substitute(Inference([Formula(['p'])], [Formula(['q'])]),
        ...               Inference([Formula(['q'])], [Formula(['p'])]))
        ([['q']] / [['p']])
        >>> i2 = Inference([Inference([Formula(['p'])], [Formula(['q'])])],
        ...                [Inference([Formula(['q'])], [Formula(['p'])])])
        >>> i2
        ([([['p']] / [['q']])] // [([['q']] / [['p']])])
        >>> i2.substitute(Inference([Formula(['p'])], [Formula(['q'])]),
        ...               Inference([Formula(['~', ['p']])], [Formula(['~', ['q']])]))
        ([([['~', ['p']]] / [['~', ['q']]])] // [([['q']] / [['p']])])
        """
        if self == sf_or_inf_to_substitute:
            return deepcopy(sf_or_inf_with)  # In case the user asks i.substitute(..., i)

        substituted_premises = []
        for premise in self.premises:
            substituted_premises.append(premise.substitute(sf_or_inf_to_substitute, sf_or_inf_with))

        substituted_conclusions = []
        for conclusion in self.conclusions:
            substituted_conclusions.append(conclusion.substitute(sf_or_inf_to_substitute, sf_or_inf_with))

        return self.__class__(substituted_premises, substituted_conclusions)

    def is_instance_of(self, inference, language, subst_dict=None, return_subst_dict=False, order=False):
        """Determines if a Inference is an instance of another (tipically schematic) Inference.

        Since (until now at least) logics does not have metavariables for inferences, all it will do is check if all the
        premises are instances and all the conclusions are instances (recursively so if this is a metainference).
        For two non-schematic inferences, one is considered an instance of another iff they are equal.
        Similar to the is_instance_of method of :doc:`formula`. The optional parameters
        `subst_dict` and `return_subst_dict` are as in that method.

        Contains an additional parameter `order`.  If True, the premises and conclusions of both have to be in the same
        order. e.g. `p, q ∧ r / p` will be an instance of `p, A / p`  but not of `A, p / p`. If False, both are instances.

        Parameters
        ----------
        inference: logics.classes.propositional.Inference
            The (schematic) Inference of which we want to know if it is instance
        language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
            Instance of Language or InfiniteLanguage
        subst_dict: dict, optional
            A susbstitution dict of the form ``{'A': someformula, 'B': someformula}``
        return_subst_dict: bool, optional
            If True will additionally return a substitution dict.
        order: bool
            If True will respect the order of the premises and conclusions in `inference`, if False will not.

        Examples
        --------
        >>> from logics.classes.propositional import Formula, Inference
        >>> from logics.instances.propositional.languages import classical_language
        >>> i1 = Inference([Formula(['p'])], [Formula(['p'])])
        >>> i2 = Inference([Formula(['A'])], [Formula(['A'])])
        >>> i1.is_instance_of(i2, classical_language)
        True
        >>> i3 = Inference([Formula(['p'])], [Formula(['q'])])
        >>> i3.is_instance_of(i2, classical_language)
        False

        The `subst_dict` and `return_subst_dict` parameters:

        >>> i1.is_instance_of(i2, classical_language, subst_dict={'A': Formula(['q'])})
        False
        >>> i1.is_instance_of(i2, classical_language, return_subst_dict=True)
        (True, {'A': ['p']})

        All the above works with any level of metainferences as well:

        >>> i4 = Inference([Inference([Formula(['p'])], [Formula(['q'])])],
        ...                [Inference([Formula(['q'])], [Formula(['p'])])])
        >>> i4
        ([([['p']] / [['q']])] // [([['q']] / [['p']])])
        >>> i5 = Inference([Inference([Formula(['A'])], [Formula(['B'])])],
        ...                [Inference([Formula(['B'])], [Formula(['A'])])])
        >>> i5
        ([([['A']] / [['B']])] // [([['B']] / [['A']])])
        >>> i4.is_instance_of(i5, classical_language)
        True
        >>> i4.is_instance_of(i5, classical_language, return_subst_dict=True)
        (True, {'A': ['p'], 'B': ['q']})

        The `order` parameter:

        >>> i6 = Inference([Formula(['p']), Formula(['→', ['p'], ['q']])], [Formula(['q'])])
        >>> i7 = Inference([Formula(['→', ['A'], ['B']]), Formula(['A'])], [Formula(['B'])])
        >>> i6.is_instance_of(i7, classical_language)  # order is False by default
        True
        >>> i6.is_instance_of(i7, classical_language, order=True)
        False
        """
        if subst_dict is None:
            subst_dict = dict()

        # Different number of premises or conclusions means False
        if len(self.premises) != len(inference.premises) or len(self.conclusions) != len(inference.conclusions):
            if not return_subst_dict:
                return False
            return False, subst_dict
        # Different levels means False (this is necessary for empty (meta)inferences, an optimization for the rest)
        if self.level != inference.level:
            if not return_subst_dict:
                return False
            return False, subst_dict

        if order:
            for premise_index in range(len(self.premises)):
                result = self.premises[premise_index].is_instance_of(inference.premises[premise_index], language,
                                                                     subst_dict, return_subst_dict=True, order=order)
                if not result[0]:
                    if not return_subst_dict:
                        return False
                    return False, subst_dict
                subst_dict.update(result[1])

            for conclusion_index in range(len(self.conclusions)):
                result = self.conclusions[conclusion_index].is_instance_of(inference.conclusions[conclusion_index],
                                                                           language, subst_dict, return_subst_dict=True,
                                                                           order=order)
                if not result[0]:
                    if not return_subst_dict:
                        return False
                    return False, subst_dict
                subst_dict.update(result[1])

            # If it did not exit thus far, then is it an instance
            if not return_subst_dict:
                return True
            return True, subst_dict

        else:
            possible_premise_combinations = permutations(range(len(inference.premises)), r=len(inference.premises))
            # For three premises this yields (0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)
            # For each of these permutations will test if the premises of self are an instance
            # of the premises of inference, in that order
            premises_are_instance = True
            for combination in possible_premise_combinations:
                premises_are_instance = True
                for prem_index in range(len(self.premises)):
                    result = self.premises[prem_index].is_instance_of(inference.premises[combination[prem_index]],
                                                                      language, subst_dict, return_subst_dict=True,
                                                                      order=order)
                    # If it is not an instance
                    if not result[0]:
                        premises_are_instance = False
                        break
                    # Else, update the kwargs
                    subst_dict.update(result[1])
                if premises_are_instance:
                    break  # If you get to true here, exit the for order loop
            if not premises_are_instance:
                if not return_subst_dict:
                    return False
                return False, subst_dict

            # Same with the conclusions
            possible_conclusion_combinations = permutations(range(len(inference.conclusions)),
                                                            r=len(inference.conclusions))
            conclusions_are_instance = True
            for combination in possible_conclusion_combinations:
                conclusions_are_instance = True
                for cncl_index in range(len(self.conclusions)):
                    result = self.conclusions[cncl_index].is_instance_of(inference.conclusions[combination[cncl_index]],
                                                                         language, subst_dict, return_subst_dict=True,
                                                                         order=order)
                    # If it is not an instance
                    if not result[0]:
                        conclusions_are_instance = False
                        break
                    # Else, update the kwargs
                    subst_dict.update(result[1])
                if conclusions_are_instance:
                    break  # If you get to true here, exit the for order loop
            if not conclusions_are_instance:
                if not return_subst_dict:
                    return False
                return False, subst_dict

            # If you got to here, every premise and every conclusion is an instance
            if not return_subst_dict:
                return True
            return True, subst_dict

    def is_valid(self, validity_aparatus):
        return validity_aparatus.is_valid(self)

    def __eq__(self, other):
        """Evaluates Inference1 == Inference2 to True when they have == premises and == conclusions"""
        return isinstance(other, self.__class__) and \
            self.premises == other.premises and self.conclusions == other.conclusions

    def __ne__(self, other):
        return not self.__eq__(other)

    def __repr__(self):
        return f"({str(self.premises)} " + "/" * self.level + f" {str(self.conclusions)})"
