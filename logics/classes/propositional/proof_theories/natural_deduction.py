from logics.classes.propositional.proof_theories import DerivationStep, Derivation


class NaturalDeductionStep(DerivationStep):
    """Step of a natural deduction derivation.

    Extends :ref:`logics.classes.propositional.proof_theories.DerivationStep <derivation-step>` adding an additional
    parameter `open_suppositions` (`list` of `int`)

    Examples
    --------
    A natural deduction step will have the following form

    >>> from logics.classes.propositional.proof_theories import NaturalDeductionStep
    >>> from logics.utils.parsers import classical_parser
    >>> s = NaturalDeductionStep(content=classical_parser.parse('p or ~q'), justification='I∨',
    ...                          on_steps=[0], open_suppositions=[1])
    >>> s
    ['∨', ['p'], ['~', ['q']]]; I∨; [0]; [1]
    """
    def __init__(self, content, justification=None, on_steps=None, open_suppositions=None):
        if open_suppositions is None:
            open_suppositions = []
        super().__init__(content, justification, on_steps)
        self.open_suppositions = open_suppositions

    def unparse(self, parser):
        return f"{parser.unparse(self.content)}; {self.justification}; {self.on_steps}; {self.open_suppositions}"

    def __repr__(self):
        return f"{self.content}; {self.justification}; {self.on_steps}; {self.open_suppositions}"


class NaturalDeductionRule(Derivation):
    """Class for natural deduction rules.

    Extends :ref:`logics.classes.propositional.proof_theories.Derivation <derivation>`. A rule is basically a Derivation
    of NaturalDeductionStep's. The premises of the rule need not have justifications and on_steps (by default, they
    will be ``None`` and ``[]``). They can also have steps which are simply the string ``'(...)'``, which will mark that
    there can be any number of steps between the previous and the next.

    Examples
    --------
    Conditional introduction for classical logic will look like this:

    >>> from logics.utils.parsers import classical_parser
    >>> from logics.classes.propositional.proof_theories import NaturalDeductionStep, NaturalDeductionRule
    >>> cond_intro = NaturalDeductionRule([
    ...     '(...)',
    ...     NaturalDeductionStep(classical_parser.parse('A'), 'supposition', open_suppositions=[0]),
    ...     '(...)',
    ...     NaturalDeductionStep(classical_parser.parse('B'), open_suppositions=[0]),
    ...     NaturalDeductionStep(classical_parser.parse('A → B'), 'I→', [0, 1], open_suppositions=[])
    ... ])

    Since there is a ``'(...)'`` before `A`, that step need not be first step of the derivation. There can also be any
    number of steps between `A` and `B`. However, step `A → B` must come immetiately after `B` since there is no
    ``'(...)'`` inbetween.

    Also note that the indexes of the `on_step` and the `open_supposition` parameters within the rule ignore the
    ``'(...)'`` members. For example, the first step has ``open_suppositions=[0]`` which means that a supposition is
    being opened *in that step* (which is not index 0, but is step 0). The last step also has ``on_steps=[0,1]`` since
    the non-``'(...)'`` steps are the 0 and 1 steps.

    Finally, note that the ``'(...)'`` will not count for either the ``index`` or ``len`` methods, but will count for
    ``__getitem__``:

    >>> cond_intro.index(NaturalDeductionStep(classical_parser.parse('B'), open_suppositions=[0]))
    1
    >>> len(cond_intro)
    3
    >>> cond_intro[0]
    '(...)'
    """
    @property
    def premises(self):
        return [step.content for step in self[:-1] if step != '(...)']

    def index(self, obj, *args, **kwargs):
        """Index method obviates the (...) steps"""
        return [x for x in self if x != '(...)'].index(obj, *args, **kwargs)

    def __len__(self):
        return len([x for x in self if x != '(...)'])

    def __repr__(self):
        return Derivation([x for x in self if x != '(...)']).__repr__()


# ----------------------------------------------------------------------------------------------------------------------
# ----------------------------------------------------------------------------------------------------------------------


class NaturalDeductionSystem:
    """Class for natural deduction systems.

    Parameters
    ----------
    language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
        Instance of Language or InfiniteLanguage
    rules: dict (str: logics.classes.propositional.proof_theories.NaturalDeductionRule)
        The keys are strings (the name of the rule) and the values are NaturalDeductionRule

    Examples
    --------
    Example (toy) system with only conjunction rules:

    >>> from logics.utils.parsers import classical_parser
    >>> from logics.classes.propositional.proof_theories import NaturalDeductionStep, NaturalDeductionRule, NaturalDeductionSystem
    >>> from logics.instances.propositional.languages import classical_infinite_language
    >>> rules = {
    ... 'I∧': NaturalDeductionRule([
    ...     '(...)',
    ...     NaturalDeductionStep(classical_parser.parse('A')),
    ...     '(...)',
    ...     NaturalDeductionStep(classical_parser.parse('B')),
    ...     '(...)',
    ...     NaturalDeductionStep(classical_parser.parse('A ∧ B'), 'I∧', [0, 1], open_suppositions=[])
    ... ]),
    ...
    ... 'E∧1': NaturalDeductionRule([
    ...     '(...)',
    ...     NaturalDeductionStep(classical_parser.parse('A ∧ B')),
    ...     '(...)',
    ...     NaturalDeductionStep(classical_parser.parse('A'), 'E∧1', [0], open_suppositions=[])
    ... ]),
    ...
    ... 'E∧2': NaturalDeductionRule([
    ...     '(...)',
    ...     NaturalDeductionStep(classical_parser.parse('A ∧ B')),
    ...     '(...)',
    ...     NaturalDeductionStep(classical_parser.parse('B'), 'E∧2', [0], open_suppositions=[])
    ... ])}
    >>> toy_system = NaturalDeductionSystem(language=classical_infinite_language, rules=rules)

    For more realistic instances you may look at :ref:`instances <prop-nd-instances>` below. In the examples below we
    will be working with a full classical logic instance defined in

    >>> from logics.instances.propositional.natural_deduction import classical_natural_deduction_system
    """
    def __init__(self, language, rules):
        self.language = language
        self.rules = rules

    def is_correct_derivation(self, derivation, inference=None, return_error_list=False):
        """Determines if a derivation has been correctly performed.

        Will check that the steps with a justification of 'premise' are premises of inference, that every other step
        is obtained via the application of a rule to a previous step, and that the last step is the conclusion of
        inference.

        Parameters
        ----------
        derivation: logics.classes.propositional.proof_theories.Derivation
            The derivation the algorithm will look at
        inference: logics.classes.propositional.Inference or None, optional
            If None, will just check correct application of the rules. If an inference, will check that the steps
            labelled as 'premise' are premises of the inference, and that the last step is the conclusion of the
            inference
        return_error_list: bool, optional
            If False, will just return True or False (exits when it finds an error, more efficient) If True, will return
            a tuple (boolean, [error_list]) (computes all errors, does not exit on the first, less efficient)

        Examples
        --------
        A correct derivation of modus ponens using all the classical rules

        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.natural_deduction import classical_natural_deduction_system
        >>> inf = classical_parser.parse('q, p → q / q')
        >>> deriv = classical_parser.parse_derivation('''
        ... q; premise; []; []
        ... ~q; supposition; []; [1]
        ... ~q; repetition; [1]; [1]
        ... (q ∧ ~q); I∧; [0, 2]; [1]
        ... q; E∧1; [3]; [1]
        ... ⊥; E~; [1, 4]; [1]
        ... p; EFSQ; [5]; [1]
        ... ⊥; repetition; [5]; [1]
        ... ~~q; I~; [1, 7]; []
        ... q; ~~; [8]; []
        ... q; supposition; []; [10]
        ... q; repetition; [10]; [10]
        ... (q → q); I→; [10, 11]; []
        ... q; E→; [12, 9]; []
        ... (q ∨ p); I∨1; [13]; []
        ... (p → q); premise; []; []
        ... q; E∨; [14, 12, 15]; []''',
        ... natural_deduction=True)
        >>> classical_natural_deduction_system.is_correct_derivation(deriv, inf)
        True

        Using a step in a closed supposition (`inference` left as ``None``)

        >>> deriv2 = classical_parser.parse_derivation('''
        ... p; supposition; []; [0]
        ... p; repetition; [0]; [0]
        ... (p → p); I→; [0, 1]; []
        ... p; E→; [2, 0]; []''',
        ... natural_deduction=True)
        >>> correct, error_list = classical_natural_deduction_system.is_correct_derivation(deriv2, return_error_list=True)
        >>> correct
        False
        >>> error_list
        ['Step 3: Incorrect handling of suppositions in on_step 0, it is in a closed supposition']

        Incorrectly closing a supposition, with a rule that does not allow that

        >>> deriv3 = classical_parser.parse_derivation('''
        ... p; premise
        ... p; supposition; []; [1]
        ... p; repetition; [0]; [1]
        ... (p ∨ q); I∨1; [0]; []''',
        ... natural_deduction=True)
        >>> correct, error_list = classical_natural_deduction_system.is_correct_derivation(deriv3, return_error_list=True)
        >>> correct
        False
        >>> error_list
        ['Step 3: Incorrect handling of suppositions']
        """
        error_list = list()

        for step_index in range(len(derivation)):
            step = derivation[step_index]

            # If the justification is 'premise'
            if step.justification == 'premise':
                if inference is not None and step.content not in inference.premises:
                    if not return_error_list:
                        return False
                    else:
                        error_list.append(f"Step {step_index}: {step.content} was marked as 'premise', "
                                          f"but is not a premise of the inference given")
                # premise steps need to have the same supposition level than the previous step
                if step_index == 0:
                    if step.open_suppositions:
                        if not return_error_list:
                            return False
                        else:
                            error_list.append(f"Step 0: Incorrect supposition handling. "
                                              f"Premise steps do not open suppositions")
                else:
                    if step.open_suppositions != derivation[step_index-1].open_suppositions:
                        if not return_error_list:
                            return False
                        else:
                            error_list.append(f"Step {step_index}: Incorrect supposition handling")

            # The justification is 'supposition'
            elif step.justification == 'supposition':
                if step_index == 0:
                    if step.open_suppositions != [0]:
                        if not return_error_list:
                            return False
                        else:
                            error_list.append("Step 0: Incorrect supposition handling")
                else:
                    if not (step.open_suppositions[:-1] == derivation[step_index - 1].open_suppositions and
                            step.open_suppositions[-1] == step_index):
                        if not return_error_list:
                            return False
                        else:
                            error_list.append(f"Step {step_index}: Incorrect supposition handling")

            # If the justification is the name of a specific rule
            else:
                if step.justification not in self.rules:
                    if not return_error_list:
                        return False
                    else:
                        error_list.append(f"Step {step_index}: Justification is incorrect, must be either "
                                          f"'premise', 'supposition', or the name of a specific axiom or rule")

                correct, error = self.is_correct_application(derivation=derivation[:step_index+1], step=-1,  # last step
                                                             rule=self.rules[step.justification], return_error=True)
                if not correct:
                    if not return_error_list:
                        return False
                    else:
                        error_list.append(f'Step {step_index}: {error}')

        # Finally, checks if the last step is the conclusion of the inference
        if inference is not None and derivation.conclusion != inference.conclusion:
            if not return_error_list:
                return False
            else:
                error_list.append(f"Final step of the derivation is not the conclusion of the inference given")

        # If it gets to here either there are no errors, or there are some but return_error_list is True
        if not error_list:
            if not return_error_list:
                return True
            return True, error_list
        return False, error_list

    # ------------------------------------------------------------------------------------------------------------------

    def is_correct_application(self, derivation, step, rule, return_error=False):
        """Determines if a rule has been correctly applied at a particular derivation step.

        Parameters
        ----------
        derivation: logics.classes.propositional.proof_theories.Derivation
            The derivation in which the step is located
        step: int
            The index of the step in the derivation
        rule: logics.classes.propositional.proof_theories.NaturalDeductionRule
            The rule to check for correct application
        return_error: bool
            If False, the method will just return True or False. If True will also return a string detailing the error
            it found (just one, not a list)

        Examples
        --------
        A derivation with the first two steps correctly applied, and an incorrect third step

        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.natural_deduction import classical_natural_deduction_system
        >>> deriv = classical_parser.parse_derivation(
        ... '''p; supposition; []; [0]
        ... p; repetition; [0]; [0]
        ... (p → p); I→; [0, 1]; []
        ... p; E→; [2, 0]; []''',
        ... natural_deduction=True)
        >>> classical_natural_deduction_system.is_correct_application(deriv, 1, classical_natural_deduction_system.rules['repetition'])
        True
        >>> classical_natural_deduction_system.is_correct_application(deriv, 2, classical_natural_deduction_system.rules['I→'])
        True
        >>> classical_natural_deduction_system.is_correct_application(deriv, 3, classical_natural_deduction_system.rules['E→'])
        False
        >>> classical_natural_deduction_system.is_correct_application(deriv, 3, classical_natural_deduction_system.rules['E→'],
        ...                                                           return_error=True)
        (False, 'Incorrect handling of suppositions in on_step 0, it is in a closed supposition')
        """
        last_step = derivation[step]

        if len(last_step.on_steps) != len(rule) - 1:
            if not return_error:
                return False
            return False, "Number of on steps given are not equal to the number of rule premises"

        # Check that no on step is in the future
        for on_step in last_step.on_steps:
            if on_step >= len(derivation) - 1:
                if not return_error:
                    return False
                return False, f"On step {on_step} is greater or equal than the current step, must be lower"

        # Check that the conclusion and the premises of the derivation are instances of the rule
        # Conclusion
        if rule[-1].justification is not None and last_step.justification != rule[-1].justification:
            if not return_error:
                return False
            return False, f"Justification for step {derivation.index(last_step)} does not coincide with " \
                          f"the justification in the rule conclusion"

        instance, subst_dict = last_step.content.is_instance_of(rule[-1].content, self.language, return_subst_dict=True)
        if not instance:
            if not return_error:
                return False
            return False, f"Step {derivation.index(last_step)} is not an instance of the conclusion of the rule given"

        # Premises
        prev_step = -1  # For '(...)' checking
        # Establish which step corresponds to each rule premise
        step_correspondence_dict = {rule[-1].on_steps[index]: last_step.on_steps[index] for
                                    index in range(len(rule[-1].on_steps))}
        # For example, if rule on_steps for its conclusion has [1, 0, 2], and the last step of the derivation has
        # an on_steps of [2,4,6], step_correspondence_dict is: {0: 4, 1: 2, 2: 6}
        # The conclusion of the rule always corresponds to the last step of the derivation:
        step_correspondence_dict[len(rule) - 1] = derivation.index(last_step)

        # For supposition checking later on (see below):
        relevant_sup_dict = dict()

        for rule_step in rule[:-1]:
            if rule_step == '(...)':
                prev_step = None

            else:
                # Number of rule premise
                prem_number = rule.index(rule_step)  # index is overriden in NaturalDeductionRule to obviate (...) steps
                # Step to which it corresponds in the derivation, according to the step_correspondence_dict
                step_number = step_correspondence_dict[prem_number]

                # Check that the step is the one following the previous one (except None --> the previous step is (...))
                if prev_step is not None and step_number != prev_step + 1:
                    if not return_error:
                        return False
                    return False, f"On step {step_number} does not immediately follow the previous on step, " \
                                  f"as the rule requires"

                # Check that the justification is right
                # (Rule premises generally do not have justifications, but I include this just in case)
                if rule_step.justification is not None and \
                        derivation[step_number].justification != rule_step.justification:
                    if not return_error:
                        return False
                    return False, f"Justification for on step {step_number} does not coincide with " \
                                  f"the justification in rule premise {prem_number}"

                # Check that the content is instance of the content of the rule (self)
                result = derivation[step_number].content.is_instance_of(rule_step.content, self.language,
                                                                        subst_dict=subst_dict, return_subst_dict=True)
                instance = result[0]
                subst_dict.update(result[1])  # Again, for uniform substitution
                if not instance:
                    if not return_error:
                        return False
                    return False, f"On step {step_number} is not an instance of rule premise number {prem_number}"
                else:
                    prev_step = step_number  # Set the current step as the prev_step for the next iteration of the loop

                # For checking correct handling of suppositions in the rule:
                if rule_step.justification == 'supposition':
                    relevant_sup_dict[rule_step.open_suppositions[-1]] = step_correspondence_dict[prem_number]
                    # For example, if the rule_step is A, 'supposition', open_suppositions=[0]
                    # And the derivation step that instantiates this rule is step 4, then save that supposition 0 in the
                    # rule corresponds to supposition 4 in the derivation (i.e. relevant_sup_dict[0] = 4)

                # Check that supposition handling is correct
                # Wrt to the rule
                for relevant_step in relevant_sup_dict:
                    # Check that the open suppositions of the rule are indeed open in the derivation
                    if relevant_step in rule_step.open_suppositions and \
                            relevant_sup_dict[relevant_step] not in derivation[step_number].open_suppositions:
                        if not return_error:
                            return False
                        return False, f"Incorrect handling of suppositions in on_step {step_number}"
                    # Check that closed suppositions of the rule are not open in the derivation
                    if relevant_step not in rule_step.open_suppositions and \
                            relevant_sup_dict[relevant_step] in derivation[step_number].open_suppositions:
                        if not return_error:
                            return False
                        return False, f"Incorrect handling of suppositions in on_step {step_number}"

                # Outside the rule, no steps in closed suppositions are being used
                # (if the on_step has an open supposition, it must also be present in the conclusion, otherwise we are
                # using something in a closed supposition)
                for open_sup in derivation[step_number].open_suppositions:
                    if open_sup not in relevant_sup_dict.values():  # not a rule step
                        if open_sup not in last_step.open_suppositions:
                            if not return_error:
                                return False
                            return False, f"Incorrect handling of suppositions in on_step {step_number}, it " \
                                          f"is in a closed supposition"

        # Conclusion again (check that it immediately follows the last step, if it corresponds)
        if prev_step is not None and derivation.index(last_step) != prev_step + 1:
            if not return_error:
                return False
            return False, f"On step {derivation.index(last_step)} does not immediately follow the previous on_step"

        # Supposition checking in the conclusion
        for relevant_step in relevant_sup_dict:
            if relevant_step in rule[-1].open_suppositions and \
                    relevant_sup_dict[relevant_step] not in last_step.open_suppositions:
                if not return_error:
                    return False
                return False, f"Incorrect handling of suppositions"
            if relevant_step not in rule[-1].open_suppositions and \
                    relevant_sup_dict[relevant_step] in last_step.open_suppositions:
                if not return_error:
                    return False
                return False, f"Incorrect handling of suppositions"
        # Outside the rule suppositions, every supposition present in the previous step must still be open,
        # and vice versa (the conclusion step should not open any new suppositions not allowed by the rule)
        if [s1 for s1 in derivation[step-1].open_suppositions if s1 not in relevant_sup_dict.values()] != \
                [s2 for s2 in derivation[step].open_suppositions if s2 not in relevant_sup_dict.values()]:
            if not return_error:
                return False
            return False, f"Incorrect handling of suppositions"

        # If it got to here and did not return, the application is correct
        if not return_error:
            return True
        return True, ""

    @staticmethod
    def solve_derivation(inference, solver):
        """Take an inference and a solver, and returns a derivation for the former.

        The solver in question must have a ``solve`` method

        Examples
        --------
        >>> from logics.instances.propositional.natural_deduction import classical_natural_deduction_system
        >>> from logics.utils.solvers import classical_natural_deduction_solver
        >>> from logics.utils.parsers import classical_parser
        >>> deriv = classical_natural_deduction_system.solve_derivation(classical_parser.parse('p then q, ~q / ~p'),
        ...                                                             classical_natural_deduction_solver)
        >>> deriv.print_derivation(classical_parser)
        0. (p → q); premise; []
        1. ~q; premise; []
        |  2. p; supposition; []
        |  3. q; E→; [0, 2]
        |  4. ⊥; E~; [1, 3]
        5. ~p; I~; [2, 4]
        """
        return solver.solve(inference)
