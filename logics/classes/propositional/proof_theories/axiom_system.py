from logics.classes.propositional import Inference
from logics.classes.errors import ErrorCode, CorrectionError


class AxiomSystem:
    """Class for obtaining axiom systems

    Parameters
    ----------
    language: language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
        Instance of Language or InfiniteLanguage
    axioms: dict (str: logics.classes.propositional.Formula)
        The keys are strings (the name of the axiom) and the values are (schematic) Formula
    rules: dict (str: logics.classes.propositional.Inference)
        The keys are strings (the name of the rule) and the values are (schematic) Inference

    Examples
    --------
    Classical propositional logic with only negation and conditional

    >>> from logics.utils.parsers import classical_parser
    >>> from logics.classes.propositional.proof_theories import AxiomSystem
    >>> from logics.instances.propositional.languages import classical_infinite_language_only_negation_conditional
    >>> axioms = {
    ... 'ax1': classical_parser.parse('A → (B → A)'),
    ... 'ax2': classical_parser.parse('(A → (B → C)) → ((A → B) → (A → C))'),
    ... 'ax3': classical_parser.parse('(~A → ~B) → (B → A)')
    ... }
    >>> rules = {'mp': classical_parser.parse('A, A → B / B')}
    >>> classical_logic_axiom_system = AxiomSystem(language=classical_infinite_language_only_negation_conditional,
    ...                                            axioms=axioms, rules=rules)

    This particular instance is also predefined in the `instances` module

    >>> from logics.instances.propositional.axiom_systems import classical_logic_axiom_system
    """
    def __init__(self, language, axioms, rules):
        self.language = language
        self.axioms = axioms
        self.rules = rules

    def is_correct_derivation(self, derivation, inference=None, return_error_list=False, exit_on_first_error=False):
        """Determines if a derivation has been correctly performed.

        Will check that the steps with a justification of 'premise' are premises of inference, that every other step
        is obtained by instantiating an axiom or via the application of a rule to a previous step, and that the
        last step is the conclusion of inference. For axioms, you may write the specific name of the axiom, or just
        write down 'axiom' and this will check all axioms

        Parameters
        ----------
        derivation: logics.classes.propositional.proof_theories.Derivation
            The derivation the algorithm will look at
        inference: logics.classes.propositional.Inference or None
            If None, will just check correct application of the rules. If an inference, will check that the steps
            labelled as 'premise' are premises of the inference, and that the last step is the conclusion of the
            inference
        return_error_list: bool
            If False, will just return True or False (exits when it finds an error, more efficient) If True, will return
            (True, a list of ``logics.classes.errors.CorrectionError``)
        exit_on_first_error: bool, optional
            If `return_error_list` and this are both true, it will return a list with a single error instead of many.
            More efficient, since it makes early exits.

        Examples
        --------
        Demostration of / p → p

        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.axiom_systems import classical_logic_axiom_system
        >>> i = classical_parser.parse('/ p → p')
        >>> deriv = classical_parser.parse_derivation('''
        ... p → ((p → p) → p); ax1
        ... (p → ((p → p) → p)) → ((p → (p → p)) → (p → p)); ax2
        ... p → (p → p); ax1
        ... ((p → (p → p)) → (p → p)); mp; [0,1]
        ... p → p; mp; [2,3]''')
        >>> classical_logic_axiom_system.is_correct_derivation(deriv, i)
        True

        Using 'axiom' instead of the name of the specific axiom

        >>> deriv2 = classical_parser.parse_derivation('''
        ... p → ((p → p) → p); axiom
        ... (p → ((p → p) → p)) → ((p → (p → p)) → (p → p)); axiom
        ... p → (p → p); axiom
        ... ((p → (p → p)) → (p → p)); mp; [0,1]
        ... p → p; mp; [2,3]''')
        >>> classical_logic_axiom_system.is_correct_derivation(deriv2, i)
        True

        An incorrect derivation

        >>> deriv3 = classical_parser.parse_derivation('''
        ... p → ((p → p) → p); axiom
        ... (p → ((p → p) → p)) → ((p → (p → p)) → (p → p)); axiom
        ... p → p; mp; [0,1]''')
        >>> classical_logic_axiom_system.is_correct_derivation(deriv3, i)
        False
        >>> correct, error_list = classical_logic_axiom_system.is_correct_derivation(deriv3, i, return_error_list=True)
        >>> error_list
        [2: ['→', ['p'], ['p']] was marked as mp, but it is not a correct application of that rule]
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
                        error_list.append(CorrectionError(code=ErrorCode.AX_INCORRECT_PREMISE, index=step_index,
                                                          description=f"{step.content} was marked as 'premise', "
                                                                      f"but is not a premise of the inference given"))
                        if exit_on_first_error:
                            return False, error_list

            # If the justification is 'axiom'
            elif step.justification == 'axiom':
                is_instance_of_axiom = False
                for axiom in self.axioms.values():
                    if step.content.is_instance_of(axiom, self.language):
                        is_instance_of_axiom = True
                        break
                if not is_instance_of_axiom:
                    if not return_error_list:
                        return False
                    else:
                        error_list.append(CorrectionError(code=ErrorCode.AX_INCORRECT_AXIOM, index=step_index,
                                                          description=f"{step.content} was marked as 'axiom', but is "
                                                                      f"not an instance of any axiom of the system"))
                        if exit_on_first_error:
                            return False, error_list

            # If the justification is the name of a speficic axiom
            elif step.justification in self.axioms:
                if not step.content.is_instance_of(self.axioms[step.justification], self.language):
                    if not return_error_list:
                        return False
                    else:
                        error_list.append(CorrectionError(code=ErrorCode.AX_INCORRECT_AXIOM, index=step_index,
                                                          description=f"{step.content} was marked as "
                                                                      f"{step.justification}, but is not an instance "
                                                                      f"of that axiom"))
                        if exit_on_first_error:
                            return False, error_list

            # If the justification is the name of a specific rule
            elif step.justification in self.rules:
                # Build an Inference with the on_steps as premises and this step as the conclusion
                inf_premises = []
                for on_step in step.on_steps:
                    inf_premises.append(derivation[on_step].content)
                inf = Inference(inf_premises, [step.content])
                # And check if this inference is an instance of the proposed rule
                if not inf.is_instance_of(self.rules[step.justification], self.language, order=False):
                    if not return_error_list:
                        return False
                    else:
                        error_list.append(CorrectionError(code=ErrorCode.AX_RULE_INCORRECTLY_APPLIED, index=step_index,
                                                          description=f"{step.content} was marked as "
                                                                      f"{step.justification}, but it is not a correct "
                                                                      f"application of that rule"))
                        if exit_on_first_error:
                            return False, error_list

            # If none of the above, then the justification is incorrect
            else:
                if not return_error_list:
                    return False
                else:
                    error_list.append(CorrectionError(code=ErrorCode.AX_INCORRECT_JUSTIFICATION, index=step_index,
                                                      description="Justification is incorrect, must be either 'premise'"
                                                                  ", 'axiom', or the name of a specific axiom or rule"))
                    if exit_on_first_error:
                        return False, error_list

        # Now check if the last step is the conclusion of the inference
        if inference is not None and not derivation.conclusion == inference.conclusion:
            if not return_error_list:
                return False
            else:
                error_list.append(CorrectionError(code=ErrorCode.AX_INCORRECT_CONCLUSION, index=len(derivation)-1,
                                                  description="Final step of the derivation is not the conclusion of "
                                                              "the inference given"))
                if exit_on_first_error:
                    return False, error_list

        # If it gets here either there are no errors, or there are some but return_error_list is True
        if not error_list:
            if not return_error_list:
                return True
            return True, error_list
        return False, error_list

    def solve_derivation(self, inference):
        # Should take an inference and return a derivation for it
        raise NotImplementedError()

    def is_valid(self, inference):
        # Should take an inference and return True if solve_derivation finds a derivation, False otherwise
        raise NotImplementedError()
