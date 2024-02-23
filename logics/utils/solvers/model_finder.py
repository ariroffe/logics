from copy import deepcopy

from logics.classes.predicate.semantics import Model
from logics.classes.exceptions import SolverError


class ModelFinder:
    max_domain_cardinality = 3

    def find_model(self, formula, sought_value, logic):
        """Given a formula, a sought thuth value and a logic, returns a Model that assigns the sought value to the
        formula (if it can find one)

        Has an instance (``logics.utils.solvers.model_finder.classical_model_finder``) predefined

        Parameters
        ----------
        formula: logics.classes.predicate.Formula
            The Formula which must be given the sought value
        sought_value: str
            The truth value that will get assigned to the formula in the model (in the predefined instances, an str)
        logic: logics.classes.predicate.semantics.ModelTheory
            The model theory that the algorithm will utilize to construct a model

        Returns
        -------
        logics.classes.predicate.semantics.Model
            A Model instance

        Raises
        ------
        logics.classes.exceptions.SolverError
            If it cannot find a model that gives the desired value to the formula

        Examples
        --------
        >>> from logics.utils.parsers import classical_predicate_parser
        >>> from logics.utils.solvers.model_finder import classical_model_finder
        >>> from logics.instances.predicate.model_semantics import classical_model_semantics
        >>> f = classical_predicate_parser.parse("exists x P(x) and ~P(a)")
        >>> classical_model_finder.find_model(f, "1", classical_model_semantics)

        Notes
        -----
        - Will construct a model of at most cardinality ``max_domain_cardinality`` (class param)
        - For now it has only been tested with classical model theory, will probably need some adjustments for
          non-classical model theories
        - For now does not work with function symbols
        """
        predicates = formula.predicates_inside()
        ind_constants = sorted(list(formula.individual_constants_inside(logic.language)))
        model = self._get_initial_model(ind_constants, predicates)
        requirements = [Requirement(formula, sought_value)]

        # Now try to find the model adding from 0 to 5 extra elements to the domain
        for add_cts in range(self.max_domain_cardinality):
            # If there are n individual constants, then '1', '2', ... 'n' are already in the domain, otherwise '1'
            # so, e.g. when add_cts is 1 and domain is {'1', '2'}, will add '3', if add_cts is 2 will ad '3', '4'
            for _ in range(add_cts):
                model['domain'].add(str(len(model['domain'])+1))

            # Might stop before the loop since we might already have elements in the domain bc of ind constants
            if len(model['domain']) > self.max_domain_cardinality:
                raise SolverError("Could not find model for the sentence provided")

            try:
                positive_atomic_requirements, negative_atomic_requirements = self._analyze_requirements(
                    requirements, model, logic
                )
                print(positive_atomic_requirements, negative_atomic_requirements)
                return model

            except ValueError:
                pass

        raise SolverError("Could not find model for the sentence provided")

    def _get_initial_model(self, ind_constants, predicates):
        # Constructs a model with as many elems in the domain as ind constants (1 if none) and an empty denot for preds
        model = Model({'domain': {"1"}})

        # Introduce as many objects to the domain as there are individual constants, 1 element if there are none
        if ind_constants:
            for idx, ind_ct in enumerate(ind_constants):
                model['domain'].add(str(idx + 1))  # '1' is already present, if only 1 ind ct this does nothing
                model[ind_ct] = str(idx + 1)

        # Add the predicates to the model with an empty extension for now
        for pred in predicates:
            model[pred] = set()

        return model

    def _analyze_requirements(self, requirements, model, logic, positive_atomic_reqs=None, negative_atomic_reqs=None,
                              free_variable_denotation_dict=None):
        if positive_atomic_reqs is None:
            positive_atomic_reqs = dict()  # that certain element/s should be in the extension of some predicate
            negative_atomic_reqs = dict()  # that certain element/s should be in the antiextension of some predicate
            # Both will have form {'P': {elem1, elem2}, 'R': {(elem1, elem2), ...}} if P unary and R binary
            free_variable_denotation_dict = dict()

        while requirements:
            req = requirements[0]  # The requirement we are analyzing now, we will delete it after we are done with it

            # Atomic formula
            if req.formula.is_atomic:
                try:
                    self._analyze_atomic_requirement(req, model, positive_atomic_reqs, negative_atomic_reqs,
                                                     free_variable_denotation_dict)
                    del requirements[0]
                except ValueError as e:
                    raise e

            # Unary connective formula
            elif req.formula[0] in logic.language.constants(1):
                try:
                    positive_atomic_reqs, negative_atomic_reqs = \
                        self._analyze_unary_connective_requirement(requirements, req, model, logic,
                                                                   positive_atomic_reqs, negative_atomic_reqs,
                                                                   free_variable_denotation_dict)
                    del requirements[0]
                except ValueError as e:
                    raise e

        return positive_atomic_reqs, negative_atomic_reqs

    def _analyze_atomic_requirement(self, requirement, model, positive_atomic_reqs, negative_atomic_reqs,
                                    free_variable_denotation_dict):
        # Will modify the positive_atomic and negative_atomic reqs dicts instead of returning
        formula = requirement.formula
        predicate = formula[0]
        predicate_arity = len(formula) - 1  # one position is the predicate
        arguments = formula[1:]
        sought_value = requirement.value

        # Unary predicate
        if predicate_arity == 1:
            args_denotation = model.denotation(arguments[0], free_variable_denotation_dict)
        # n>1-ary predicate
        else:
            args_denotation = tuple(model.denotation(x, free_variable_denotation_dict) for x in arguments)

        # Check if contradictions and add new requirements
        if sought_value == '1':
            # Check if contradiction
            if predicate in negative_atomic_reqs and args_denotation in negative_atomic_reqs[predicate]:
                raise ValueError("Contradiction in atomic requirements")
            # Add the atomic requirement
            if predicate not in positive_atomic_reqs:
                positive_atomic_reqs[predicate] = {args_denotation}
            else:
                positive_atomic_reqs[predicate].add(args_denotation)
        elif sought_value == '0':
            # Check if contradiction
            if predicate in positive_atomic_reqs and args_denotation in positive_atomic_reqs[predicate]:
                raise ValueError("Contradiction in atomic requirements")
            # Add the atomic requirement
            if predicate not in negative_atomic_reqs:
                negative_atomic_reqs[predicate] = {args_denotation}
            else:
                negative_atomic_reqs[predicate].add(args_denotation)

    def _analyze_unary_connective_requirement(self, all_requirements, requirement, model, logic, positive_atomic_reqs,
                                              negative_atomic_reqs, free_variable_denotation_dict):
        formula = requirement.formula
        connective = formula.main_symbol
        sought_value = requirement.value

        # We need to check the truth function for the connective and try every requirement that results in the sentence
        # getting the sought value
        for t_value in logic.truth_values:
            if logic.apply_truth_function(connective, t_value) == sought_value:
                try:
                    # Add a new requirement and remove the current one we are analyzing
                    new_requirements = [Requirement(formula=formula[1], value=t_value), *all_requirements[1:]]

                    # Call recursively and see if it returns. Send copies of everything in case it does not
                    positive_atomic_reqs, negative_atomic_reqs = self._analyze_requirements(
                        new_requirements, model, logic, deepcopy(positive_atomic_reqs), deepcopy(negative_atomic_reqs),
                        free_variable_denotation_dict
                    )
                    return positive_atomic_reqs, negative_atomic_reqs
                except ValueError:
                    pass
        # If we reach here, we found no value that will satisfy the requirement
        raise ValueError("Unsatisfiable unary requirement")


class Requirement:
    """Requirement that a formula should get a given value"""
    def __init__(self, formula, value):
        self.formula = formula
        self.value = value

    def __str__(self):
        return f"Requirement - formula: {self.formula}, value: {self.value}"


classical_model_finder = ModelFinder()
