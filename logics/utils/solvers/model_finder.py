from copy import copy, deepcopy
from itertools import product

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
        {'domain': {'1', '2'}, 'a': '1', 'P': {'2'}}
        >>> classical_model_finder.find_model(f, "0", classical_model_semantics)
        {'domain': {'1'}, 'a': '1', 'P': {'1'}}

        Notes
        -----
        - Will construct a model of at most cardinality ``max_domain_cardinality`` (class param)
        - For now it has only been tested with classical model theory, will probably need some adjustments for
          non-classical model theories
        - For now does not work with function symbols
        - Will not work with open formulae
        """
        predicates = formula.predicates_inside()
        ind_constants = sorted(list(formula.individual_constants_inside(logic.language)))
        requirements = [Requirement(formula, sought_value)]

        # Now try to find the model adding from 0 to 5 extra elements to the domain
        for add_cts in range(self.max_domain_cardinality):
            model = self._get_initial_model(ind_constants, predicates)
            if add_cts:  # if it is not 0, add an extra element to the domain
                model['domain'].add(str(len(model['domain'])+1))

            # print(f"\nAttempt with domain {model['domain']}, initial model {model}")
            # Might stop before the loop since we might already have elements in the domain bc of ind constants
            if len(model['domain']) > self.max_domain_cardinality:
                raise SolverError("Could not find model for the sentence provided")

            try:
                positive_atomic_requirements, negative_atomic_requirements = self._analyze_requirements(
                    requirements, model, logic
                )
                self.assign_model_predicates(model, positive_atomic_requirements)
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

    def _analyze_requirements(self, requirements, model, logic, positive_atomic_reqs=None, negative_atomic_reqs=None):
        if positive_atomic_reqs is None:
            positive_atomic_reqs = dict()  # that certain element/s should be in the extension of some predicate
            negative_atomic_reqs = dict()  # that certain element/s should be in the antiextension of some predicate
            # Both will have form {'P': {elem1, elem2}, 'R': {(elem1, elem2), ...}} if P unary and R binary

        while requirements:
            req = requirements[0]  # The requirement we are analyzing now, we will delete it after we are done with it

            # Atomic formula
            if req.formula.is_atomic:
                try:
                    self._analyze_atomic_requirement(req, model, positive_atomic_reqs, negative_atomic_reqs)
                    del requirements[0]
                except ValueError as e:
                    raise e

            # Unary connective formula
            elif req.formula[0] in logic.language.constants(1):
                try:
                    positive_atomic_reqs, negative_atomic_reqs = \
                        self._analyze_unary_connective_requirement(requirements, req, model, logic,
                                                                   positive_atomic_reqs, negative_atomic_reqs)
                    del requirements[0]
                except ValueError as e:
                    raise e

            # Binary connective formula
            elif req.formula[0] in logic.language.constants(2):
                try:
                    positive_atomic_reqs, negative_atomic_reqs = \
                        self._analyze_binary_connective_requirement(requirements, req, model, logic,
                                                                   positive_atomic_reqs, negative_atomic_reqs)
                    del requirements[0]
                except ValueError as e:
                    raise e

            # Quantified formula
            elif req.formula[0] in logic.language.quantifiers:
                try:
                    positive_atomic_reqs, negative_atomic_reqs = \
                        self._analyze_quantifier_requirement(requirements, req, model, logic,
                                                             positive_atomic_reqs, negative_atomic_reqs)
                    del requirements[0]
                except ValueError as e:
                    raise e

            else:
                raise SolverError(f"Unknown logical constant {req.formula[0]}")

        return positive_atomic_reqs, negative_atomic_reqs

    def _analyze_atomic_requirement(self, requirement, model, positive_atomic_reqs, negative_atomic_reqs):
        # Will modify the positive_atomic and negative_atomic reqs dicts instead of returning
        formula = requirement.formula
        predicate = formula[0]
        predicate_arity = len(formula) - 1  # one position is the predicate
        arguments = formula[1:]
        sought_value = requirement.value
        variable_assignment = requirement.variable_assignment

        # Unary predicate
        if predicate_arity == 1:
            args_denotation = model.denotation(arguments[0], variable_assignment)
        # n>1-ary predicate
        else:
            args_denotation = tuple(model.denotation(x, variable_assignment) for x in arguments)

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
                                              negative_atomic_reqs):
        formula = requirement.formula
        connective = formula.main_symbol
        sought_value = requirement.value
        prev_variable_assignment = requirement.variable_assignment

        # We need to check the truth function for the connective and try every requirement that results in the sentence
        # getting the sought value
        for t_value in logic.truth_values:
            if logic.apply_truth_function(connective, t_value) == sought_value:
                # Add a new requirement and remove the current one we are analyzing
                new_requirements = [Requirement(formula=formula[1], value=t_value,
                                                variable_assignment=prev_variable_assignment),
                                    *all_requirements[1:]]
                try:
                    # Call recursively and see if it returns. Send copies of everything in case it does not
                    positive_atomic_reqs, negative_atomic_reqs = self._analyze_requirements(
                        new_requirements, model, logic, deepcopy(positive_atomic_reqs), deepcopy(negative_atomic_reqs)
                    )
                    return positive_atomic_reqs, negative_atomic_reqs
                except ValueError:
                    pass
        # If we reach here, we found no value that will satisfy the requirement
        raise ValueError("Unsatisfiable unary requirement")

    def _analyze_binary_connective_requirement(self, all_requirements, requirement, model, logic, positive_atomic_reqs,
                                              negative_atomic_reqs):
        formula = requirement.formula
        connective = formula.main_symbol
        sought_value = requirement.value
        prev_variable_assignment = requirement.variable_assignment

        # We need to check the truth function for the connective and try every PAIR of requirements that results in the
        # sentence getting the sought value
        for t_value1 in logic.truth_values:
            for t_value2 in logic.truth_values:
                if logic.apply_truth_function(connective, t_value1, t_value2) == sought_value:
                    # Add TWO new requirements and remove the current one we are analyzing
                    new_requirements = [
                        Requirement(formula=formula[1], value=t_value1, variable_assignment=prev_variable_assignment),
                        Requirement(formula=formula[2], value=t_value2, variable_assignment=prev_variable_assignment),
                        *all_requirements[1:]
                    ]
                    try:
                        # Call recursively and see if it returns. Send copies of everything in case it does not
                        positive_atomic_reqs, negative_atomic_reqs = self._analyze_requirements(
                            new_requirements, model, logic, deepcopy(positive_atomic_reqs),
                            deepcopy(negative_atomic_reqs)
                        )
                        return positive_atomic_reqs, negative_atomic_reqs
                    except ValueError:
                        pass
        # If we reach here, we found no value that will satisfy the requirement
        raise ValueError("Unsatisfiable unary requirement")

    def _analyze_quantifier_requirement(self, all_requirements, requirement, model, logic, positive_atomic_reqs,
                                              negative_atomic_reqs):
        formula = requirement.formula
        quantifier = formula[0]
        quantified_variable = formula[1]
        subf = formula[2]
        sought_value = requirement.value
        prev_variable_assignment = requirement.variable_assignment

        new_variable_assignment = copy(prev_variable_assignment)
        if quantified_variable in new_variable_assignment:
            # If in a nested quantifier on a variable that was previously bound before
            # Then the current quantifier binds it, it becomes free inside subf
            del new_variable_assignment[quantified_variable]
        # there should only be one free var
        free_var = next(iter(subf.free_variables(logic.language, _bound_variables=set(new_variable_assignment))))
        if not free_var:
            # If the quantifier is not binding anything, then it does not add any atomic requirement
            return positive_atomic_reqs, negative_atomic_reqs

        domain = sorted(list(model['domain']))
        possible_variable_assignments = [{free_var: elem, **new_variable_assignment} for elem in domain]
        # If x is free here and y was bound before, the above should give [{x: obj1, y:objn}, {x: obj2, y:objn}, ...]

        possible_truth_value_combinations_for_instances = product(logic.truth_values, repeat=len(domain))
        # if there are 3 elems in the domain, then the instances can get values (1, 1, 1), (1, 1, 0), (1, 0, 1), ...

        # See which combinations of truth values result in the quantified formula getting the desired value
        for value_comb in possible_truth_value_combinations_for_instances:
            v = value_comb[0]
            for v2 in value_comb[1:]:
                if quantifier == '∃':
                    v = logic.apply_truth_function('∨', v, v2)  # Treat existentials as disjunctions
                if quantifier == '∀':
                    v = logic.apply_truth_function('∧', v, v2)  # Treat universals as conjunctions

            # If it does get the value:
            if v == sought_value:
                # Then we need to add as requisites the instances with the appropriate var assignment
                new_requirements = [Requirement(formula=subf,
                                                value=value_comb[idx],
                                                variable_assignment=possible_variable_assignments[idx])
                                    for idx in range(len(domain))]
                new_requirements = [*new_requirements, *all_requirements[1:]]
                try:
                    positive_atomic_reqs, negative_atomic_reqs = self._analyze_requirements(
                        new_requirements, model, logic, deepcopy(positive_atomic_reqs),
                        deepcopy(negative_atomic_reqs)
                    )
                    return positive_atomic_reqs, negative_atomic_reqs
                except ValueError:
                    pass

        # If we reach here, we found no value that will satisfy the requirement
        raise ValueError("Unsatisfiable quantifier requirement")

    def assign_model_predicates(self, model, positive_atomic_requirements):
        for pred in positive_atomic_requirements:
            model[pred] = positive_atomic_requirements[pred]


class Requirement:
    """Requirement that a formula should get a given value with a given variable assignment"""
    def __init__(self, formula, value, variable_assignment=None):
        if variable_assignment is None:
            variable_assignment = dict()
        self.variable_assignment = variable_assignment
        self.formula = formula
        self.value = value

    def __repr__(self):
        return f"(Requirement - formula: {self.formula}, value: {self.value}, variables: {self.variable_assignment})"


classical_model_finder = ModelFinder()
