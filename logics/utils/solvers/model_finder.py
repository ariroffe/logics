from logics.classes.predicate.semantics import Model


class ModelFinder:
    def find_model(self, formula, sought_value, logic):
        """Given a formula, a sought thuth value and a logic, returns a Model that assigns the sought value to the
        formula (if it can find one)

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
        """
        predicates = formula.predicates_inside()
        ind_constants = sorted(list(formula.individual_constants_inside(logic.language)))
        model = self._get_initial_model(ind_constants, predicates)
        return model

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


model_finder = ModelFinder()
