from copy import deepcopy

from logics.classes.propositional.proof_theories.sequents import Sequent, SequentNode
from logics.classes.exceptions import SolverError


class SequentReducer:
    """Solver for sequent calculi

    Parameters
    ----------
    max_apparitions_per_side: int or None, optional
        In case you want to limit the number of apparitions of a formula in a side, set it to an `int`. Otherwise,
        leave it as ``None`` (default). Useful for when you have contraction as a solver rule and want n-reduced
        sequents (see Paoli, Substructural Logics: A Primer)
    smart_weakening: bool, optional
        If ``True`` (default value), at every step of the reduction, will look for a formula present in all sides.
        If it finds it, starts from there and weakens its way into the current sequent to reduce. Makes the reducer
        faster in some contexts.
    weakening_rule_names: dict {int: str}
        If `smart_weakening` is activated, you need to tell it the name of the rule to use in each side when appliying
        weakening. For example, ``weakening_rule_names = {0: 'WL', 1: 'WR'}`` (the key should be the index of the side)
    """

    def __init__(self, max_apparitions_per_side=None, smart_weakening=True, weakening_rule_names=None):
        self.max_apparitions_per_side = max_apparitions_per_side
        self.smart_weakening = smart_weakening
        self.weakening_rule_names = weakening_rule_names
        # Will not take a SequentCalculus as argument because the same solver may work for more than one system

    def reduce(self, sequent, sequent_calculus, premises=None, max_depth=100):
        """Reduces a sequent using the rules of the system given, and returns a tree (a SequentNode with children).

        Will return the first reduction tree of a sequent that it finds, but there may be more. If it does not find any,
        will raise ``SolverError``.

        Parameters
        ----------
        sequent: logics.classes.propositional.proof_theories.Sequent
            The sequent to reduce
        sequent_calculus: logics.classes.propositional.proof_theories.SequentCalculus
            The sequent calculus from which the rules are used
        premises: list of logics.classes.propositional.proof_theories.Sequent, optional
            An optional list of sequents to use as premises, additionally to the axioms
        max_depth: int, optional
            The maximum depth that a tree can have. If it hits it, exits with a SolverError. Defaults to 100

        Raises
        ------
        logics.classes.exceptions.SolverError
            If it cannot find a reduction for the given sequent or hits the max_depth limit

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.sequents import LKminEA
        >>> from logics.utils.solvers.sequents import LKminEA_sequent_reducer
        >>> seq = classical_parser.parse('Gamma ==> Delta, (A or not A)')
        >>> tree= LKminEA_sequent_reducer.reduce(seq, LKminEA)
        >>> tree.print_tree(classical_parser)
        Γ ⇒ Δ, (A ∨ ~A) (∨R1)
        └── Γ ⇒ Δ, A, ~A (~R)
            └── Γ, A ⇒ Δ, A (WR)
                └── Γ, A ⇒ A (WL)
                    └── A ⇒ A (identity)
        >>> seq2 = classical_parser.parse('Gamma ==> Delta, (A and not A)')
        >>> LKminEA_sequent_reducer.reduce(seq2, LKminEA)
        Traceback (most recent call last):
        ...
        logics.classes.exceptions.SolverError: Could not find reduction for [['Γ'], ['Δ', ['∧', ['A'], ['~', ['A']]]]]
        >>> seq3 = classical_parser.parse('A, ~B ==>')
        >>> tree3 = LKminEA_sequent_reducer.reduce(seq3, LKminEA, premises=[classical_parser.parse("A ==> B")])
        >>> tree3.print_tree(classical_parser)
        A, ~B ⇒  (~L)
        └── A ⇒ B (premise)
        """
        if premises is None:
            premises = list()
        reduction, failed_reductions = self._standard_reduce(sequent, sequent_calculus, premises, max_depth)
        if reduction is None:
            raise SolverError(f'Could not find reduction for {sequent}')

        return reduction

    def _standard_reduce(self, sequent, sequent_calculus, premises, max_depth,
                         present_sequents=None, failed_reductions=None):
        """
        Simply checks for each rule in sequent_calculus.solver_rule_order (should be a list of strings (rule names)
        is applicable to sequent, and then instantiates and reduces the premises.
        For better efficiency, if it fails a reduction saves the result and does not try it again later on.
        Will also avoid repeating a sequent in a branch

        Will return the first complete reduction it finds. If it finds none, will return (None, failed_reductions)
        """
        # print('-' * (100-max_depth), sequent)
        # print(sequent)
        if max_depth == 0:
            return None, failed_reductions
        if failed_reductions is None:
            failed_reductions = list()
        if present_sequents is None:
            present_sequents = list()

        # First check if the sequent given is a premise or an axiom
        for premise in premises:
            if sequent == premise:
                return SequentNode(content=sequent, justification='premise'), failed_reductions
        for axiom_name in sequent_calculus.axioms:
            if sequent_calculus.sequent_is_axiom(sequent, axiom_name):
                return SequentNode(content=sequent, justification= axiom_name), failed_reductions

        # Smart weakening
        if self.smart_weakening:
            weakening_reduction = self._smart_weakening(sequent, sequent_calculus, premises)
            if weakening_reduction is not None:
                return weakening_reduction, failed_reductions

        # If not an axiom, check if the sequent is an instance of the conclusion of every rule
        for rule_name in sequent_calculus.solver_rule_order:
            rule = sequent_calculus.rules[rule_name]
            instance, possible_subst_dicts = sequent.is_instance_of(rule.content, sequent_calculus.language,
                                                                    return_subst_dicts=True)
            if instance:
                # print('\t', rule_name, 'applicable to', sequent)
                new_node = SequentNode(content=sequent, justification=rule_name)

                # Get all the possible premise instantiations. Do this first because:
                # - some possible dicts may yield different premise instantiations, but others may yield the same
                # - in the latter case, we do not want to try the same list of premises more than once
                possible_premise_instantiations = list()
                for subst_dict in possible_subst_dicts:
                    exit_dict = False
                    rule_premises = list()
                    for rule_premise in rule.children:
                        instantiated_premise = rule_premise.content.instantiate(sequent_calculus.language, subst_dict)
                        # Check if the premise is already in the path, or if a previous attempt of reduction failed
                        if instantiated_premise == sequent or instantiated_premise in present_sequents or \
                                instantiated_premise in failed_reductions:
                            exit_dict = True
                            break
                        # Check for the maximum number of apparitions of a formula
                        if not self._check_max_apparitions(instantiated_premise):
                            exit_dict = True
                            break
                        rule_premises.append(instantiated_premise)
                    if not exit_dict and rule_premises not in possible_premise_instantiations:
                        possible_premise_instantiations.append(rule_premises)

                # Now, for each set of possible premises of the rule, attempt a reduction
                correct_reduction = True
                # print('\t', 'instantiated premises', possible_premise_instantiations)
                for instantiated_premises in possible_premise_instantiations:
                    for instantiated_premise in instantiated_premises:
                        # print('\t\t', 'attempting reduction of', instantiated_premise)
                        if instantiated_premise not in failed_reductions:
                            premise_reduction, failed_reductions = self._standard_reduce(instantiated_premise,
                                                                          sequent_calculus,
                                                                          premises=premises,
                                                                          max_depth=max_depth-1,
                                                                          present_sequents=present_sequents + [sequent],
                                                                          failed_reductions=failed_reductions)
                            # The reduction failed (the method returned None)
                            if premise_reduction is None:
                                correct_reduction = False
                                if instantiated_premise not in failed_reductions:
                                    failed_reductions.append(instantiated_premise)
                                break
                            # Premise reduction is a node (which may contain children)
                            premise_reduction.parent = new_node

                    if correct_reduction:
                        return new_node, failed_reductions

        # If neither of the above, the sequent cannot be reduced, raise SolverError
        # print('\t\t', 'exit reduction of', sequent)
        return None, failed_reductions

    def _check_max_apparitions(self, sequent):
        """Checks that no formula appears more than max_apparitions_per_side in a sequent"""
        if self.max_apparitions_per_side:
            for side in sequent:
                for elem in side:
                    # NO - Check for context variables as well, since we are allowing to contract them in LKminEA
                    # if elem not in sequent_calculus.language.context_variables and \
                    #         side.count(elem) > self.max_apparitions_per_side:
                    #     return False
                    if side.count(elem) > self.max_apparitions_per_side:
                        return False
        return True

    def _smart_weakening(self, sequent, sequent_calculus, premises):
        """
        Will look for a formula present in all sides, and return a reduction of it applying weakening
        """
        # Check if any premises content is already present, to start from it
        for premise in premises:
            premise_present = True
            for side_index in range(premise.sides):
                for premise_elem in premise[side_index]:
                    if premise_elem not in sequent[side_index]:
                        premise_present = False
                        break
            if premise_present:
                initial_sequent = premise
                new_node = SequentNode(content=initial_sequent, justification='premise')
                for side_number in range(premise.sides):
                    new_node = self._weaken_from_premise(premise, sequent, side_number, new_node)
                return new_node

        # Look for a formula present in all sides, to start from identity
        first_side = sequent[0]
        for elem in first_side:
            # If it is a formula
            if elem not in sequent_calculus.language.context_variables:
                present_in_all_sides = True
                for side in sequent[1:]:
                    if elem not in side:
                        present_in_all_sides = False
                        break

                if present_in_all_sides:
                    initial_sequent = Sequent([[elem] for _ in range(sequent.sides)])  # This gives [[A], ..., [A]]
                    new_node = SequentNode(content=initial_sequent, justification='identity')
                    for side_number in range(sequent.sides):
                        new_node = self._weaken_from_identity(elem, sequent, side_number, new_node)
                    return new_node
        return None

    def _weaken_from_identity(self, formula, target_sequent, side_number, new_node):
        """
        Takes a formula (the one that will be in the identity axiom), a sequent (the one we want to reach) and generates
        a path of SequentNodes from the initial node to sequent.
        """
        target_side = target_sequent[side_number]
        formula_index = target_side.index(formula)  # First apparition of the formula in the formula

        # We need to weaken in order, so first let's do backwards from index to 0
        for index_left in range(formula_index-1, -1, -1):
            new_sequent = deepcopy(new_node.content)
            new_sequent[side_number].insert(0, target_side[index_left])
            new_node = SequentNode(content=new_sequent, justification=self.weakening_rule_names[side_number],
                                   children=[new_node])

        # Now walk forward from index
        for index_right in range(formula_index + 1, len(target_side)):
            new_sequent = deepcopy(new_node.content)
            new_sequent[side_number].append(target_side[index_right])
            new_node = SequentNode(content=new_sequent, justification=self.weakening_rule_names[side_number],
                                   children=[new_node])

        return new_node

    def _weaken_from_premise(self, premise, target_sequent, side_number, new_node):
        """
        Takes a formula (the premise from which to start), a sequent (the one we want to reach) and generates
        a path of SequentNodes from the initial node to sequent.
        Unlike the above, I will not weaken in a nice order here, it will just be from left to right (easier to do)
        """
        premise_side_iterator = iter(premise[side_number])

        # Prepare the loop below
        try:
            premise_elem = next(premise_side_iterator)
        except StopIteration:
            premise_elem = None
        target_position = 0

        # Loop through the target side
        for target_elem in target_sequent[side_number]:
            # If there are no more premise elements to look for or
            # target element does not coincide with the premise element to look for,
            # weaken the current content to add it
            if premise_elem is None or target_elem != premise_elem:
                new_sequent = deepcopy(new_node.content)
                new_sequent[side_number].insert(target_position, target_elem)
                new_node = SequentNode(content=new_sequent, justification=self.weakening_rule_names[side_number],
                                       children=[new_node])
            # If it does coincide, get the next element (if there is one)
            else:
                try:
                    premise_elem = next(premise_side_iterator)
                except StopIteration:
                    premise_elem = None
            target_position += 1

        return new_node


LKmin_sequent_reducer = SequentReducer(max_apparitions_per_side=3, smart_weakening=False,
                                       weakening_rule_names={0: 'WL', 1: 'WR'})
LKminEA_sequent_reducer = SequentReducer(smart_weakening=True, weakening_rule_names={0: 'WL', 1: 'WR'})
