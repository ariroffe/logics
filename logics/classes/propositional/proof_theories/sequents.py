from copy import copy
from itertools import combinations, combinations_with_replacement

from anytree import NodeMixin, RenderTree, PostOrderIter

from logics.classes.exceptions import SolverError
from logics.classes.errors import ErrorCode, CorrectionError


class Sequent(list):
    """Class for representing sequents.

    Extends ``list`` instead of ``Inference`` because that allows us to have n-sided calculi. Standard 2-sided sequents
    will be len2-lists, 3-sided will be len3-lists, etc. Also, unlike Inferences, there are no nested Sequents (Sequents
    inside other Sequents). All are level 1.

    Context variables are represented as strings, not ``Formula`` (see the parameter in ``Language``).

    Also notice that, since sequents are lists of lists, order and repetition of formulae within sides matter,
    e.g. ``Γ, A ⇒ B, Δ`` is not the same as ``Γ, A ⇒ Δ, B`` nor of ``Γ, Γ, A ⇒ B, B, Δ``.

    Examples
    --------
    >>> from logics.classes.propositional import Formula
    >>> from logics.classes.propositional.proof_theories import Sequent
    >>> seq1 = Sequent([['Γ', Formula(['A'])], [Formula(['B']), 'Δ']])  # A 2-sided sequent
    >>> seq1
    [['Γ', ['A']], [['B'], 'Δ']]
    >>> seq2 = Sequent([['Γ', Formula(['A'])], [Formula(['B']), 'Δ'], [Formula(['C']), 'Σ']])  # A 3-sided sequent
    >>> seq2
    [['Γ', ['A']], [['B'], 'Δ'], [['C'], 'Σ']]

    As said above, order and repetition matter:

    >>> seq3 = Sequent([[Formula(['A']), 'Γ'], [Formula(['B']), 'Δ']])
    >>> seq3 == seq1
    False

    You can also use parsers to get sequents:

    >>> from logics.utils.parsers import classical_parser
    >>> seq4 = classical_parser.parse("Gamma, A ==> B, Delta")
    >>> seq4
    [['Γ', ['A']], [['B'], 'Δ']]
    >>> seq4 == seq1
    True
    >>> seq5 = classical_parser.parse("Gamma, A | B, Delta | C, Sigma")
    [['Γ', ['A']], [['B'], 'Δ'], [['C'], 'Σ']]
    >>> seq5 == seq2
    True

    The parser can also be used for unparsing (pretty printing) sequents:

    >>> classical_parser.unparse(seq1)
    'Γ, A ⇒ B, Δ'
    >>> classical_parser.unparse(seq2)
    'Γ, A | B, Δ | C, Σ'
    """
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        if len(self) < 2:
            raise ValueError('Sequents must have at least two sides (list members)')

    @property
    def sides(self):
        """Property that returns the number of sides.

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> seq1 = classical_parser.parse("Gamma, A ==> B, Delta")
        >>> seq1.sides
        2
        >>> seq2 = classical_parser.parse("Gamma, A | B, Delta | C, Sigma")
        >>> seq2.sides
        3
        """
        return len(self)

    # The following two methods are meant for 2-sided sequents
    @property
    def antecedent(self):
        """Returns the antecedent (first side) for 2-sided sequents, a ``ValueError`` for n>2-sided sequents.

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> seq1 = classical_parser.parse("Gamma, A ==> B, Delta")
        >>> seq1.antecedent
        ['Γ', ['A']]
        >>> seq2 = classical_parser.parse("Gamma, A | B, Delta | C, Sigma")
        >>> seq2.antecedent
        Traceback (most recent call last):
        ...
        ValueError: n>2-sided sequents do not have antecedent and succedent
        """
        if self.sides == 2:
            return self[0]
        raise ValueError('n>2-sided sequents do not have antecedent and succedent')

    @property
    def succedent(self):
        """Same as above but with the succedent. Only works for 2-sided sequents.

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> seq1 = classical_parser.parse("Gamma, A ==> B, Delta")
        >>> seq1.succedent
        [['B'], 'Δ']
        >>> seq2 = classical_parser.parse("Gamma, A | B, Delta | C, Sigma")
        >>> seq2.succedent
        Traceback (most recent call last):
        ...
        ValueError: n>2-sided sequents do not have antecedent and succedent
        """
        if self.sides == 2:
            return self[1]
        raise ValueError('n>2-sided sequents do not have antecedent and succedent')

    def main_formulae(self, language):
        """Given a language, will return all the non-context formulae in a sequent (with repetitions).

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.languages import classical_language
        >>> seq1 = classical_parser.parse("Gamma, A ==> A, B, Delta")
        >>> seq1.main_formulae(classical_language)
        [['A'], ['A'], ['B']]
        """
        main_f = list()
        for side_index in range(len(self)):
            main_f.extend(self._side_main_formulae(self[side_index], language))
        return main_f

    @staticmethod
    def _side_main_formulae(side, language):
        """Same as above, but takes a side (a list, not a Sequent)"""
        return [x for x in side if x not in language.context_variables]

    def context_formulae(self, language):
        """Same as above but with the context formulae.

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.languages import classical_language
        >>> seq1 = classical_parser.parse("Gamma, A ==> Gamma, B, Delta")
        >>> seq1.context_formulae(classical_language)
        ['Γ', 'Γ', 'Δ']
        """
        context_f = list()
        for side_index in range(len(self)):
            context_f.extend(self._side_context_formulae(self[side_index], language))
        return context_f

    @staticmethod
    def _side_context_formulae(side, language):
        """Same as above, but takes a side (a list, not a Sequent)"""
        return [x for x in side if x in language.context_variables]

    def substitute(self, language, sf_to_substitute, sf_with):
        """Substitute stuff within sequents.

        Parameters
        ----------
        language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
            Instance of Language or InfiniteLanguage
        sf_to_substitute: logics.classes.propositional.Formula or str or list of the previous
            Can substitute either a formula, a context variable or an entire slice of a sequent
        sf_with: logics.classes.propositional.Formula or str or list of the previous
            Can substitute it with either a formula, a context variable or an entire slice of a sequent

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.languages import classical_language
        >>> seq = classical_parser.parse("Γ, ~~A ==> ~A, Δ")

        Substitute a (sub)formula for another formula, or a formula for a context variable:

        >>> subst1 = seq.substitute(classical_language, classical_parser.parse("~A"), classical_parser.parse("D"))
        >>> classical_parser.unparse(subst1)
        'Γ, ~D ⇒ D, Δ'
        >>> subst2 = seq.substitute(classical_language, classical_parser.parse("~~A"), "Δ")
        >>> classical_parser.unparse(subst2)
        'Γ, Δ ⇒ ~A, Δ'

        Substitute a context variable for either a formula or another context variable:

        >>> subst3 = seq.substitute(classical_language, "Γ", classical_parser.parse("D"))
        >>> classical_parser.unparse(subst3)
        'D, ~~A ⇒ ~A, Δ'
        >>> subst4 = seq.substitute(classical_language, "Γ", "Δ")
        >>> classical_parser.unparse(subst4)
        'Δ, ~~A ⇒ ~A, Δ'

        Substitute a formula or a context variable for a slice (list):

        >>> subst5 = seq.substitute(classical_language, classical_parser.parse("~~A"), ["Δ", classical_parser.parse("D")])
        >>> classical_parser.unparse(subst5)
        'Γ, Δ, D ⇒ ~A, Δ'
        >>> subst6 = seq.substitute(classical_language, "Γ", ["Δ", classical_parser.parse("D")])
        >>> classical_parser.unparse(subst6)
        'Δ, D, ~~A ⇒ ~A, Δ'

        Substitute a slice (list) for either a formula or a context variable:

        >>> subst7 = seq.substitute(classical_language, ["Γ", classical_parser.parse("~~A")], "Δ")
        >>> classical_parser.unparse(subst7)
        'Δ ⇒ ~A, Δ'

        Substitute a slice (list) for another slice:

        >>> subst8 = seq.substitute(classical_language, ["Γ", classical_parser.parse("~~A")], ["Δ", classical_parser.parse("D")])
        >>> classical_parser.unparse(subst8)
        'Δ, D ⇒ ~A, Δ'

        Through all this, the original sequent remains unaltered:

        >>> classical_parser.unparse(seq)
        'Γ, ~~A ⇒ ~A, Δ'
        """
        substitution = []
        for side in self:
            substitution.append(self.side_substitute(side, language, sf_to_substitute, sf_with))
        return self.__class__(substitution)

    def side_substitute(self, side, language, sf_to_substitute, sf_with):
        """Same as above but takes a sequent side (a list) rather than an entire Sequent

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.languages import classical_language
        >>> seq = classical_parser.parse("Γ, ~~A ==> ~A, Δ")
        >>> seq.side_substitute(seq.antecedent, classical_language, classical_parser.parse("~A"), classical_parser.parse("D"))
        ['Γ', ['~', ['D']]]
        """
        # Substitute a list
        if type(sf_to_substitute) == list:
            return self._list_substitute(side, sf_to_substitute, sf_with)
        # Substitute an element (a (sub)formula or context variable)
        return self._element_substitute(side, language, sf_to_substitute, sf_with)

    def _element_substitute(self, side, language, sf_to_substitute, sf_with):
        new_side = []
        for elem in side:
            # Context variables
            if elem in language.context_variables:
                # If they are the element to substitute
                if elem == sf_to_substitute:
                    # If the substitution is a list, extend
                    if type(sf_with) == list:
                        new_side.extend(sf_with)
                    # If an element, append it
                    else:
                        new_side.append(sf_with)
                # Else leave them equal
                else:
                    new_side.append(elem)

            # Formula
            else:
                # If the substitution is a list
                if type(sf_with) == list:
                    # In that case, the sf_to_substitute must be an entire formula of the sequent, not a subformula
                    if elem == sf_to_substitute:
                        new_side.extend(sf_with)
                    else:
                        new_side.append(elem)
                # If an element
                else:
                    # Entire formula (for either a formula or a context variable)
                    if elem == sf_to_substitute:
                        new_side.append(sf_with)
                    # A subformula (can only be substituted with a formula, not a context variable)
                    elif type(sf_with) == type(elem):
                        new_side.append(elem.substitute(sf_to_substitute, sf_with))
                    else:
                        new_side.append(elem)  # else do nothing and put the original element
        return new_side

    def _list_substitute(self, side, sf_to_substitute, sf_with):
        new_side = []
        skip = 0
        for idx, elem in enumerate(side):
            if skip > 0:
                skip -= 1
            else:
                if side[idx:idx+len(sf_to_substitute)] == sf_to_substitute:
                    # List substitution
                    if type(sf_with) == list:
                        new_side.extend(sf_with)
                    # Element substitution
                    else:
                        new_side.append(sf_with)
                    skip = len(sf_to_substitute) - 1  # Skip the already substituted formulae in the list
                else:
                    new_side.append(side[idx])

        return new_side

    def instantiate(self, language, subst_dict):
        """Given a language and a substitution dict, returns the Sequent instantiated with the dict.

        Will return a different Sequent object, and not modify the original. For instantiating formulae,
        the susbstitution dict must have form ``{'A': someformula, 'B': someformula}``. Context variables can represent
        multiple formulae, so they must be instantiated with lists, e.g.
        ``{'Γ': ['Σ', Formula(['A'])], 'Δ': ['Δ']}``

        Parameters
        ----------
        language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
            Instance of Language or InfiniteLanguage
        subst_dict: dict
            See above for the format

        Returns
        -------
        logics.classes.propositional.proof_theories.Sequent
            A *different* sequent instance from the original

        Raises
        ------
        ValueError
            if some schematic propositional or context variable within the formula has no substitution assigned in the
            dictionary

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.languages import classical_language
        >>> sequent1 = classical_parser.parse('Γ, A, Δ, ~p ==>')
        >>> B = classical_parser.parse("B")
        >>> inst1 = sequent1.instantiate(classical_language, {'A': B, 'Γ': ['Δ', B], 'Δ': ['Δ']})
        >>> classical_parser.unparse(inst1)
        'Δ, B, B, Δ, ~p ⇒ '
        >>> classical_parser.unparse(sequent1)  # sequent1 is unmodified
        'Γ, A, Δ, ~p ⇒ '
        >>> sequent1.instantiate(classical_language, {'A': B, 'Γ': ['Δ', B]})
        Traceback (most recent call last):
        ...
        ValueError: Context variable Δ not present in substitution dict
        """
        new_sequent = []
        for side in self:
            new_side = []
            for elem in side:
                # Context variable
                if elem in language.context_variables:
                    if elem not in subst_dict:
                        raise ValueError(f'Context variable {elem} not present in substitution dict')
                    new_side.extend(subst_dict[elem])  # Substitutions of context vars are lists
                # Formula
                else:
                    new_formula = elem.instantiate(language, subst_dict)
                    new_side.append(new_formula)
            new_sequent.append(new_side)
        return Sequent(new_sequent)

    def is_instance_of(self, rule_sequent, language, possible_subst_dicts=None,
                       return_subst_dicts=False):
        """Determines if a sequent is an instance of another sequent (which is tipically within a rule).

        Works similarly to ``Formula.is_instance_of()`` but has one big difference: A sequent can be an instance of
        another sequent in many possible ways (i.e. with many possible substitution dicts). For example,
        ``Γ, A, B, Δ ⇒`` is an instance of ``Γ, A, Δ ⇒``; but unlike with formulae, it is not univocally determined
        which formula/context variable in the second corresponds to which in the first. It could be the case that
        ``{Γ: [Γ], A: A, Δ: [B, Δ]}`` or that ``{Γ: [Γ, A], A: B, Δ: Δ}``. This is also very important
        in determining if an application of a rule is correct (see the source code comment for some examples).

        Thus, the two optional parameters are a bit different:

            * `possible_subst_dicts`: defaults to ``None``. Is a list of all the possible substitution dicts. If given,
              at least one of them should be the case.
            * `return_subst_dicts`: defaults to ``False``. If True, will return the list of all possible substitution
              dicts (i.e. a list of dicts)

        Parameters
        ----------
        rule_sequent: logics.classes.propositional.proof_theories.Sequent
            The Sequent of which we want to know if it is instance
        language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
            Instance of Language or InfiniteLanguage
        possible_subst_dicts: dict, optional
            A list of susbstitution dicts of the form ``{'A': someformula, 'Γ': [...]}``
        return_subst_dicts: bool, optional
            If True will additionally return a list of possible substitution dicts

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.languages import classical_language
        >>> sequent1 = classical_parser.parse("Γ, A, Δ ⇒")
        >>> sequent2 = classical_parser.parse("Γ, A, B, Δ ⇒")
        >>> sequent2.is_instance_of(sequent1, classical_language)
        True
        >>> sequent2.is_instance_of(sequent1, classical_language, return_subst_dicts=True)
        (True, [{'A': ['A'], 'Γ': ['Γ'], 'Δ': [['B'], 'Δ']}, {'A': ['B'], 'Γ': ['Γ', ['A']], 'Δ': ['Δ']}])
        >>> sequent2.is_instance_of(sequent1, classical_language,
        ...                         possible_subst_dicts=[{'A': ['B'], 'Γ': ['Γ', ['A']], 'Δ': ['Δ']}])
        True
        >>> sequent2.is_instance_of(sequent1, classical_language,
        ...                         possible_subst_dicts=[{'A': ['B'], 'Γ': ['Γ', ['A']], 'Δ':[['B'], 'Δ']}])
        False
        """
        # This is a hard problem and I had to entirely re-write this code many times.
        # The reason is basically how uniform substitution has to work. Given a sequent and an instance,
        # there may be more than one way to assign the formulae and context variables of the rule to the instance.
        # For example, take the rule sequent:
        #
        # Γ, ~A, Δ, ~B, Σ, Π ⇒
        #
        # and the instance:
        #
        # ~A, ~B, C, ~A ⇒
        #
        # This clearly is an instance of the sequent above, but looking at it alone does not determine which of the
        # formulae is the ~A of the rule, which is the ~B, and what the context variables are. The ~A and ~B of
        # the rule (marked with () and [] respectively) may be :
        #
        # 1. (~A), [~B], C, ~A ⇒         ~A = ~A; ~B = ~B; Γ = []; Δ = []; Σ = [C, ~A]; Π = []
        # 2. (~A), [~B], C, ~A ⇒         ~A = ~A; ~B = ~B; Γ = []; Δ = []; Σ = [C]; Π = [~A]
        # 3. (~A), [~B], C, ~A ⇒         ~A = ~A; ~B = ~B; Γ = []; Δ = []; Σ = []; Π = [C, ~A]
        # 4. (~A), ~B, C, [~A] ⇒         ~A = ~A; ~B = ~A; Γ = []; Δ = [~B, C]; Σ = []; Π = []
        # 5. ~A, (~B), C, [~A] ⇒         ~A = ~B; ~B = ~A; Γ = [~A]; Δ = [C]; Σ = []; Π = []
        #
        # If all you wanted was to determine if A SINGLE SIDE is an instance, then it does not matter which of the
        # above is the case, only that there is at leasy one possibility.
        #
        # However, for the many sides of a sequent, and to see if a given subtree is a correct application of a rule,
        # we need uniform substitution among sides, and ambong the conclusion and premises. Take for example the Cut rule:
        #
        # Γ ⇒ Δ, A    A, Σ ⇒ Π
        # --------------------
        #     Γ, Σ ⇒ Δ, Π
        #
        # and the following two subtrees:
        #
        # a.  p, q ⇒ r, s    s ⇒ t        b.  p, q ⇒ r, s    r ⇒ t
        #     --------------------            --------------------
        #         p, q ⇒ r, t                     p, q ⇒ r, t
        #
        # a. is a correct application of the rule but b is not.
        # What we would tipically do in the other modules is see if the instances's conclusion is an instance of the
        # rule's conclusion, and build a kwarg dict with the substitution instances, that we then use in the premises.
        # But here that approach fails, because we do not know what the Γ, Σ, Δ, Π are by looking at the conclusion alone,
        # and moreover, every sequent in the instance is an instance of the rule's premise sequents TAKEN BY THEMSELVES.
        #
        # The only solution that I could get working is, instead of having a kwargs dict with the substitutions, have a
        # possible_subst_dicts which take into account all the possibilities, and then discard some. For instance,
        # in the cut cases above, when the algorithm looks at the second side of the conclusion, it elaborates:
        # possible_subst_dicts = [
        #     {Δ: [r], Π: [t]},
        #     {Δ: [r, t], Π: []},
        #     {Δ: [], Π: [r, t]},
        # ]
        # When it then looks at the first premise, it will delete the second and third options, and get
        # possible_subst_dicts = [
        #     {Δ: [r], Π: [t], A: s},
        # ]
        # This will then be satisfied by case a., but not by case b.
        # It is not a very efficient solution, but it works. The implementation is detailed in the next method's docstring

        if possible_subst_dicts is None:
            possible_subst_dicts = [{}]

        # Different number of sides means False
        if self.sides != rule_sequent.sides:
            if not return_subst_dicts:
                return False
            return False, possible_subst_dicts

        # We now check if each side of self is an instance of the sequent side
        for side_index in range(len(self)):
            instance, possible_subst_dicts = self._side_is_instance_of(self[side_index], rule_sequent[side_index],
                                                                       language, possible_subst_dicts)
            if not instance:
                if not return_subst_dicts:
                    return False
                return False, possible_subst_dicts

        if not return_subst_dicts:
            return True
        return True, possible_subst_dicts

    def _side_is_instance_of(self, self_side, rule_side, language, possible_subst_dicts):
        """
        Implementation works as follows:
        1- method _get_rule_pattern
        First, get the rule's sequent pattern of main formulae. For instance, for:

        [Γ, A, B, Δ, Σ, A]

        Get the pattern [A, B, A], register that the first A is not the first member (there is context at the left),
        that the last A is the last member (no context at the right) and that the first A, B must come together (there
        is no context between them). For this, _get_rule_pattern which returns [A, B, A],
        left_context = True, right_context = False, together = [(0, 1)]

        2- method _get_possible_indexes
        Next, look at the instance's non-context formulae, and loop through all possible patterns of corresponance
        to [A, B, A]. For example, if the instance (self) is:

        [Γ, A, B, C, Δ, C, A]
         0  1  2  3  4  5  6   (indexes)

        Get that the non-context formulae are in the indexes [1, 2, 3, 5, 6]
        Try the patterns:
        (1, 2, 3)
        (1, 2, 5)
        (1, 2, 6)
        (1, 3, 5)
        (1, 3, 6)
           ...
        (2, 3, 5)
        (2, 3, 6)
           ...
        For each of these, we need to determine whether:
        a. The pattern effectively instances the rule's pattern, e.g. (1,2,3) i.e. [A, B, C] does not instance [A, B, A]
        b. The left_context and right_context requisites are satisfied (only the ones ending with 6 will satisfy this)
        c. The together constraints are satisfied, in this case that the b = a + 1 in the indexes (a, b, c)
        d. Previous constraints are satisfied (if, e.g. a previous instance determined that B=B, discard all instances
           that have something other than 2 in the second index)
        In the case above, (1, 2, 6) will satisfy all four constraints.
        The return of this method is a list of 2-tuples:
        [((pattern), [list of possible dicts for that pattern]), ((pattern), [list of possible dicts for that pattern])]

        3- method _get_context_dicts
        For each of the elements above, determine what the formulae and context variables instantiate, e.g for:
        rule sequent [Γ, A, B, Δ, Σ, A], instance [Γ, A, B, C, Δ, C, A] and indexes (1, 2, 6), we already have
        determined that the the A of the rule = A, the B of the rule = B, but the context variable corresponances can be
        determined in various ways.
        The Γ of the rule = [Γ], but the Δ and Σ, of the rule = [C, Δ, C].
        So, we need to include several possibilities in the possible_subst_dicts:
        - A: A, B: B, Γ: [Γ], Δ: [C, Δ, C], Σ: []
        - A: A, B: B, Γ: [Γ], Δ: [C, Δ], Σ: [C]
        - A: A, B: B, Γ: [Γ], Δ: [C], Σ: [Δ, C]
        - A: A, B: B, Γ: [Γ], Δ: [], Σ: [C, Δ, C]
        Of course, in building the dicts of the context formulae, we need to look again into the
        possible_subst_dict for previous possible assignments that might allow us to discard one (or all) the
        possibilities
        """
        # Empty rule side
        if rule_side == list():
            return self_side == list(), possible_subst_dicts

        pattern, left_context, right_context, together = self._get_rule_pattern(rule_side, language.context_variables)
        possible_indexes = self._get_possible_indexes(self_side, language, pattern,
                                                      left_context, right_context, together,
                                                      possible_subst_dicts=possible_subst_dicts)
        if not possible_indexes:
            return False, possible_subst_dicts

        possible_subst_dicts = self._get_context_dicts(self_side, rule_side, possible_indexes,
                                                       language.context_variables)
        if not possible_subst_dicts:
            return False, possible_subst_dicts

        return True, possible_subst_dicts

    @staticmethod
    def _get_rule_pattern(sequent_side, context_variables):
        """Sub-algorithm 1- of the algorithm described above (in _side_is_instance_of)"""
        pattern = list()
        left_context = False
        right_context = False
        together = list()
        # This is for the together, see below
        prev_context = False

        for member_index in range(len(sequent_side)):
            # Context variable
            if sequent_side[member_index] in context_variables:
                prev_context = True
                if member_index == 0:
                    left_context = True
                if member_index == len(sequent_side) - 1:
                    right_context = True

            # Non-context variable (formula)
            else:
                pattern.append(sequent_side[member_index])
                if not prev_context and len(pattern) > 1:
                    together.append((len(pattern) - 2, len(pattern) - 1))  # last index, prev to last index of pattern
                prev_context = False

        return pattern, left_context, right_context, together

    def _get_possible_indexes(self, self_side, language, rule_pattern,
                              left_context, right_context, together, possible_subst_dicts):
        """Sub-algorithm 2- of the algorithm described above (in _side_is_instance_of)
        Possible substitution dicts has to be a list of dicts, since previous instances may determine context vars in
        different ways. To test with an empty dict use [{}]
        """
        result_to_return = list()

        # First, get the indexes of the formulae in self_side (the instance sequent)
        self_indexes = [self_index for self_index in range(len(self_side))
                        if self_side[self_index] not in language.context_variables]

        self_index_iterator = self._get_index_iterator(self_indexes, len(rule_pattern))
        for possible_self_pattern in self_index_iterator:
            # Each possible_self_pattern is basically a tuple of integers e.g. (1, 2, 5)
            # Representing indexes of places where there are formulae in self_side
            exit_pattern = False

            # Begin by checking the left_context and right_context requisite (easyest)
            if not left_context and possible_self_pattern[0] != 0:
                exit_pattern = True
            if not right_context and possible_self_pattern[-1] != len(self_side) - 1:
                exit_pattern = True

            # Check that the together constraints are satisfied
            if not exit_pattern:
                for together_tuple in together:
                    if possible_self_pattern[together_tuple[1]] != possible_self_pattern[together_tuple[0]] + 1:
                        exit_pattern = True
                        break

            # Check if the corresponding formulae are instances with each of the possible subst dicts, and if previous
            # constraints for formulae are satisfied
            if not exit_pattern:
                some_dict_successful = False
                pattern_possible_subst_dicts = list()
                for possible_subst_dict in possible_subst_dicts:
                    all_instance = True
                    new_dict = copy(possible_subst_dict)
                    for position in range(len(possible_self_pattern)):
                        rule_formula = rule_pattern[position]
                        self_formula = self_side[possible_self_pattern[position]]
                        instance, new_dict = self_formula.is_instance_of(rule_formula, language, subst_dict=new_dict,
                                                                         return_subst_dict=True)

                        if not instance:
                            all_instance = False
                            break

                    # If all are instance, save the tuple and the new_dict
                    if all_instance:
                        some_dict_successful = True
                        pattern_possible_subst_dicts.append(new_dict)

                if some_dict_successful:
                    result_to_return.append((possible_self_pattern, pattern_possible_subst_dicts))

        return result_to_return

    @staticmethod
    def _get_index_iterator(indexes, length):
        """
        Gets a list of indexes, and returns an iterator that yields length-tuples of them, that are ordered.
        For instance, for indexes = [1, 2, 3, 5, 6], and length 3, the iterator will yield the cases from the large
        docstring above (i.e. (1, 2, 3), (1, 2, 5), (1, 2, 6), (2, 3, 5), ...)
        """
        return combinations(indexes, length)

    def _get_context_dicts(self, self_side, rule_side, possible_self_patterns, context_variables):
        """Sub-algorithm 3- of the algorithm described above (in _side_is_instance_of)"""
        # For each pattern + dicts
        new_subst_dicts = list()
        for possible_pattern in possible_self_patterns:
            # possible_self_patterns is the return of the previous method. It contains something like:
            # ((1, 2, 5), [{'A': B, 'B': C}])
            pattern_indexes = possible_pattern[0]
            pattern_possible_subst_dicts = possible_pattern[1]

            # Walk through the rule until we find a formula (or the last element of the rule)
            prev_rule_context = []
            rule_elem_counter = -1
            rule_formula_number = -1
            instance_corresponding_index = None  # Will remain None only if rule_side has no formulae
            exit_pattern = False
            for rule_elem in rule_side:
                rule_elem_counter += 1
                last_element = rule_elem_counter == len(rule_side) - 1  # True if it is the last element, False otherw

                # Context variable
                if rule_elem in context_variables:
                    prev_rule_context.append(rule_elem)
                # Formula
                else:
                    rule_formula_number += 1

                # There is context to assign and we reach a formula or the end of the rule
                if prev_rule_context and (rule_elem not in context_variables or last_element):
                    # We now need to determine the part of the instance that corresponds to prev_rule_context
                    # For example, in rule = [Γ, Δ, A, B, Σ], instance=[Γ, A, B, Δ, Σ], pattern=[(1, 2), ...]
                    # we will stop at A and have prev_rule_context=[Γ, Δ]. Given that, according to pattern, the A
                    # of the rule is the A of the instance, we need to get that, in the instance, [Γ] corresponds
                    # to prev_rule_context (i.e. [Γ, Δ]).
                    # Same in the end, we need to establish that Σ in the rule corresponds to [Δ, Σ] in the instance

                    # Formula
                    if rule_elem not in context_variables:
                        instance_corresponding_index = pattern_indexes[rule_formula_number]
                        # Will not be updated if last element and not formula

                    # First formula
                    if rule_elem not in context_variables and rule_formula_number == 0:
                        instance_context = self_side[0:instance_corresponding_index]
                    # Last element and not formula
                    elif rule_elem in context_variables and last_element:
                        # Last element and there is no previous formula instance (i.e. the rule has no formulae)
                        if instance_corresponding_index is None:
                            instance_context = self_side
                        else:
                            instance_context = self_side[instance_corresponding_index+1:]
                    # Formula that came after a previous formula
                    else:
                        prev_instance_index = pattern_indexes[rule_formula_number-1]
                        instance_context = self_side[prev_instance_index+1:instance_corresponding_index]

                    # We now have, for example, that the rule's [Γ, Δ] corresponds to the instance's [Σ, A]
                    # We need to determine every possible way of assigning the right elements to the left vars
                    # i.e. {Γ:[Σ, A], Δ:[]}, {Γ:[Σ], Δ:[A]} and {Γ:[], Δ:[Σ, A]} and see if they violate the prev
                    # established constraints in possible_dict
                    new_pattern_possible_subst_dicts = list()
                    for possible_subst_dict in pattern_possible_subst_dicts:
                        # Each possible correspondance dict has something like
                        # {Γ:[Σ, A], Δ:[]} or {Γ:[Σ], Δ:[A]} or {Γ:[], Δ:[Σ, A]}
                        # We need to se if each possible assignment is compatible with each of the prev subst dicts
                        possible_correspondances_iterator = self._get_context_distribs_iterator(prev_rule_context,
                                                                                                instance_context)
                        for possible_correspondance_dict in possible_correspondances_iterator:
                            new_subst_dict = copy(possible_subst_dict)
                            compatible = True
                            for context_var in possible_correspondance_dict:
                                # No previous restriction
                                if context_var not in possible_subst_dict:
                                    new_subst_dict[context_var] = possible_correspondance_dict[context_var]
                                # There is a previous incompatible restriction
                                elif possible_subst_dict[context_var] != possible_correspondance_dict[context_var]:
                                    compatible = False
                                    break

                            if compatible:
                                new_pattern_possible_subst_dicts.append(new_subst_dict)

                    # Since we may continue looking at this pattern, (e.g in rule [Gamma, A, Delta, B])
                    # we reach here two times, in A and B), replace the old possibilities with the new ones
                    if new_pattern_possible_subst_dicts:
                        pattern_possible_subst_dicts = copy(new_pattern_possible_subst_dicts)
                    # If no possibility, exit the pattern
                    else:
                        exit_pattern = True
                        break  # This breaks out of the for rule_elem loop

                    # Once you found a formula and did all the above, empty the previous context for the next formula
                    prev_rule_context = []

            # Here we have finished looking at all the rule's elements.
            # See if we have any pattern_possible_subst_dicts and append them to new_subst_dicts (to return)
            if pattern_possible_subst_dicts and not exit_pattern:
                new_subst_dicts.extend(pattern_possible_subst_dicts)

        # Here we have finished looking at all the patterns
        return new_subst_dicts

    @staticmethod
    def _get_context_distribs_iterator(rule_context_list, instance_list):
        """
        Does what the comment above says, e.g. if the rule's [Γ, Δ] corresponds to the instance's [Σ, A], returns an
        iterator that will yield {Γ:[Σ, A], Δ:[]}, {Γ:[Σ], Δ:[A]} and {Γ:[], Δ:[Σ, A]}
        """
        combs = combinations_with_replacement(rule_context_list, len(instance_list))
        # Combs will yield ('Γ', 'Γ'), ('Γ', 'Δ'), ('Δ', 'Δ') (to which of the rules vars the instances elems belong)

        def iterator(combs):
            for comb in combs:
                yield_dict = {cv: [] for cv in rule_context_list}
                for comb_index in range(len(comb)):
                    yield_dict[comb[comb_index]].append(instance_list[comb_index])
                yield yield_dict

        return iterator(combs)


# ----------------------------------------------------------------------------------------------------------------------
# ----------------------------------------------------------------------------------------------------------------------
# Derivations (Trees)

class SequentNode(NodeMixin):
    """Class for nodes in sequent tree-derivations.

    Subclasses NodeMixin from the `anytree package <https://anytree.readthedocs.io/en/latest/>`_.
    Since a node can have children, it can also be taken to represent a tree (an entire derivation), see below for some
    examples.

    Unlike tableaux nodes, these must be read backwards: The parent sequent is the derived sequent and the children
    are its premises.

    Parameters
    ----------
    content: logics.classes.propositional.proof_theories.Sequent
        The sequent of the node
    justification: str, optional
        If the node is non-root, this parameter should contain the name of the rule by which it was obtained
    parent: logics.classes.propositional.proof_theories.SequentNode, optional
        The parent node. The root node of a tableaux has None as parent (the default value).
    children: list of logics.classes.propositional.proof_theories.SequentNode, optional
        A list of the children node. Also optional. If child nodes are specified with the `parent` attribute, there
        is no need to provide this (see the example below).

    Examples
    --------
    >>> from logics.utils.parsers import classical_parser
    >>> from logics.classes.propositional.proof_theories import SequentNode
    >>> n3 = SequentNode(content=classical_parser.parse('A, Gamma ==> Delta'))
    >>> n2 = SequentNode(content=classical_parser.parse('Gamma ==> Delta, ~A'), justification='~R', children=[n3])
    >>> n1 = SequentNode(content=classical_parser.parse('Gamma ==> ~A, Delta'), justification='ER', children=[n2])

    As in tableaux, we can pretty print like this:

    >>> n1.print_tree(classical_parser)
    Γ ⇒ ~A, Δ (ER)
    └── Γ ⇒ Δ, ~A (~R)
        └── A, Γ ⇒ Δ

    Also as in tableaux nodes, the anytree package gives us some base functionality:

    >>> n1.is_root
    True
    >>> n3.is_leaf
    True
    >>> n1.children  # returns (n2,)
    ([['Γ'], ['Δ', ['~', ['A']]]] (~R),)
    >>> n1.descendants  # returns (n2, n3)
    ([['Γ'], ['Δ', ['~', ['A']]]] (~R), [[['A'], 'Γ'], ['Δ']])
    >>> n3.root  # returns n1
    [['Γ'], [['~', ['A']], 'Δ']] (ER)
    >>> n1.leaves  # returns (n3,)
    ([[['A'], 'Γ'], ['Δ']],)
    >>> n3.path  # returns (n1, n2, n3)
    ([['Γ'], [['~', ['A']], 'Δ']] (ER), [['Γ'], ['Δ', ['~', ['A']]]] (~R), [[['A'], 'Γ'], ['Δ']])
    >>> n3.depth
    2
    >>> n1.height
    2
    """
    def __init__(self, content, justification=None, parent=None, children=None):
        self.content = content
        self.justification = justification
        self.parent = parent
        if children:
            self.children = children

    def is_instance_of(self, node, language, possible_subst_dicts=None, return_subst_dicts=False):
        """Determines if a SequentNode is an instance of another SequentNode

        A node is considered an instance of another iff:

        * The content of `self` is an instance of the content of node
        * The justification is equal to the justification of node (or is ``None`` in node)

        `return_subst_dicts` and `possible_subst_dicts` are as in ``Sequent.is_instance_of`` (and are used for uniform
        substitution).

        Parameters
        ----------
        node: logics.classes.propositional.proof_theories.SequentNode
            The SequentNode of which we want to know if it is instance
        language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
            Instance of Language or InfiniteLanguage
        possible_subst_dicts: dict, optional
            A list of susbstitution dicts of the form ``{'A': someformula, 'Γ': [...]}``
        return_subst_dicts: bool, optional
            If True will additionally return a list of possible substitution dicts.

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.languages import classical_language
        >>> from logics.classes.propositional.proof_theories import SequentNode
        >>> n1 = SequentNode(content=classical_parser.parse('Gamma, ~A, Delta ==>'))
        >>> n2 = SequentNode(content=classical_parser.parse('Gamma, ~p, ~~p ==>'))
        >>> n2.is_instance_of(n1, classical_language)
        True
        >>> n2.is_instance_of(n1, classical_language, return_subst_dicts=True)
        (True, [{'A': ['p'], 'Γ': ['Γ'], 'Δ': [['~', ['~', ['p']]]]}, {'A': ['~', ['p']], 'Γ': ['Γ', ['~', ['p']]], 'Δ': []}])
        >>> n3 = SequentNode(content=classical_parser.parse('Gamma, ~p, ~~p ==>'), justification='~L')
        >>> n3.is_instance_of(n1, classical_language)  # justification is None in n1
        True
        >>> n4 = SequentNode(content=classical_parser.parse('Gamma, ~A, Delta ==>'), justification='~L')
        >>> n2.is_instance_of(n4, classical_language)  # Justification is None in n2 but not in n4
        False
        """
        if possible_subst_dicts is None:
            possible_subst_dicts = [{}]

        # First check the justification (it is less costly)
        if node.justification is not None and self.justification != node.justification:
            if not return_subst_dicts:
                return False
            return False, possible_subst_dicts

        # Check if the sequent is instance
        instance, possible_subst_dicts = self.content.is_instance_of(node.content, language,
                                                                     possible_subst_dicts=possible_subst_dicts,
                                                                     return_subst_dicts= True)
        if not return_subst_dicts:
            return instance
        return instance, possible_subst_dicts

    # ------------------------------------------------------------------------------------------------------------------
    # Methods to print the node / tree to the console

    def _self_string(self, parser=None):
        """
        Returns the content + the justification (if there is any) of the present node
        If a parser is given as argument, returns the content unparsed (see below for an example)
        """
        if not parser:
            s = f'{self.content}'
        else:
            s = f'{parser.unparse(self.content)}'
        if self.justification is not None:
            s += f' ({self.justification})'
        return s

    def __repr__(self):
        return self._self_string()

    def print_tree(self, parser=None):
        """Will print a node and its *descendants* in a pretty, tree-like, format

        If a parser is given as argument, returns the content unparsed. See above for an example.
        """
        for pre, _, node in RenderTree(self):
            print(pre + node._self_string(parser))

    def __eq__(self, other):
        """Nodes are compared without regards to their parents or children"""
        return isinstance(other, self.__class__) and \
            self.content == other.content and self.justification == other.justification

    def __ne__(self, other):
        return not self.__eq__(other)


# ----------------------------------------------------------------------------------------------------------------------
# ----------------------------------------------------------------------------------------------------------------------
# Systems

class SequentCalculus:
    """Class for sequent calculi systems

    Parameters
    ----------
    language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
        Instance of Language or InfiniteLanguage
    axioms: dict (str: logics.classes.propositional.proof_theories.Sequent)
        The keys are strings (the name of the rule) and the values are Sequent
    rules: dict (str: logics.classes.propositional.proof_theories.SequentNode)
        The keys are strings (the name of the rule) and the values are SequentNode (w/children)
    solver
        Any object with a ``reduce`` method (which takes a sequent and a sequent calculus). ``None`` by default.
    solver_rule_order: list of str
        The order of rules (given as rule names) in which the solver should try to reduce a sequent. If
        `smart_weakening` is activated in the solver (see the solver class) the weakening rules can be obviated here.

    Attributes
    ----------
    fast_axiom_check: bool
        Class attribute. If true, will assume that the only axiom present is identity without context
        (i.e. ``A ⇒ A``, or ``A | ... | A``). It is less general but the reducer works faster with this enabled.
        ``True`` by default.

    Examples
    --------
    >>> from logics.utils.parsers import classical_parser
    >>> from logics.instances.propositional.languages import classical_language
    >>> from logics.classes.propositional.proof_theories import Sequent, SequentNode, SequentCalculus

    Defining some axioms and rules:

    >>> identity = classical_parser.parse('A ==> A')
    >>> weakening_left_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta'))
    >>> weakening_left = SequentNode(content=classical_parser.parse('A, Gamma ==> Delta'),
    ...                              children=[weakening_left_premise])
    >>> weakening_left.print_tree(classical_parser)  # For illustration purposes
    A, Γ ⇒ Δ
    └── Γ ⇒ Δ
    >>> weakening_right_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta'))
    >>> weakening_right = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A'),
    ...                               children=[weakening_right_premise])
    >>> weakening_right.print_tree(classical_parser)  # For illustration purposes
    Γ ⇒ Δ, A
    └── Γ ⇒ Δ
    >>> negation_left_premise = SequentNode(content=classical_parser.parse('Gamma ==> Delta, A'))
    >>> negation_left = SequentNode(content=classical_parser.parse('~A, Gamma ==> Delta'),
    ...                             children=[negation_left_premise])
    >>> negation_left.print_tree(classical_parser)  # For illustration purposes
    ~A, Γ ⇒ Δ
    └── Γ ⇒ Δ, A
    >>> negation_right_premise = SequentNode(content=classical_parser.parse('A, Gamma ==> Delta'))
    >>> negation_right = SequentNode(content=classical_parser.parse('Gamma ==> Delta, ~A'),
    ...                              children=[negation_right_premise])
    >>> negation_right.print_tree(classical_parser)  # For illustration purposes
    Γ ⇒ Δ, ~A
    └── A, Γ ⇒ Δ

    Defining an example (toy) system with only weakening and negation rules:

    >>> toy_system = SequentCalculus(language=classical_language, axioms={'identity': identity},
    ...                              rules={'WL': weakening_left, 'WR': weakening_right,
    ...                                     '~L': negation_left, '~R': negation_right})
    """
    fast_axiom_check = True

    def __init__(self, language, axioms, rules, solver=None, solver_rule_order=None):
        self.language = language
        self.axioms = axioms
        self.rules = rules
        self.solver = solver
        self.solver_rule_order = solver_rule_order

    def sequent_is_axiom(self, sequent, axiom_name=None):
        """Determines if a sequent is an instance of an axiom of the system.

        Parameters
        ----------
        sequent: logics.classes.propositional.proof_theories.Sequent
            The sequent you wish to check
        axiom_name: str, optional
            If left as ``None`` will check every axiom of the system. If given a string (an axiom name) will only check
            that particular axiom. Giving a string will do nothing is ``fast_axiom_check`` is enabled.

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.sequents import LK
        >>> seq = classical_parser.parse("p ==> p")
        >>> LK.sequent_is_axiom(seq)
        True
        >>> seq2 = classical_parser.parse("p, Gamma ==> Delta, p")
        >>> LK.sequent_is_axiom(seq2)
        False
        """
        if self.fast_axiom_check:
            return self._fast_sequent_is_axiom(sequent)
        return self._slow_sequent_is_axiom(sequent, axiom_name)

    def _fast_sequent_is_axiom(self, sequent):
        # Fast version (does not call is_instance_of, assumes the axiom is identity)
        first_side = sequent[0]
        if len(first_side) != 1 or first_side[0] in self.language.context_variables:
            return False
        formula = first_side[0]
        for side in sequent[1:]:
            if side != [formula]:
                return False
        return True

    def _slow_sequent_is_axiom(self, sequent, axiom_name):
        if axiom_name is None:
            for axiom in self.axioms.values():
                if sequent.is_instance_of(axiom, self.language):
                    return True
        else:
            if sequent.is_instance_of(self.axioms[axiom_name], self.language):
                return True
        return False

    def tree_is_closed(self, node):
        """Given a tree (a *derived* sequent with children -premises-) checks if all descendant branches are closed
        (i.e. if every leaf is an axiom)

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.classes.propositional.proof_theories import SequentNode
        >>> from logics.instances.propositional.sequents import LK
        >>> n1 = SequentNode(content=classical_parser.parse('A ==> A'), justification='identity')
        >>> n2 = SequentNode(content=classical_parser.parse('A ==> A, Delta'), justification='WR', children=[n1])
        >>> n3 = SequentNode(content=classical_parser.parse('Gamma, A ==> A, Delta'), justification='WL', children=[n2])
        >>> n3.print_tree(classical_parser)  # for illustration purposes
        Γ, A ⇒ A, Δ (WL)
        └── A ⇒ A, Δ (WR)
            └── A ⇒ A (identity)
        >>> LK.tree_is_closed(n3)
        True
        >>> n2.children = []
        >>> LK.tree_is_closed(n2)
        False
        """
        for node2 in node.leaves:
            if not self.sequent_is_axiom(node2.content):
                return False
        return True

    def is_correctly_applied(self, node, rule_name, return_subst_dicts=False, return_error=False):
        """Checks if a node and its immediate descentants are an instance of a given rule

        Parameters
        ----------
        node: logics.classes.propositional.proof_theories.SequentNode
            A sequent node (derived) w/children (premises)
        rule_name: str
            The name of the rule you want to check
        return_subst_dicts: bool, optional
            If set to ``True`` will return a list of the possible substitution dicts
        return_error: bool, optional
            If ``True`` will return a string detailing the error it found (just one, not a list of errors)

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.classes.propositional.proof_theories import SequentNode
        >>> from logics.instances.propositional.sequents import LK
        >>> n1 = SequentNode(content=classical_parser.parse('A ==> A'), justification='identity')
        >>> n2 = SequentNode(content=classical_parser.parse('A ==> A, Delta'), justification='WR', children=[n1])
        >>> n2.print_tree(classical_parser)  # for illustration purposes
        A ⇒ A, Δ (WR)
        └── A ⇒ A (identity)
        >>> LK.is_correctly_applied(n2, "WR")
        True
        >>> LK.is_correctly_applied(n2, "WR", return_subst_dicts=True)  # (weakening is defined with context vars)
        (True, [{'Γ': [['A']], 'Δ': [['A']], 'Π': ['Δ']}])
        >>> n2.justification = "WL"
        >>> LK.is_correctly_applied(n2, "WL")
        False
        >>> LK.is_correctly_applied(n2, "WL", return_error=True)
        (False, "... premise [[['A']], [['A']]] (identity) is not an instance of rule premise [['Γ'], ['Δ']]")
        """
        possible_subst_dicts = dict()

        if node.justification != rule_name:
            if not return_subst_dicts and not return_error:
                return False
            return_value = [False]
            if return_subst_dicts:
                return_value.append(possible_subst_dicts)
            if return_error:
                return_value.append(f'Node justification for node {node} is not {rule_name}')
            return tuple(return_value)

        rule = self.rules[rule_name]

        # Check that the rule has the same number of children (premises) than node
        node_premises = node.children
        rule_premises = rule.children
        if len(node_premises) != len(rule_premises):
            if not return_subst_dicts and not return_error:
                return False
            return_value = [False]
            if return_subst_dicts:
                return_value.append(possible_subst_dicts)
            if return_error:
                return_value.append(f'Incorrect number of premises for node {node}')
            return tuple(return_value)

        # Check if the node is instance of the rule's conclusion (with no previous substitution dict)
        instance, possible_subst_dicts = node.is_instance_of(rule, self.language, return_subst_dicts=True)
        if not instance:
            if not return_subst_dicts and not return_error:
                return False
            return_value = [False]
            if return_subst_dicts:
                return_value.append(possible_subst_dicts)
            if return_error:
                return_value.append(f"Node {node} is incorrectly derived, "
                                    f"it is not an instance of {node.justification}'s conclusion")
            return tuple(return_value)

        # Then check that the immediate children (the premises) are instance
        for premise_index in range(len(node_premises)):
            instance, possible_subst_dicts = \
                node_premises[premise_index].is_instance_of(rule_premises[premise_index], self.language,
                                                            possible_subst_dicts=possible_subst_dicts,
                                                            return_subst_dicts=True)
            if not instance:
                if not return_subst_dicts and not return_error:
                    return False
                return_value = [False]
                if return_subst_dicts:
                    return_value.append(possible_subst_dicts)
                if return_error:
                    return_value.append(f"Node {node} is incorrectly derived, premise "
                                        f"{node_premises[premise_index]} is not an instance of "
                                        f"rule premise {rule_premises[premise_index]}")
                return tuple(return_value)

        if not return_subst_dicts and not return_error:
            return True
        return_value = [True]
        if return_subst_dicts:
            return_value.append(possible_subst_dicts)
        if return_error:
            return_value.append(None)
        return tuple(return_value)

    def is_correct_tree(self, tree, premises=None, return_error_list=False, exit_on_first_error=False):
        """Checks if a tree derivation is correct.

        That is, checks that every leaf is an axiom or a premise, and that every other node is obtained via a correct
        application of a rule to its children nodes. Remember that the root of the tree is the derived node.

        Parameters
        ----------
        tree: logics.classes.propositional.proof_theories.SequentNode
            A sequent tree (derivation)
        premises: list of logics.classes.propositional.proof_theories.Sequent, optional
            An optional list of sequents to use as premises, additionally to the axioms
        return_error_list: bool, optional
            If False, will just return True or False (exits when it finds an error, more efficient) If True, will return
            (True, a list of ``logics.classes.errors.CorrectionError``)
        exit_on_first_error: bool, optional
            If `return_error_list` and this are both true, it will return a list with a single error instead of many.
            More efficient, since it makes early exits.

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.classes.propositional.proof_theories import SequentNode
        >>> from logics.instances.propositional.sequents import LK

        A correct derivation:

        >>> n1 = SequentNode(content=classical_parser.parse('A ==> A'), justification='identity')
        >>> n2 = SequentNode(content=classical_parser.parse('A ==> A, Delta'), justification='WR', children=[n1])
        >>> n3 = SequentNode(content=classical_parser.parse('Gamma, A ==> A, Delta'), justification='WL', children=[n2])
        >>> n3.print_tree(classical_parser)  # for illustration purposes
        Γ, A ⇒ A, Δ (WL)
        └── A ⇒ A, Δ (WR)
            └── A ⇒ A (identity)
        >>> LK.is_correct_tree(n3)
        True

        An incorrect derivation (correct with premises):

        >>> n4 = SequentNode(content=classical_parser.parse('p ==> q'))
        >>> n5 = SequentNode(content=classical_parser.parse('p ==> q, Delta'), justification='WR', children=[n4])
        >>> n6 = SequentNode(content=classical_parser.parse('Gamma, p ==> q, Delta'), justification='WL', children=[n5])
        >>> n6.print_tree(classical_parser)  # for illustration purposes
        Γ, p ⇒ q, Δ (WL)
        └── p ⇒ q, Δ (WR)
            └── p ⇒ q
        >>> LK.is_correct_tree(n6)
        False
        >>> LK.is_correct_tree(n6, return_error_list=True)
        (False, [Node [[['p']], [['q']]]: Axiom None is not a valid axiom name, Node [[['p']], [['q']]] is not a valid axiom])
        >>> LK.is_correct_tree(n6, premises=[classical_parser.parse('p ==> q')])
        True
        """
        # todo CHANGE THE INDEXES IN THE CorrectionErrors

        error_list = list()

        if premises is None:
            premises = list()

        for node in PostOrderIter(tree):
            # Leaves
            if node.is_leaf:
                # Check if it is a premise
                premise = False
                for premise in premises:
                    if node.content == premise:
                        if node.justification is not None and node.justification != 'premise':
                            if not return_error_list:
                                return False
                            error_list.append(CorrectionError(code=ErrorCode.SEQ_INCORRECT_PREMISE, index=None,
                                                              category="SEQ",
                                                              description=f"Node {node}: Premise nodes must have either"
                                                                          f" None or 'premise' as justification"))
                            if exit_on_first_error:
                                return False, error_list
                        premise = True

                # If not, it must be an axiom
                if not premise:
                    axiom_name = node.justification
                    if self.fast_axiom_check and axiom_name != 'identity':
                        if not return_error_list:
                            return False
                        error_list.append(CorrectionError(code=ErrorCode.SEQ_INCORRECT_AXIOM, index=None,
                                                          category="SEQ",
                                                          description=f'Node {node}: Axiom {axiom_name} is not a valid '
                                                                      f'axiom name'))
                        if exit_on_first_error:
                            return False, error_list
                    if not self.sequent_is_axiom(node.content, axiom_name):
                        if not return_error_list:
                            return False
                        error_list.append(CorrectionError(code=ErrorCode.SEQ_INCORRECT_AXIOM, index=None,
                                                          category="SEQ",
                                                          description=f'Node {node} is not a valid axiom'))
                        if exit_on_first_error:
                            return False, error_list

            # Internal nodes
            else:
                # Check if correct rule application
                correct, error = self.is_correctly_applied(node, rule_name=node.justification, return_error=True)
                if not correct:
                    if not return_error_list:
                        return False
                    error_list.append(CorrectionError(code=ErrorCode.SEQ_RULE_INCORRECTLY_APPLIED, index=None,
                                                      category="SEQ", description=error))
                    if exit_on_first_error:
                        return False, error_list

        if error_list:
            return False, error_list
        if not return_error_list:
            return True
        return True, error_list

    @staticmethod
    def transform_inference_into_sequent(inference, sides=2, separate_premises_from_conclusions_at_index=1):
        """Transforms an Inference into an n-sided sequent, in order to check for validity using sequent calculi.

        Parameters
        ----------
        inference: logics.classes.propositional.Inference
            The inference you want to transform
        sides: int, optional
            Number of sides you want the resulting sequent to have. Defaults to 2
        separate_premises_from_conclusions_at_index: int, optional
            For n-sided calculi, where you want to separate the premises and conclusions. Defaults to 1

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.sequents import LK
        >>> inf = classical_parser.parse("p ∨ q, ~p / q")
        >>> seq = LK.transform_inference_into_sequent(inf)
        >>> classical_parser.unparse(seq)
        '(p ∨ q), ~p ⇒ q'
        >>> seq = LK.transform_inference_into_sequent(inf, sides=3)
        >>> classical_parser.unparse(seq)
        '(p ∨ q), ~p | q | q'
        >>> seq = LK.transform_inference_into_sequent(inf, sides=3, separate_premises_from_conclusions_at_index=2)
        >>> classical_parser.unparse(seq)
        '(p ∨ q), ~p | (p ∨ q), ~p | q'
        """
        sequent = list()
        for side_index in range(sides):
            if side_index < separate_premises_from_conclusions_at_index:
                sequent.append(inference.premises)
            else:
                sequent.append(inference.conclusions)
        sequent = Sequent(sequent)
        return sequent

    def reduce(self, sequent, premises=None):
        """Shortcut for ``solver.reduce(sequent, self, premises)``, see the solver documentation"""
        return self.solver.reduce(sequent, self, premises)

    def is_valid(self, inference, sides=2, separate_premises_from_conclusions_at_index=1):
        """Determines if an Inference is valid.

        Will only work if a solver was given to the *init* method when initializing the class.
        Default arguments assume a 2-sided calculus

        Parameters
        ----------
        inference: logics.classes.propositional.Inference
            The inference you want to transform
        sides: int, optional
            Number of sides you want the resulting sequent to have. Defaults to 2
        separate_premises_from_conclusions_at_index: int, optional
            For n-sided calculi, where you want to separate the premises and conclusions. Defaults to 1

        Examples
        --------
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.instances.propositional.sequents import LKminEA  # see below in Instances for a description
        >>> inf = classical_parser.parse("p ∨ q, ~p / q")
        >>> LKminEA.is_valid(inf)
        True
        >>> inf2 = classical_parser.parse("p ∨ q / p")
        >>> LKminEA.is_valid(inf2)
        False
        """
        if self.solver is None:
            raise NotImplemented('The present sequent calculus has no solver assigned')
        sequent = self.transform_inference_into_sequent(inference, sides, separate_premises_from_conclusions_at_index)
        try:
            self.solver.reduce(sequent, self)
            return True
        except SolverError:
            return False
