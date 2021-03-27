class DerivationStep:
    """Step within an axiomatic derivation.

    Parameters
    ----------
    content: logics.classes.propositional.Formula
        The formula present in the step
    justification: str
        The name of the rule or axiom used in obtaining this step. May be 'premise' as well.
    on_steps: list of int
        Steps to which the derivation rule was applied to (may be empty). These are 0-based (first step of the
        derivation is step 0).

    Examples
    --------
    A derivation step will have the following form

    >>> from logics.classes.propositional.proof_theories import DerivationStep
    >>> from logics.utils.parsers import classical_parser
    >>> s = DerivationStep(content=classical_parser.parse('p or ~q'), justification='mp', on_steps=[0, 2])
    >>> s  # note the format in which it prints to the console
    ['∨', ['p'], ['~', ['q']]]; mp; [0, 2]

    Also note that you can parse an entire derivation, which will be comprised of DerivationStep

    >>> classical_parser.parse_derivation("p → (p → p); ax1")
    >>> deriv = classical_parser.parse_derivation("p → (p → p); ax1")
    >>> deriv[0]
    ['→', ['p'], ['→', ['p'], ['p']]]; ax1; []
    >>> type(deriv[0])
    <class 'logics.classes.propositional.proof_theories.derivation.DerivationStep'>

    See Also
    --------
    logics.utils.parsers.classical_parser
    """
    def __init__(self, content, justification, on_steps=None):
        self.content = content
        self.justification = justification
        if on_steps is None:
            on_steps = []
        self.on_steps = on_steps

    def unparse(self, parser):
        return f"{parser.unparse(self.content)}; {self.justification}; {self.on_steps}"

    def __eq__(self, other):
        # done with __dict__ because it will enable comparisons of instances of classes that extend this one
        return isinstance(other, DerivationStep) and (self.__dict__ == other.__dict__)

    def __ne__(self, other):
        return not self.__eq__(other)

    def __repr__(self):
        return f"{self.content}; {self.justification}; {self.on_steps}"


class Derivation(list):
    """An axiomatic or natural deduction derivation.

    Extends `list`. A derivation is a list of DerivationStep. Each step contains formula, justification, [on_steps]

    Examples
    --------
    >>> from logics.classes.propositional.proof_theories import DerivationStep, Derivation
    >>> from logics.classes.propositional import Formula
    >>> derivation = Derivation([
    ...     DerivationStep(Formula(['∧', ['p'], ['q']]), 'premise'),
    ...     DerivationStep(Formula(['p']), 'E∧', [2])
    ... ])
    >>> derivation
    0. ['∧', ['p'], ['q']]; premise; []
    1. ['p']; E∧; [2]

    would be a derivation of p from p ∧ q, using the rule E∧ ((A ^ B) / A). Note that you can also obtain a Derivation
    using the parser, e.g.

    >>> from logics.utils.parsers import classical_parser
    >>> classical_parser.parse_derivation('''
    ... p ∧ q; premise
    ... p; E∧; [0]
    ... ''')
    0. ['∧', ['p'], ['q']]; premise; []
    1. ['p']; E∧; [0]

    Slicing a Derivation also returns a Derivation

    >>> derivation[1:]
    0. ['p']; E∧; [2]
    >>> type(derivation[1:])
    <class 'logics.classes.propositional.proof_theories.derivation.Derivation'>
    """
    @property
    def premises(self):
        """Returns a list of the premises of the derivation (the DerivationStep's with a justification of 'premise')"""
        return [step.content for step in self if step.justification == 'premise']

    @property
    def conclusion(self):
        """Returns the formula in the last step of the derivation (or ``None`` if the derivation is empty)"""
        if not self:
            return None
        return self[-1].content

    def print_derivation(self, parser):
        """For even prettier printing of a derivation in the console, you can pass a parser and it will unparse the
        formula

        Examples
        --------
        >>> from logics.classes.propositional.proof_theories import DerivationStep, Derivation
        >>> from logics.utils.parsers import classical_parser
        >>> from logics.classes.propositional import Formula
        >>> derivation = Derivation([
        ...     DerivationStep(Formula(['∧', ['p'], ['q']]), 'premise'),
        ...     DerivationStep(Formula(['p']), 'E∧', [2])
        ... ])
        >>> derivation.print_derivation(classical_parser)
        0. (p ∧ q); premise; []
        1. p; E∧; [2]
        """
        for step_index in range(len(self)):
            if hasattr(self[step_index], 'open_suppositions'):
                print("|  " * len(self[step_index].open_suppositions) + f"{step_index}. "
                                                                        f"{parser.unparse(self[step_index].content)}; "
                                                                        f"{self[step_index].justification}; "
                                                                        f"{self[step_index].on_steps}")
            else:
                print(f"{step_index}. {self[step_index].unparse(parser)}")

    def __repr__(self):
        """For prettier printing of a derivation in the console"""
        string = ''
        for step_index in range(len(self)):
            if hasattr(self[step_index], 'open_suppositions'):
                string += "|  " * len(self[step_index].open_suppositions) + \
                          f"{step_index}. {self[step_index].content}; " \
                          f"{self[step_index].justification}; " \
                          f"{self[step_index].on_steps}\n"
            else:
                string += f"{step_index}. {self[step_index]}\n"
        return string

    def __getitem__(self, item):
        """If you slice a Derivation (e.g. derivation[:4]) you get a Derivation"""
        if isinstance(item, slice):
            return Derivation(super().__getitem__(item))
        return super().__getitem__(item)
