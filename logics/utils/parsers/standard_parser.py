from copy import copy

from logics.classes.propositional import Formula, Inference
from logics.classes.propositional.proof_theories import Derivation, DerivationStep, NaturalDeductionStep, \
    Sequent
from logics.classes.exceptions import NotWellFormed
from logics.utils.parsers import parser_utils


class StandardParser:
    """Parser for propositional languages.

    Parsers serve for transforming strings into Formula, Inference, Sequent, etc. and vice-versa, thus handling objects
    of those types more easily and less cumbersombly. See below for some examples.

    Parameters
    ----------
    language: logics.classes.propositional.Language or logics.classes.propositional.InfiniteLanguage
        Instance of Language or InfiniteLanguage
    parse_replacement_dict: dict, optional
        Dictionary of the form ({string: string, ...}). See below for an explanation
    unparse_replacement_dict: dict, optional
        Same as the above parameter
    infix_cts: list of str, optional
        The list of constants that will be written in infix notation
    comma_separator: str, optional
        Character (preferrably of len 1) used to separate the premises or separate the conclusions within an inference
    inference_separator: str, optional
        Character (preferrably of len 1) used to separate between the premises and conclusions in an inference
    derivation_step_separator: str, optional
        Character (preferrably of len 1) used to separate the components of a derivation step
    two_sided_sequent_separator: str, optional
        Character (preferrably of len 1) used to separate the two sides of a two-sided sequent
    n_sided_sequent_separator: str, optional
        Character (preferrably of len 1) used to separate the sides of an n-sided sequent

    Examples
    --------
    Let us first define a language (say, one containing only conjunction and negation as constants)

    >>> from logics.classes.propositional import Language
    >>> language = Language(atomics=['p', 'q', 'r'],
    ...                     constant_arity_dict={'~': 1, '∧': 2},
    ...                     sentential_constants=['⊥', '⊤'],
    ...                     metavariables=['A', 'B', 'C'],
    ...                     context_variables=['Γ', 'Δ', 'Σ', 'Λ', 'Π', 'Θ'])

    We now define a parser for that language

    >>> from logics.utils.parsers.standard_parser import StandardParser
    >>> parser = StandardParser(language=language,
    ...                         parse_replacement_dict= {'&': '∧', ' and ': '∧', 'not ': '~',
    ...                                                  '==>': '⇒', 'Gamma': 'Γ', 'Delta': 'Δ'},
    ...                         # Note the whitespaces in the keys above, in ' and ' and 'not '
    ...                         infix_cts=['∧'], comma_separator=',', inference_separator='/',
    ...                         derivation_step_separator=';', two_sided_sequent_separator='⇒',
    ...                         n_sided_sequent_separator='|')

    With that, we can do things like the following:

    >>> f = parser.parse('~(p and not q)')
    >>> f
    ['~', ['∧', ['p'], ['~', ['q']]]]
    >>> type(f)
    <class 'logics.classes.propositional.formula.Formula'>
    >>> parser.unparse(f)
    '~(p ∧ ~q)'
    >>> i = parser.parse('(p / p) // (q / p & not p)')
    >>> i
    ([([['p']] / [['p']])] // [([['q']] / [['∧', ['p'], ['~', ['p']]]])])
    >>> type(i)
    <class 'logics.classes.propositional.inference.Inference'>
    >>> parser.unparse(i)
    '(p / p) // (q / p ∧ ~p)'
    >>> s = parser.parse('Gamma, A ==> Delta')
    >>> s
    [['Γ', ['A']], ['Δ']]
    >>> type(s)
    <class 'logics.classes.propositional.proof_theories.sequents.Sequent'>
    >>> parser.unparse(s)
    'Γ, A ⇒ Δ'

    There are some pre-instantiated parsers for common languages (such as classical language and its fragments), e.g:

    >>> from logics.utils.parsers import classical_parser
    >>> classical_parser.parse('p iff not (p or q)')
    ['↔', ['p'], ['~', ['∨', ['p'], ['q']]]]

    The instances are documented below in this document.

    Suppose you want to use the classical parser, but want to use ``'⊃'`` and ``'≡'`` instead of ``'→'`` and ``'↔'``.
    Instead of redefining everything again (the language, parser, every model theory and proof theory, etc...) you can
    just add a rule to `parse_replacement_dict` and another to `unparse_replacement_dict` as follows:

    >>> classical_parser.parse_replacement_dict.update({'⊃': '→', '≡': '↔'})
    >>> classical_parser.unparse_replacement_dict.update({'→': '⊃', '↔': '≡'})
    >>> # You can now use '⊃' and '≡' as arguments to the parser
    >>> f = classical_parser.parse('(p ≡ q) and (q ⊃ r)')
    >>> # Internally, the formula is still stored with '→' and '↔'
    >>> f
    ['∧', ['↔', ['p'], ['q']], ['→', ['q'], ['r']]]
    >>> # When unparsing, you will see what you want ('⊃' and '≡')
    >>> classical_parser.unparse(f)
    '(p ≡ q) ∧ (q ⊃ r)'
    """
    def __init__(self, language, parse_replacement_dict=None, unparse_replacement_dict=None, infix_cts=None,
                 comma_separator=',', inference_separator='/', derivation_step_separator=';',
                 two_sided_sequent_separator='⇒', n_sided_sequent_separator='|'):
        if infix_cts is None:
            infix_cts = list()
        if parse_replacement_dict is None:
            parse_replacement_dict = {}
        if unparse_replacement_dict is None:
            unparse_replacement_dict = {}
        self.language = language
        self.parse_replacement_dict = parse_replacement_dict
        self.unparse_replacement_dict = unparse_replacement_dict
        self.infix_cts = infix_cts
        self.comma_separator = comma_separator
        self.inference_separator = inference_separator
        self.derivation_step_separator = derivation_step_separator
        self.two_sided_sequent_separator = two_sided_sequent_separator
        self.n_sided_sequent_separator = n_sided_sequent_separator

    # ------------------------------------------------------------------------------------------------------------------
    # PUBLIC METHODS

    def parse(self, string, replace=True):
        """Parses a string and returns an object of the appropriate type (Formula, Inference or Sequent).

        Will automatically detect the type of object you want to build. If any of the sequent separators are present,
        will return a Sequent; elif the inference separator is present, will return an Inference; otherwise it will
        return a Formula.

        Inferences (of any level) should come between parentheses, e.g. ``'((p / q), (q / r) // p) /// (// (/ p))'``
        (outermost ones can be avoided).

        This is to avoid ambiguity, since, for example ``'p / q, r / s //'`` could be read as
        ``'(p / q, r) (/ s) //'``, ``'(p / q), (r / s) //'`` or ``'(p /) (q, r / s) //'``)
        """
        if not string:
            raise NotWellFormed('An empty string is neither a formula nor an inference')

        if replace:  # This will run only in the first recursive call to parse
            string = self._prepare_to_parse(string)

        if self.two_sided_sequent_separator in string or self.n_sided_sequent_separator in string:
            return self._parse_sequent(string)

        # In both cases, the try block is a trick in order to be able to avoid adding external parentheses
        if self.inference_separator in string:
            if replace:  # For inferences, it only tries adding external parentheses in the first recursive call
                try:
                    return self._parse_inference('(' + string + ')')
                except NotWellFormed:
                    return self._parse_inference(string)
            else:
                return self._parse_inference(string)
        else:
            try:
                return self._parse_formula('(' + string + ')')
            except Exception:
                return self._parse_formula(string)

    def unparse(self, logics_object, first_iteration=True):
        """Takes an object (Formula, Inference or Sequent) and returns a readable string version of it.

        The `first_iteration` parameter is for recursion purposes and should not be altered.
        """
        # Sequent
        if isinstance(logics_object, Sequent):
            unparsed_object = self._unparse_sequent(logics_object)
        # Inference
        elif isinstance(logics_object, Inference):
            if first_iteration:
                unparsed_object =  self._unparse_inference(logics_object)[1:-1]
            else:
                unparsed_object =  self._unparse_inference(logics_object)
        # Formula or PredicateFormula
        else:
            unparsed_object =  self._unparse_formula(logics_object)

        return self._post_unparse(unparsed_object)

    def parse_derivation(self, string, natural_deduction=False):
        """Parse an axiomatic or natural deduction derivation

        `string` must come in the following format:

        .. code-block:: python

            '''p → ((p → p) → p); ax1
            (p → ((p → p) → p)) → ((p → (p → p)) → (p → p)); ax2
            p → (p → p); ax1
            ((p → (p → p)) → (p → p)); mp; [1, 2]
            p → p; mp; [3, 4]'''

        That is, it is a multiline string such that each step comes in a different line. Components of a step must be
        separated by the derivation_step_separator. If the on_steps and open_suppositions are not specified, will assume
        they are an empty list.

        Can also parse Natural deduction derivations, with steps have one extra element for the open suppositions, e.g.:
        ``"p → p; mp; [3, 4]; [1, 2]"``. For that, set `natural_deduction` to True.
        """
        derivation = []
        string = string.strip()  # remove trailing whitespace
        string_list = string.split('\n')
        for string_step in string_list:
            derivation.append(self._parse_derivation_step(string_step.strip(), natural_deduction))
        return Derivation(derivation)

    def to_latex(self, formula_or_inference):
        # todo someone with better knowledge of LaTeX than I should do this
        if isinstance(formula_or_inference, Formula):
            pass
        if isinstance(formula_or_inference, Inference):
            pass

        raise NotImplementedError()

    # ------------------------------------------------------------------------------------------------------------------
    # ------------------------------------------------------------------------------------------------------------------
    # PRIVATE METHODS

    def _prepare_to_parse(self, string):
        """Prepares a string to be parsed. For example, replaces & for ∧,  deletes whitespaces, etc.

        E.g. will turn '(p / q & p) // q' into '(p/1]q∧p)/2]q'
        """
        # First it replaces the expressions in the dict
        for expression in self.parse_replacement_dict:
            string = string.replace(expression, self.parse_replacement_dict[expression])

        # Then replaces / for /1], // for /2], /// for /3] etc, for things like '/ // /', since we'll delete whitespaces
        # and we do not want to return the metainference '////'
        # The ] at the end is for the PredicateParser, since we could give the string /1+1=2 and we do not want that
        # turned into /11+1=2, taken as an inference of level 11
        if self.inference_separator in string:
            separator_level = 0
            # This loop has to go backwards since we will be modifying the string
            for char_index in range(len(string) - 1, -1, -1):
                if string[char_index] == self.inference_separator:  # It found an inference separator at the right
                    separator_level += 1
                    # if there are further separators at the left
                    if char_index > 0 and string[char_index - 1] == self.inference_separator:
                        pass
                    else:  # If not, replace the following for the separator level
                        string = string[:char_index + 1] + str(separator_level) + ']' + \
                                 string[char_index+1+separator_level-1:]
                        separator_level = 0  # reset the separator level

        # Lastly, deletes whitespaces
        string = string.replace(' ', '')

        return string

    def _post_unparse(self, string):
        """Runs after unparsing an object"""
        for expression in self.unparse_replacement_dict:
            string = string.replace(expression, self.unparse_replacement_dict[expression])
        return string

    # ------------------------------------------------------------------------------------------------------------------
    # FORMULAE

    def _parse_formula(self, string):
        """Takes a string (prepared by the methods above) and returns an instance of Formula

        Formulae with binary constants must come between parentheses (see the trick above to avoid the outermost ones)
        """
        # Atomics go back directly
        if self._is_atomic(string):
            return self._parse_atomic(string)
        return self._parse_molecular(string)

    def _is_atomic(self, string):
        """In propositional languages, atomics are either propositional letters, metavariables or
        sentential constants"""
        return self.language.is_atomic_string(string) or self.language.is_metavariable_string(string) \
                or self.language.is_sentential_constant_string(string)

    def _parse_atomic(self, string):
        return Formula([string])

    def _parse_molecular(self, string, Formula=Formula):
        # Formula is a parameter for the formula class, by default Formula. The predicate parser will call this with
        # Formula = PredicateFormula

        # Unary, prefix binary or >1-arity (prefix) constant
        # Check to see if it begins with any of the constants (infix case)
        for constant in self.language.constants():
            arity = self.language.arity(constant)

            # Unary constants do not add parenthesis
            if arity == 1 and string[:len(constant)] == constant:
                return Formula([constant, self.parse(string[len(constant):], replace=False)])

            # >1-arity constants written in infix notation
            if string[:len(constant)+1] == constant + '(':  # The string begins with 'constant('
                # Otherwise, separate the arguments that come between () and parse each one
                arguments = parser_utils.separate_arguments(string[len(constant):], self.comma_separator)
                if len(arguments) != arity:
                    raise NotWellFormed(f'Incorrect arity for constant {constant} in string {string}')
                parsed_arguments = [self.parse(arg, replace=False) for arg in arguments]
                return Formula([constant] + parsed_arguments)

        # Binary infix formula
        # If the string begins and ends with parenthesis, it can be a binary infix formula
        if string[0] == '(' and string[-1] == ')':
            binary_ct, binary_ct_index = parser_utils.get_main_constant(string, self.infix_cts)
            if binary_ct is not None:
                return Formula([binary_ct, self.parse(string[1:binary_ct_index], replace=False),
                                self.parse(string[binary_ct_index + len(binary_ct):-1], replace=False)])

        # If we did not return until now, we are in presence of something that is not a wff
        raise NotWellFormed(string + " is not a well-formed propositional formula for the language given")

    def _unparse_formula(self, formula, remove_external_parentheses=True):
        """Turns a Formula back into a readable string
        e.g. Formula('∨', Formula(['q']), Formula(['p'])) is turned into 'q ∨ p'
        """
        # Atomic
        if formula.is_atomic:
            return self._unparse_atomic(formula)
        return self._unparse_molecular(formula, remove_external_parentheses)

    def _unparse_atomic(self, formula):
        return formula[0]

    def _unparse_molecular(self, formula, remove_external_parentheses):
        # Unary operator
        if formula.main_symbol in self.language.constants(1):
            return f"{formula[0]}{self._unparse_formula(formula[1], remove_external_parentheses=False)}"

        # Binary infix operator
        elif formula.main_symbol in self.infix_cts:
            unp_formula = f"({self._unparse_formula(formula[1], False)} {formula[0]} {self._unparse_formula(formula[2], False)})"
            if remove_external_parentheses:
                return unp_formula[1:-1]
            return unp_formula

        # Prefix >1-arity operator
        else:
            string = formula.main_symbol + '('
            for arg in formula.arguments():
                string += self._unparse_formula(arg, remove_external_parentheses=False)
                string += ', '
            string = string[:-2] + ')'  # remove final ', ' and add final parenthesis
            return string

    # ------------------------------------------------------------------------------------------------------------------
    # INFERENCES

    def _parse_inference(self, string):
        """Takes a stirng and returns an Inference. See above for the format. Do not call this method directly.
        """
        # First we need to detect the level of the inference
        level = None
        for char_index in range(len(string)):
            if string[char_index] == self.inference_separator:
                for char2_index in range(char_index+1, len(string)+1):
                    if string[char2_index] != ']':
                        # The level of this particular apparition of the inference separator
                        case_level = int(string[char_index+1:char2_index+1])
                        # If bigger than the previous level, replace
                        if level is None or case_level > level:
                            level = case_level
                    else:
                        break
        if level is None:
            raise NotWellFormed('Something went wrong. Make sure your inference separator is 1 character long.')

        # Then we see if the top level separator is repeated and raise error
        separator = self.inference_separator + str(level) + ']'
        if string.count(separator) > 1:
            raise NotWellFormed(f'More than one ocurrence of the top-level conclusion separator in {string}')

        # Every inference comes between parentheses, so we remove those
        if not (string[0] == '(' and string[-1] == ')'):
            raise NotWellFormed(f'Inference {string} did not come between parentheses')
        string = string[1:-1]

        # Split the inference at the top level separator
        premises, conclusions = string.split(separator)  # Up to now we have 'prem1,prem2,...' and 'c1,c2,...' (strings)
        # prem1, prem2, c1, c2, ... might be formulae (e.g.'(pvq),p,...') or inferences (e.g. '(p/q,r),(p,q/r),...')

        # Premises
        if premises == '':  # Empty premises
            premises = []
        else:  # Non-empty premises
            # separate_arguments requires external parentheses
            premises = parser_utils.separate_arguments('(' + premises + ')', self.comma_separator)

        # Conclusions (idem)
        if conclusions == '':
            conclusions = []
        else:
            conclusions = parser_utils.separate_arguments('(' + conclusions + ')', self.comma_separator)

        # For an empty (meta)inference declare the level
        if not premises and not conclusions:
            return Inference([], [], level=level)
        else:
            return Inference([self.parse(p, replace=False) for p in premises],
                             [self.parse(c, replace=False) for c in conclusions])

    def _unparse_inference(self, inference):
        """Same as above but with inferences.
        e.g. turns Inference([Inference([Formula(['p'])], [Formula(['p'])])], []) into 'p / p //'
        """
        separator = self.inference_separator * inference.level

        premises = ''
        if inference.premises:
            for premise in inference.premises:
                premises += self.unparse(premise, first_iteration=False) + ', '
            premises = premises[:-2] + ' '  # Remove the final ', ' and add a space

        conclusions = ''
        if inference.conclusions:
            for conclusion in inference.conclusions:
                conclusions += self.unparse(conclusion, first_iteration=False) + ', '
            conclusions = ' ' + conclusions[:-2]  # Same as before and add a space at the beginning

        return f"({premises}{separator}{conclusions})"

    # ------------------------------------------------------------------------------------------------------------------
    # DERIVATIONS

    def _parse_derivation_step(self, string_step, natural_deduction=False):
        """Derivation steps must come in the following format: ((p → (p → p)) → (p → p)); mp; [1, 2]
        That is, there is the content, the name of the rule and the on_steps, all separated by the deriv_step_separator
        on_steps must be written as lists. If on_steps is not given, the parser assumes that it is []
        e.g. p → ((p → p) → p); ax1
        You can also use 'premise' and 'axiom' as justifications
        """
        string_step_elements = string_step.split(self.derivation_step_separator)
        content = self.parse(string_step_elements[0].strip())
        justification = string_step_elements[1].strip()

        if natural_deduction and len(string_step_elements) == 3:
            raise ValueError(f'Ambiguous step specification for {string_step}, natural deduction steps needs to have '
                             f'either 2 or 4 components')

        if len(string_step_elements) == 2 or string_step_elements[2].strip() == '':
            on_steps = []
        else:
            on_steps = eval(string_step_elements[2].strip())
            # Remove repeated steps in the on_steps - and print warning if it does
            if len(on_steps) != len(set(on_steps)):
                for step_index in range(len(on_steps) - 1, -1, -1):
                    step = on_steps[step_index]
                    if on_steps.count(step) > 1:
                        del on_steps[step_index]
                print(f'Warning: Repeated step in on_steps was removed in {string_step}')

        if natural_deduction:
            if len(string_step_elements) == 2 or string_step_elements[3].strip() == '':
                open_suppositions = []
            else:
                open_suppositions = eval(string_step_elements[3].strip())
            return NaturalDeductionStep(content=content, justification=justification, on_steps=on_steps,
                                        open_suppositions=open_suppositions)
        else:
            return DerivationStep(content=content, justification=justification, on_steps=on_steps)

    # ------------------------------------------------------------------------------------------------------------------
    # SEQUENTS

    def _parse_sequent(self, string):
        """Sequents come in standard notation, examples are:
        'Γ, ~A ⇒ Δ' (two-sided)
        'Γ, ~A | Γ, ~A | Γ, A' (n>2-sided)
        """
        string = self._prepare_to_parse(string)
        if self.two_sided_sequent_separator in string:
            if string.count(self.two_sided_sequent_separator) > 1 or self.n_sided_sequent_separator in string:
                raise NotWellFormed('Two-sided sequents can contain only one separator')
            unparsed_sequent = string.split(self.two_sided_sequent_separator)
        elif self.n_sided_sequent_separator in string:
            unparsed_sequent = string.split(self.n_sided_sequent_separator)
        else:
            raise NotWellFormed('No sequent separators found in string')

        parsed_sequent = list()
        for side in unparsed_sequent:
            # Empty side
            if side == '':
                parsed_sequent.append([])
            else:
                unparsed_side = side.split(self.comma_separator)
                parsed_side = list()
                for elem in unparsed_side:
                    # Context variables go in as they came
                    if elem in self.language.context_variables:
                        parsed_side.append(elem)
                    # Formulae are parsed
                    else:
                        parsed_side.append(self.parse(elem, replace=False))
                parsed_sequent.append(parsed_side)

        return Sequent(parsed_sequent)

    def _unparse_sequent(self, sequent):
        if sequent.sides == 2:
            separator = self.two_sided_sequent_separator
        else:
            separator = self.n_sided_sequent_separator

        string = ''
        for side in sequent:
            if side:
                for elem in side:
                    # Context variable
                    if elem in self.language.context_variables:
                        string += f'{elem}{self.comma_separator} '
                    # Formula
                    else:
                        string += f'{self._unparse_formula(elem)}{self.comma_separator} '
                string = string[:-1 - len(self.comma_separator)]  # Remove the last ', '
            string += f' {separator} '  # And add ' separator '

        # After unparsing all sides remove the last separator
        return string[:-2 - len(separator)]


# ----------------------------------------------------------------------------------------------------------------------
# ----------------------------------------------------------------------------------------------------------------------
# INSTANCES

from logics.instances.propositional.languages import classical_infinite_language_with_sent_constants, \
    LFI_language, modal_infinite_language_with_sent_constants


classical_parse_replacement_dict = {
    # For negation
    '¬': '~',
    'not ': '~',

    # For conjunction
    '&': '∧',
    '^': '∧',
    ' and ': '∧',  # notice the spaces before and after 'and'

    # For disjunction
    'v': '∨',  # The key is a letter v, so if you plan to use this parser dont use that as an atomic of Language
    ' or ': '∨',

    # For conditional
    ' then ': '→',
    '-->': '→',
    'if ': '',  # if you write ' if p then q' it will just leave 'p then q'

    # For biconditional
    ' iff ': '↔',
    '<->': '↔',

    # For the semantic hammer
    '|=': '/',

    # Sentential constants
    'falsum': '⊥',
    'Falsum': '⊥',
    'bottom': '⊥',
    'Bottom': '⊥',
    'verum': '⊤',
    'Verum': '⊤',
    'Top': '⊤',
    'top': '⊤',

    # For sequent calculi
    '==>': '⇒',
    'Gamma': 'Γ',
    'Delta': 'Δ',
    'Sigma': 'Σ',
    'Pi': 'Π',
    'Theta': 'Θ',
    'Lambda': 'Λ',
}

classical_parser = StandardParser(language=classical_infinite_language_with_sent_constants,
                                  parse_replacement_dict=classical_parse_replacement_dict,
                                  infix_cts=['∧', '∨', '→', '↔'],
                                  comma_separator=',', inference_separator='/', derivation_step_separator=';')

LFI_replacement_dict = copy(classical_parse_replacement_dict)
LFI_replacement_dict.update({
    "inc ": "•",
    "inconsistent ": "•",
    "con ": "◦",
    "consistent ": "◦",
    "°": "◦",
})
LFI_parser = StandardParser(language=LFI_language,
                            parse_replacement_dict=LFI_replacement_dict,
                            infix_cts=['∧', '∨', '→', '↔'],
                            comma_separator=',', inference_separator='/', derivation_step_separator=';')

modal_replacement_dict = copy(classical_parse_replacement_dict)
modal_replacement_dict.update({
    'box ': '□',
    'Box ': '□',
    'necessary ': '□',
    'nec ': '□',
    '◻': '□',
    'diamond ': '◇',
    'Diamond ': '◇',
    'possible ': '◇',
    'pos ': '◇'
})

modal_parser = StandardParser(language=modal_infinite_language_with_sent_constants,
                              parse_replacement_dict=modal_replacement_dict,
                              infix_cts=['∧', '∨', '→', '↔'],
                              comma_separator=',', inference_separator='/', derivation_step_separator=';')
