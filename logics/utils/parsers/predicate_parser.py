from copy import deepcopy

from logics.utils.parsers import parser_utils
from logics.classes.exceptions import NotWellFormed
from logics.classes.predicate import PredicateFormula
from logics.utils.parsers.standard_parser import StandardParser


class PredicateParser(StandardParser):
    """Parser for predicate languages.

    Extends ``StandardParser``. Has two additional parameters to specify infix predicates and functions.
    Also includes some changes in the format of the valid input:

    * Atomics must be given in format ``"R(a, b, c)"`` for prefix predicates, or ``"a = b"`` for infix predicates
    * Infix predicate formuale must come without outer parentheses, e.g. ``"(a = b)"`` is not well formed
    * Outermost parentheses in infix function terms can be ommited, e.g. both ``"0+(0+0)"`` and ``"(0+(0+0))"`` are ok
    * Infix predicates and function symbols CANNOT be given in prefix notation
    * Quantified formulae come in format ∀x (A) or ∀x ∈ T (A) - Always add parentheses to the quantified formula

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
    infix_pred: list of str, optional
        The list of predicates that will be written in infix notation
    infix_func: list of str, optional
        The list of function symbols that will be written in infix notation
    comma_separator: str, optional
        Character (preferrably of len 1) used to separate the premises or separate the conclusions within an inference
    inference_separator: str, optional
        Character (preferrably of len 1) used to separate between the premises and conclusions in an inference
    derivation_step_separator: str, optional
        Character (preferrably of len 1) used to separate the components of a derivation step

    Examples
    --------
    >>> from logics.instances.predicate.languages import real_number_arithmetic_language
    >>> from logics.utils.parsers.predicate_parser import PredicateParser
    >>> replacement_dict = {
    ...                         '¬': '~', 'not ': '~',
    ...                         '&': '∧', ' and ': '∧',  # notice the spaces before and after 'and'
    ...                         'v': '∨',  ' or ': '∨',
    ...                         ' then ': '→', '-->': '→', 'if ': '',  # 'if p then q' it will convert to 'p then q'
    ...                         ' iff ': '↔', '<->': '↔',
    ...                         'forall ': '∀', 'exists ': '∃', ' in ': '∈'
    ...                     }
    >>> real_number_arithmetic_parser = PredicateParser(language=real_number_arithmetic_language,
    ...                                                 parse_replacement_dict=replacement_dict,
    ...                                                 infix_cts=['∧', '∨', '→', '↔'],
    ...                                                 infix_pred=['=', '<', '>'], infix_func=['+', '*', '**'])
    >>> real_number_arithmetic_parser.parse("0.5 + 0.5 = 1")
    ['=', ('+', '0.5', '0.5'), '1']
    >>> f = real_number_arithmetic_parser.parse("1 + 1 = 2 or exists x (x + 1 = 2)")
    >>> f
    ['∨', ['=', ('+', '1', '1'), '2'], ['∃', 'x', ['=', ('+', 'x', '1'), '2']]]
    >>> type(f)
    <class 'logics.classes.predicate.formula.PredicateFormula'>
    >>> real_number_arithmetic_parser.unparse(f)
    '1 + 1 = 2 ∨ ∃x (x + 1 = 2)'
    >>> # Infix predicates and function symbols cannot be given in prefix notation
    >>> real_number_arithmetic_parser.parse("=(+(1,1),2)")
    Traceback (most recent call last):
    ...
    IndexError: string index out of range

    Examples with a predefined parser for a language with prefix predicates and function symbols (see below for
    more predefined instances):

    >>> from logics.utils.parsers.predicate_parser import classical_predicate_parser
    >>> classical_predicate_parser.parse("R(a, b) or P(f(a))")
    ['∨', ['R', 'a', 'b'], ['P', ('f', 'a')]]
    >>> classical_predicate_parser.parse("forall x in f(a) (if ~P(x) then P(x))")
    ['∀', 'x', '∈', ('f', 'a'), ['→', ['~', ['P', 'x']], ['P', 'x']]]
    """
    def __init__(self, language, parse_replacement_dict, unparse_replacement_dict=None, infix_cts=None, infix_pred=None,
                 infix_func=None, comma_separator=',', inference_separator='/', derivation_step_separator=';'):
        if infix_pred is None:
            infix_pred = list()
        if infix_func is None:
            infix_func = list()
        self.infix_pred = infix_pred
        self.infix_func = infix_func
        super().__init__(language=language, parse_replacement_dict=parse_replacement_dict,
                         unparse_replacement_dict=unparse_replacement_dict,
                         infix_cts=infix_cts, comma_separator=comma_separator, inference_separator=inference_separator,
                         derivation_step_separator=derivation_step_separator)

    # ------------------------------------------------------------------------------------------------------------------
    # PARSE FORMULA METHODS

    def _is_atomic(self, string):
        """To identify if a string as an atomic formula, check that it does not contain constants and quantifiers"""
        for quant in self.language.quantifiers:
            if quant in string:
                return False
        for ctt in self.language.constants():
            if ctt in string:
                return False
        return True

    def _parse_atomic(self, string):
        # First check if it is a sentential constant
        if self.language.is_sentential_constant_string(string):
            return PredicateFormula([string])

        # Check for an infix predicate
        # There can only be one, so this will suffice, no need to call parser_utils.get_main_constant
        infix_predicate = False
        for pred in self.infix_pred:
            if pred in string:
                infix_predicate = True
                pred_index = string.index(pred)
                break
        if infix_predicate:
            # Infix predicate formulae are always binary
            return PredicateFormula([pred, self.parse_term(string[:pred_index], replace=False),
                                     self.parse_term(string[pred_index+len(pred):], replace=False)])

        # Non-infix predicate
        for pred in self.language.predicates() | set(self.language.predicate_variables):
            if string[:len(pred) + 1] == pred + '(':
                arity = self.language.arity(pred)
                unparsed_terms = parser_utils.separate_arguments(string[len(pred):], ',')
                if len(unparsed_terms) != arity:
                    raise NotWellFormed(f'Incorrect arity for predicate {pred} in atomic {string}')
                parsed_arguments = [self.parse_term(term, replace=False) for term in unparsed_terms]
                return PredicateFormula([pred] + parsed_arguments)

        # If you did not return thus far, string is not a wff
        raise NotWellFormed(f'String {string} is not a valid atomic formula')

    def parse_term(self, string, replace=True):
        """Parses an individual term

        If `replace` is ``True``, will apply the `parse_replacement_dict` to the string before parsing the term.
        Otherwise, it will not.

        Examples
        --------
        >>> from logics.utils.parsers.predicate_parser import realnumber_arithmetic_parser
        >>> realnumber_arithmetic_parser.parse_term("1+1")
        ('+', '1', '1')
        >>> realnumber_arithmetic_parser.parse_term("1+(1+2)")
        ('+', '1', ('+', '1', '2'))
        >>> realnumber_arithmetic_parser.parse_term("(1+(1+2))")
        ('+', '1', ('+', '1', '2'))
        """
        # If a valid individual variable or constant, return it as it came
        if replace:
            string = self._prepare_to_parse(string)

        if self.language._is_valid_individual_constant_or_variable(string):
            return string

        # Search for an infix operator
        # First try adding external parentheses (in order to avoid giving external ones)
        infix_term = self._parse_infix_term(f'({string})')
        if infix_term is not None:
            return infix_term
        # Then without adding external parentheses
        infix_term = self._parse_infix_term(string)
        if infix_term is not None:
            return infix_term

        # If it did not find infix operators, must be a prefix one
        for func_symbol in self.language.function_symbols:
            if string[:len(func_symbol) + 1] == func_symbol + '(':
                arity = self.language.arity(func_symbol)
                unparsed_arguments = parser_utils.separate_arguments(string[len(func_symbol):], ',')
                if len(unparsed_arguments) != arity:
                    raise NotWellFormed(f'Incorrect arity for function symbol {func_symbol} in term {string}')
                parsed_arguments = tuple(self.parse_term(term, replace=False) for term in unparsed_arguments)
                return (func_symbol,) + parsed_arguments

        # If you did not return thus far, string is not a term
        raise NotWellFormed(f'String {string} is not a valid term')

    def _parse_infix_term(self, string):
        # If not between parentheses, its something of the form 's(0+0)' and not '(0+0)'
        if string[0] != '(' or string[-1] != ')':
            return None
        infix_function, index = parser_utils.get_main_constant(string, self.infix_func)
        if infix_function is not None:
            return (infix_function, self.parse_term(string[1:index], replace=False),
                    self.parse_term(string[index + len(infix_function):-1], replace=False))
        return None

    def _parse_molecular(self, string, Formula=PredicateFormula):
        """Here we need only add the quantifier case and call super"""
        for quantifier in self.language.quantifiers:
            # The string begins with the quantifier
            if string[:len(quantifier)] == quantifier:
                current_index = len(quantifier)  # The current index is the position after the quantifier

                # Get the variable
                variable = None
                for char_index in range(current_index, len(string)):
                    if self.language._is_valid_variable(string[len(quantifier):char_index+1]):
                        variable = string[len(quantifier):char_index+1]
                        current_index = char_index + 1  # The current index is the position after the variable
                    else:
                        break
                if variable is None:
                    raise NotWellFormed(f'Incorrect variable specification in quantified formula {string}')

                # See if the quantifier is bounded and parse the bound
                bounded = False
                formula_opening_parenthesis_index = parser_utils.get_last_opening_parenthesis(string)
                if formula_opening_parenthesis_index is None:
                    raise NotWellFormed(f'Quantified formula in {string} must come between parentheses')
                elif string[current_index] == '∈':
                    bounded = True
                    current_index += 1
                    unparsed_term = string[current_index:formula_opening_parenthesis_index]
                    parsed_term = self.parse_term(unparsed_term, replace=False)
                # We have a non bounded-formula, the parenthesis must come immediately after the variable
                elif formula_opening_parenthesis_index != current_index:
                    raise NotWellFormed(f'Quantified formula in {string} must come between parentheses')

                # Lastly, parse the formula
                unparsed_formula = string[formula_opening_parenthesis_index+1:-1]
                parsed_formula = self.parse(unparsed_formula)

                if not bounded:
                    return PredicateFormula([quantifier, variable, parsed_formula])
                else:
                    return PredicateFormula([quantifier, variable, '∈', parsed_term, parsed_formula])

        return super()._parse_molecular(string, PredicateFormula)

    # ------------------------------------------------------------------------------------------------------------------
    # UNPARSE FORMULA METHODS

    def _unparse_term(self, term, add_parentheses=False):
        # Atomic term
        if not isinstance(term, tuple):
            return term
        # Molecular term (function symbol with arguments)
        # Prefix function symbol
        if term[0] not in self.infix_func:
            unparsed_term = term[0] + '('
            for arg in term[1:]:
                unparsed_term += self._unparse_term(arg) + ', '
            return unparsed_term[:-2] + ')'
        # Infix (and thus binary) function symbol
        else:
            if not add_parentheses:
                return f'{self._unparse_term(term[1], True)} {term[0]} {self._unparse_term(term[2], True)}'
            else:
                # Infix terms inside other infix terms must come between parentheses
                return f'({self._unparse_term(term[1], True)} {term[0]} {self._unparse_term(term[2], True)})'

    def _unparse_atomic(self, formula):
        # Sentential constant or sentential metavariable (atomic formula of length 1)
        if len(formula) == 1:
            return formula[0]
        # Prefix predicate symbol
        if formula[0] not in self.infix_pred:
            unparsed_formula = formula[0] + '('
            for arg in formula[1:]:
                unparsed_formula += self._unparse_term(arg) + ', '
            return unparsed_formula[:-2] + ')'
        # Infix (and thus binary) predicate symbol
        return f'{self._unparse_term(formula[1])} {formula[0]} {self._unparse_term(formula[2])}'

    def _unparse_molecular(self, formula, remove_external_parentheses):
        # Quantified formula
        if formula.main_symbol in self.language.quantifiers:
            # Bounded
            if formula[2] == '∈':
                return f'{formula[0]}{formula[1]} ∈ {self._unparse_term(formula[3])} ({self._unparse_formula(formula[4], remove_external_parentheses=True)})'
            # Unbounded
            return f'{formula[0]}{formula[1]} ({self._unparse_formula(formula[2], remove_external_parentheses=True)})'

        # Non-quantified formula
        return super()._unparse_molecular(formula, remove_external_parentheses)


# ----------------------------------------------------------------------------------------------------------------------
# Parser for arithmetic truth, does Godel coding of things inside Tr predicate
# For example, Tr(⌜x=x⌝) will be parsed as PredicateFormula(['Tr', '514951']).

class ArithmeticTruthParser(PredicateParser):
    """Parser for arithmetic truth

    Subclasses PredicateParser, but does Godel coding of things inside Tr predicate

    Parameters
    ----------
    godel_encoding_function: callable
        The function with which you wish to encode sentences inside Tr predicates
    godel_decoding_function: callable
        The function with which you wish to decode sentences inside Tr predicates
    everything_else_in_PredicateParser
        Everything else present in the parent PredicateParser class

    Examples
    --------
    >>> from logics.instances.predicate.languages import arithmetic_truth_language
    >>> from logics.utils.parsers.parser_utils import godel_encode, godel_decode
    >>> from logics.utils.parsers.predicate_parser import ArithmeticTruthParser
    >>> replacement_dict = {
    ...                         '¬': '~', 'not ': '~',
    ...                         '&': '∧', ' and ': '∧',  # notice the spaces before and after 'and'
    ...                         'v': '∨',  ' or ': '∨',
    ...                         ' then ': '→', '-->': '→', 'if ': '',  # 'if p then q' it will convert to 'p then q'
    ...                         ' iff ': '↔', '<->': '↔',
    ...                         'forall ': '∀', 'exists ': '∃', ' in ': '∈'
    ...                     }
    >>> replacement_dict.update({
    ...     '⌜': 'quote(',
    ...     '⌝': ')'
    ... })
    >>> arithmetic_truth_parser = ArithmeticTruthParser(godel_encoding_function=godel_encode,
    ...                                                 godel_decoding_function=godel_decode,
    ...                                                 language=arithmetic_truth_language,
    ...                                                 parse_replacement_dict=replacement_dict,
    ...                                                 infix_cts=['∧', '∨', '→', '↔'],
    ...                                                 infix_pred=['=', '<', '>'], infix_func=['+', '*', '**'])
    >>> arithmetic_truth_parser.parse('0=0+0')
    ['=', '0', ('+', '0', '0')]
    >>> arithmetic_truth_parser.parse('Tr(⌜0=0+0⌝)')
    ['Tr', '04908990']
    >>> arithmetic_truth_parser.parse('Tr(⌜Tr(⌜0=0⌝)⌝)')
    ['Tr', '4999919899999190490199199']
    >>> arithmetic_truth_parser.parse('λ iff ~Tr(⌜λ⌝)')
    ['↔', ['λ'], ['~', ['Tr', '79999']]]
    """
    def __init__(self, godel_encoding_function, godel_decoding_function, *args, **kwargs):
        # These are two functions that take a string (an UNPARSED formula) and return another string (its code)
        self.godel_encode = godel_encoding_function
        self.godel_decode = godel_decoding_function
        super().__init__(*args, **kwargs)

    def _prepare_to_parse(self, string):
        """Replaces quote(sentence) for code_of_sentence"""
        string = super()._prepare_to_parse(string)
        string = self._remove_quotations(string)
        return string

    def _remove_quotations(self, string):
        # Search for the first apparition of quote and encode the content
        while 'quote(' in string:
            opening_parenthesis_index = string.index('quote(') + 5  # index of the opening parenthesis
            # Get where the closing parenthesis is
            closing_parenthesis_index = parser_utils.get_closing_parenthesis(string[opening_parenthesis_index:]) \
                                        + opening_parenthesis_index
            string_to_encode = string[opening_parenthesis_index+1:closing_parenthesis_index]
            codified_string = self.godel_encode(string_to_encode)
            string = string[:string.index('quote(')] + codified_string + string[closing_parenthesis_index+1:]

        return string

    def _parse_atomic(self, string):
        """Since codes are numerals like 514951 and not s(s(...)) we need to provide a special clause for the truth pred
        otherwise Tr(514951) will raise NotWellFormed
        """
        if string[:3] == 'Tr(':
            arity = 1
            unparsed_terms = parser_utils.separate_arguments(string[2:], ',')
            if len(unparsed_terms) != arity:
                raise NotWellFormed(f'Incorrect arity for predicate Tr in atomic {string}')
            code = unparsed_terms[0]
            try:
                int(code)
            except ValueError:
                raise NotWellFormed(f'String {string} must have a numeral as the argument of Tr')
            # Do not parse the term, just return the numeral
            return PredicateFormula(['Tr', code])

        return super()._parse_atomic(string)


# ----------------------------------------------------------------------------------------------------------------------
# INSTANCES

from logics.instances.predicate.languages import classical_function_language, \
    arithmetic_language, real_number_arithmetic_language, arithmetic_truth_language
from logics.utils.parsers.standard_parser import classical_parse_replacement_dict


predicate_replacement_dict = deepcopy(classical_parse_replacement_dict)
predicate_replacement_dict.update({
    ' in ': '∈',
    'forall ': '∀',
    'exists ': '∃'
})

classical_predicate_parser = PredicateParser(language=classical_function_language,
                                             parse_replacement_dict=predicate_replacement_dict,
                                             infix_cts=['∧', '∨', '→', '↔'])

arithmetic_parser = PredicateParser(language=arithmetic_language,
                                    parse_replacement_dict=predicate_replacement_dict,
                                    infix_cts=['∧', '∨', '→', '↔'],
                                    infix_pred=['=', '<', '>'], infix_func=['+', '*', '**'])

realnumber_arithmetic_parser = PredicateParser(language=real_number_arithmetic_language,
                                               parse_replacement_dict=predicate_replacement_dict,
                                               infix_cts=['∧', '∨', '→', '↔'],
                                               infix_pred=['=', '<', '>'], infix_func=['+', '-', '*', '**', '/', '//'])


truth_predicate_replacement_dict = deepcopy(classical_parse_replacement_dict)
truth_predicate_replacement_dict.update({
    '⌜': 'quote(',
    '⌝': ')'
})
arithmetic_truth_parser = ArithmeticTruthParser(godel_encoding_function=parser_utils.godel_encode,
                                                godel_decoding_function=parser_utils.godel_decode,
                                                language=arithmetic_truth_language,
                                                parse_replacement_dict=truth_predicate_replacement_dict,
                                                infix_cts=['∧', '∨', '→', '↔'],
                                                infix_pred=['=', '<', '>'], infix_func=['+', '*', '**'])
