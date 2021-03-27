from copy import deepcopy
from itertools import product


# Internal format for formulas:
# Each subformula within a formula is a list
# For example, (p or ¬p) parses as [['p'], '˅', ['¬',['p']]]
# Parser accepts things such as "(if p then q)" and "if p then q"
# Unary connectives go out before the formula they apply to, binaries go out in the middle
# For first order, parses atomics as they come in (e.g. "Rax" parses as ["Rax"])
# Quantified strings e.g. ("Vx Px") as ['∀', 'x', ['Px']]

atomics = ['p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'o']
set_terms = ["A", "B", "C", "D", "E", "F", "G", "H", "J"]
binary_set_operations = ['∩', '∪', '−', '×']
reserved_terms = atomics[:]
reserved_terms.extend(['(', ')', ',', "'", '"', "V", "E", "$", "%"])
FOL_individual_constants = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n']
FOL_variables = ['x', 'y', 'z', 'w', 'v', 'u']
FOL_predicates = ['P', 'Q', 'R', 'S', 'T', 'U', 'A', 'B', 'C']

# ----------------------------------------------------------------------------------------------------------------------
# PROPOSITIONAL LOGIC


def parse_propositional(string, logic):
    """Takes a string an transforms it into a formula of the format defined above
    ¡¡¡This function prepares the formula, the next one parses it!!!"""

    # An empty string returns an error
    if not string:
        ValueError("An empty string is not a well-formed propositional formula")

    # Delete the ifs
    string = string.replace('if ', '')

    # Parse constants
    for con in logic.parsed_constants:
        string = string.replace(con, logic.parsed_constants[con])
    string = string.replace("falsum", "⊥")
    string = string.replace("Falsum", "⊥")

    # Remove spaces
    string = string.replace(" ", "")

    # Trick so that binaries do not have to contain external parentheses
    try:
        formula = parse_propositional2('(' + string + ')', logic)
        return formula
    except ValueError:
        pass

    formula = parse_propositional2(string, logic)
    return formula


def parse_propositional2(string, logic):
    # Atomics go back directly
    if string in atomics or string == '⊥':
        return [string]

    # It recognizes if it is in presence of a negated or binary formula
    # Checks if unary:
    if string[0] in logic.constants(1):
        return [string[0], parse_propositional2(string[1:], logic)]
    
    # Checks if binary (starts and ends with parentheses)
    elif string[0] == '(' and string[-1] == ')':
        # Searches for a constant that has 1 more left parenthesis open than right
        num_parentheses_left = 0
        num_parentheses_right = 0
                
        for x in range(len(string)):
            if string[x] == '(':
                num_parentheses_left += 1
            elif string[x] == ')':
                num_parentheses_right += 1
            elif string[x] in logic.constants(2) and num_parentheses_left == num_parentheses_right + 1:
                return [parse_propositional2(string[1:x], logic), string[x],
                        parse_propositional2(string[x+1:-1], logic)]

        # If the string starts and ends with parentheses, but did not return at this point, raise an error
        raise ValueError(string + " is not a well-formed propositional formula")

    # If we did not enter any of the above, then the string is not a formula, and we just return an error
    else:
        raise ValueError(string + " is not a well-formed propositional formula")


def unparse_propositional_formula(formula, logic):
    form1 = deepcopy(formula)
    form1 = unparse_propositional_parentheses(form1, logic)
    form1 = unparse_propositional_rest(form1, logic)
    return form1


def unparse_propositional_parentheses(formula, logic):
    # If atomic
    if len(formula) == 1:
        return formula[0]
    # If unary connective
    elif len(formula) == 2:
        formula[1] = unparse_propositional_parentheses(formula[1], logic)
        # If the next one is atomic (i.e. [¬, p])
        if type(formula[1]) == str:
            return formula
        # If the next one is unary (i.e. [¬, [¬, phi]] )
        elif len(formula[1]) == 2:
            formula = [formula[0], formula[1][0], formula[1][1]]  # Turns it into [¬, ¬, phi]
            return formula
        # If the next one has length 3
        elif len(formula[1]) == 3:
            # If a unary is in the middle [¬ [¬, ¬, phi]]
            if formula[1][1] in logic.constants(1):
                formula[1].insert(0, formula[0])
                formula = formula[1]
                return formula
            # If that does not happen, the next is a binary and should be left as is
            else:
                return formula
        # If no contitional was entered before, then length > 3, eg  [¬, [¬, ¬, ¬, phi]]
        else:
            formula[1].insert(0, formula[0])
            formula = formula[1]
            return formula
    # If the formula is binary
    elif len(formula) == 3:
        formula[0] = unparse_propositional_parentheses(formula[0], logic)
        formula[2] = unparse_propositional_parentheses(formula[2], logic)
        return formula


def unparse_propositional_rest(formula, logic):
    # If atomic (eg 'p') or falsum
    if len(formula) == 1:
        return formula
    # If binary
    elif len(formula) == 3 and formula[1] in logic.constants(2):
        formula0 = unparse_propositional_rest(formula[0], logic)
        formula2 = unparse_propositional_rest(formula[2], logic)
        unparsed_formula = f"({formula0} {formula[1]} {formula2})"
        return unparsed_formula
    # If not atomic or binary, it is some chain of unaries [¬, ¬, .., phi]
    else:
        last_formula = unparse_propositional_rest(formula[-1], logic)
        formula = formula[:-1]  # Remove unparsed Phi
        formula.append(last_formula)  # Add parsed Phi
        unparsed_formula = str(formula)
        unparsed_formula = unparsed_formula.replace("'", "")
        unparsed_formula = unparsed_formula.replace(",", "")
        for ucon in logic.constants(1):
            # Remove space after unary connectives
            while ucon + " " in unparsed_formula:
                unparsed_formula = unparsed_formula.replace(ucon + " ", ucon)
        return unparsed_formula[1:-1]  # This is to remove the []


# Propositional arguments
def parse_propositional_argument(own_argument_string, logic):
    """WILL NOT CHECK IF THE ARGUMENT IS VALID DUE TO A CIRCULAR IMPORT ERROR - CHECK IN THE CALLING FUNCTION"""
    warning = False
    own_argument_string = own_argument_string.strip()
    own_argument_string = own_argument_string.replace(" ", "")

    if own_argument_string.count("/") != 1:
         raise ValueError("[Argument must contain a single conclusion prefaced with '/']")

    # A no-premise argument is given
    if own_argument_string[0] == "/":
        try:
           concl = parse_propositional(own_argument_string[1:], logic)
        except ValueError:
            raise ValueError('[The string given as conclusion is not a well-formed formula]')
        if not str(logic) == "Classical":
           warning = True
        return [[], concl, warning]

    # An argument with premises is given
    else:
        prems = []
        own_argument_string = own_argument_string.replace('/', ',')
        formulas = separate_arguments('(' + own_argument_string + ')')
        for x in range(len(formulas[:-1])):
            try:
                prems.append(parse_propositional(formulas[x], logic))
            except ValueError:
                raise ValueError(f'[Premise {x+1} is not a well-formed formula]')
        try:
            concl = parse_propositional(formulas[-1], logic)
        except ValueError:
            raise ValueError('[Conclusion given is not a well-formed formula]')
        if not str(logic) == "Classical":
           warning = True
        return [prems, concl, warning]


def unparse_propositional_argument(argument, logic):
    """Argument comes in form [ [prem1, prem2], conclusion] """

    argument_string = ''
    premises = argument[0]
    conclusion = argument[1]
    for premise in premises:
        argument_string += unparse_propositional_formula(premise, logic) + ', '
    # Remove last comma and add /
    argument_string = argument_string[:-2] + ' / '
    argument_string += unparse_propositional_formula(conclusion, logic)
    return argument_string


# ----------------------------------------------------------------------------------------------------------------------
# SET THEORY


def unparse_set_operation(string):
    """Rewrites a set operation in prefix notation into infix notation"""

    string = string.replace(" ", "")

    if string[:2] == '℘(':
        parsed_argument = unparse_set_operation(string[2:-1])
        return f'℘({parsed_argument})'

    elif string[0] in binary_set_operations:
        args = separate_arguments(string[1:])
        arg1 = unparse_set_operation(args[0])
        arg2 = unparse_set_operation(args[1])
        return f'({arg1} {string[0]} {arg2})'

    else:
        return string


def parse_set_operation(string):
    """This function prepares the formula, the next one parses it
    Operations are written in infix notation. Use U for union, I for intersection - for complement, P for pset,
     X for cartesian product. Also accepts union, inters, cartp, complem, pset"""

    string = string.replace('U', '∪')
    string = string.replace('I', '∩')
    string = string.replace('X', '×')
    string = string.replace('-', '−')
    string = string.replace('P', '℘')

    string = string.replace('union', '∪')
    string = string.replace('inters', '∩')
    string = string.replace('cartp', '×')
    string = string.replace('complem', '−')
    string = string.replace('pset', '℘')

    string = string.replace(" ", "")

    # Trick so that external parentheses don't have to be put
    try:
        string2 = parse_set_operation2(f'({string})')
        return string2
    except ValueError:
        string = parse_set_operation2(string)

    return string


def parse_set_operation2(string):
    """Basically rewrittes a set operation string into prefix notation"""

    # Atomic
    if string in set_terms:
        return string

    # Unary operation (powerset)
    if string[:2] == '℘(' and string[-1] == ')':
        formula_inside = parse_set_operation2(string[2:-1])
        return f'℘({formula_inside})'

    # Binary operation
    elif string[0] == '(' and string[-1] == ')':

        # Searches for an operation that has 1 more left parenthesis open than right
        num_parentheses_left = 0
        num_parentheses_right = 0

        for x in range(len(string)):
            if string[x] == '(':
                num_parentheses_left += 1
            elif string[x] == ')':
                num_parentheses_right += 1
            elif string[x] in binary_set_operations and num_parentheses_left == num_parentheses_right + 1:
                # This if is to check that there are spaces before and after the binary operation
                operation = string[x]
                first_arg = parse_set_operation2(string[1:x])
                second_arg = parse_set_operation2(string[x+1:-1])
                return f'{operation}({first_arg},{second_arg})'

        raise ValueError('Invalid set operation')

    raise ValueError('Invalid set operation')


def parse_own_sets(string):
    """Format is A = {...}; B = {...}"""

    set_dict = dict()
    list_dict = dict()

    string = string.replace(" ", "")

    args = string.split(";")

    for arg in args:
        if arg[0] not in set_terms:
            incorrect_name = arg[:arg.index("=")]
            raise ValueError(f'[{incorrect_name} is not a valid set name]')
        if arg[1] != '=' or arg[2] != '{' or arg[-1] != '}':
            raise ValueError('[Set specification must be in format "set_name = {element1, element2, ...}"]')

        set_elements_string = arg[3:-1]

        list_dict[arg[0]] = parse_list_elements(set_elements_string)
        set_dict[arg[0]] = parse_set_elements(set_elements_string)

    return [set_dict, list_dict]


def parse_list_elements(string):
    """Takes a string of format 1,2,3,{1,2} and returns the LIST!!! of those things
    If an element contains {} or <> takes it as a set (LIST) or a tuple"""

    string = string.replace('{', 'set(')
    string = string.replace('}', ')')
    string = string.replace('<', 'tuple(')
    string = string.replace('>', ')')

    args = separate_arguments(f'({string})')

    for x in range(len(args)):
        # Empty set
        if args[x] == 'set()':
            args[x] = list()
        # Empty tuple
        if args[x] == 'tuple()':
            args[x] = tuple()
        # Set
        elif args[x][:4] == 'set(' and args[x][-1] == ')':
            args[x] = parse_list_elements(args[x][4:-1])
        # Tuple
        elif args[x][:6] == 'tuple(' and args[x][-1] == ')':
            args[x] = tuple(parse_list_elements(args[x][6:-1]))

    return args


def parse_set_elements(string):
    """Takes a string of format 1,2,3,{1,2} and returns the frozenset of those things
    If an element contains {} or <> takes it as a frozenset or a tuple"""

    string = string.replace('{', 'set(')
    string = string.replace('}', ')')
    string = string.replace('<', 'tuple(')
    string = string.replace('>', ')')

    args = separate_arguments(f'({string})')

    for x in range(len(args)):
        # Empty set
        if args[x] == 'set()':
            args[x] = frozenset()
        # Empty tuple
        if args[x] == 'tuple()':
            args[x] = tuple()
        # Set
        elif args[x][:4] == 'set(' and args[x][-1] == ')':
            args[x] = parse_set_elements(args[x][4:-1])
        # Tuple
        elif args[x][:6] == 'tuple(' and args[x][-1] == ')':
            args[x] = tuple(parse_set_elements(args[x][6:-1]))

    args = frozenset(args)

    return args


def unparse_set_solution(solution):

    if type(solution) == frozenset:
        parsed_args = [unparse_set_solution(x) for x in solution]
        parsed_args.sort()
        string = '{' + str(parsed_args)[1:-1] + '}'
        string = string.replace("'", "").replace('"', '')
        return string
    elif type(solution) == tuple:
        parsed_args = [unparse_set_solution(x) for x in solution]
        string = '<' + str(parsed_args)[1:-1] + '>'
        string = string.replace("'", "").replace('"', '')
        return string
    else:
        return solution


def parse_user_solution(string):

    if string == 'set()':
        return frozenset()
    elif string == 'tuple()':
        return tuple()
    elif string[:4] == 'set(' and string[-1] == ')':
        args = separate_arguments(string[3:])
        args = [parse_user_solution(x) for x in args]
        return frozenset(args)
    elif string[:6] == 'tuple(' and string[-1] == ')':
        args = separate_arguments(string[5:])
        args = [parse_user_solution(x) for x in args]
        return tuple(args)
    else:
        return string.replace(" ", "")


# ----------------------------------------------------------------------------------------------------------------------
# PREDICATE LOGIC


def parse_predicate_formula(string, logic, predicate_arity_dict=None):
    """Takes a string an transforms it into a formula of the format defined above
    ¡¡¡This function prepares the formula, the next one parses it!!!
    Returns the parsed formula and the predicate arity dict!"""

    # An empty string returns an error
    if not string:
        ValueError("An empty string is not a well-formed propositional formula")

    # Delete the ifs
    string = string.replace('if ', '')

    # Parse constants (including quantifiers)
    for con in logic.parsed_constants:
        string = string.replace(con, logic.parsed_constants[con])
    string = string.replace("falsum", "⊥")
    string = string.replace("Falsum", "⊥")

    # Remove spaces
    string = string.replace(" ", "")

    # Trick so that binaries do not have to contain external parentheses
    try:
        formula_and_dict = parse_predicate_formula2('(' + string + ')', logic, None, predicate_arity_dict)
        return formula_and_dict
    except ValueError:
        pass

    formula_and_dict = parse_predicate_formula2(string, logic, None, predicate_arity_dict)
    return formula_and_dict


def parse_predicate_formula2(string, logic, bound_variables=None, predicate_arity_dict=None):
    """Parses a FOL string into a list of lists
    Returns the parsed formula and the predicate arity dict"""

    if bound_variables is None:
        bound_variables = list()
    if predicate_arity_dict is None:
        predicate_arity_dict = dict()


    # Falsum
    if string == '⊥':
        return [[string], predicate_arity_dict]

    # Atomics
    if string[0] in FOL_predicates:
        arity = 0
        for char in string[1:]:
            if char in FOL_individual_constants:
                arity += 1
            elif char in FOL_variables:
                if char in bound_variables:
                    arity += 1
                else:
                    raise ValueError(f"Variable {char} is free in {string}")
            else:
                raise ValueError(f"Invalid formula")

        if string[0] not in predicate_arity_dict:
            predicate_arity_dict[string[0]] = arity
        else:
            if predicate_arity_dict[string[0]] != arity:
                raise ValueError("Inconsistent assignment of predicate arity")

        return [[string], predicate_arity_dict]

    # Checks if unary:
    if string[0] in logic.constants(1):
        parse_inside = parse_predicate_formula2(string[1:], logic, bound_variables, predicate_arity_dict)
        formula_inside = parse_inside[0]
        predicate_arity_dict = parse_inside[1]
        return [[string[0], formula_inside], predicate_arity_dict]

    # Checks if binary (starts and ends with parentheses)
    elif string[0] == '(' and string[-1] == ')':
        # Searches for a constant that has 1 more left parenthesis open than right
        num_parentheses_left = 0
        num_parentheses_right = 0

        for x in range(len(string)):
            if string[x] == '(':
                num_parentheses_left += 1
            elif string[x] == ')':
                num_parentheses_right += 1
            elif string[x] in logic.constants(2) and num_parentheses_left == num_parentheses_right + 1:
                result1 = parse_predicate_formula2(string[1:x], logic, bound_variables, predicate_arity_dict)
                formula1 = result1[0]
                predicate_arity_dict = result1[1]
                result2 = parse_predicate_formula2(string[x + 1:-1], logic, bound_variables, predicate_arity_dict)
                formula2 = result2[0]
                predicate_arity_dict = result2[1]
                return [[formula1, string[x], formula2], predicate_arity_dict]

        # If the string starts and ends with parentheses, but did not return at this point, raise an error
        raise ValueError(string + " is not a well-formed propositional formula")

    # Checks if quantifier
    elif string[0] in logic.quantifiers and string[1] in FOL_variables:
        bound_variables.append(string[1])
        parse_inside = parse_predicate_formula2(string[2:], logic, bound_variables, predicate_arity_dict)
        formula_inside = parse_inside[0]
        predicate_arity_dict = parse_inside[1]
        del bound_variables[-1]
        return [[string[0], string[1], formula_inside], predicate_arity_dict]

    # If we did not enter any of the above, then the string is not a formula, and we just return an error
    else:
        raise ValueError("Invalid formula")


def unparse_predicate_formula(formula, logic):
    form1 = deepcopy(formula)
    form1 = unparse_predicate_parentheses(form1, logic)
    form1 = unparse_predicate_rest(form1, logic)
    return form1


def unparse_predicate_parentheses(formula, logic):
    # If atomic
    if len(formula) == 1:
        return formula[0]

    # If unary connective
    elif len(formula) == 2:
        formula[1] = unparse_predicate_parentheses(formula[1], logic)
        # If the next one is atomic (i.e. [¬, p])
        if type(formula[1]) == str:
            return formula
        # If the next one is unary (i.e. [¬, [¬, phi]] )
        elif len(formula[1]) == 2:
            formula = [formula[0], formula[1][0], formula[1][1]]  # Turns it into [¬, ¬, phi]
            return formula
        # If the next one has length 3
        elif len(formula[1]) == 3:
            # If a unary is in the middle [¬ [¬, ¬, phi]]
            if formula[1][1] in logic.constants(1):
                formula[1].insert(0, formula[0])
                formula = formula[1]
                return formula
            # If that does not happen, the next is a binary and should be left as is
            else:
                return formula
        # If no contitional was entered before, then length > 3, eg  [¬, [¬, ¬, ¬, phi]]
        else:
            formula[1].insert(0, formula[0])
            formula = formula[1]
            return formula

    # If the formula is binary
    elif len(formula) == 3 and formula[1] in logic.constants(2):
        formula[0] = unparse_predicate_parentheses(formula[0], logic)
        formula[2] = unparse_predicate_parentheses(formula[2], logic)
        return formula

    # If quantified
    elif len(formula) == 3 and formula[0] in logic.quantifiers:
        formula[2] = unparse_predicate_parentheses(formula[2], logic)
        return formula


def unparse_predicate_rest(formula, logic):
    # If atomic (eg 'Px') or falsum
    if type(formula) == str:
        return formula

    # If binary
    elif len(formula) == 3 and formula[1] in logic.constants(2):
        formula0 = unparse_predicate_rest(formula[0], logic)
        formula2 = unparse_predicate_rest(formula[2], logic)
        unparsed_formula = f"({formula0} {formula[1]} {formula2})"
        return unparsed_formula

    # If quantified
    elif len(formula) == 3 and formula[0] in logic.quantifiers:
        formula_inside = unparse_predicate_rest(formula[2], logic)
        unparsed_formula = f"{formula[0]}{formula[1]} {formula_inside}"
        return unparsed_formula

    # If not atomic or binary or quantified, it is some chain of unaries [¬, ¬, .., phi]
    else:
        last_formula = unparse_predicate_rest(formula[-1], logic)
        formula = formula[:-1]  # Remove unparsed Phi
        formula.append(last_formula)  # Add parsed Phi
        unparsed_formula = str(formula)
        unparsed_formula = unparsed_formula.replace("'", "")
        unparsed_formula = unparsed_formula.replace(",", "")
        for ucon in logic.constants(1):
            # Remove space after unary connectives
            while ucon + " " in unparsed_formula:
                unparsed_formula = unparsed_formula.replace(ucon + " ", ucon)
        return unparsed_formula[1:-1]  # This is to remove the []


def parse_own_model(string, unparsed_formula, logic_name):
    string_list = string.split('\n')

    if string_list[0].replace(" ", "") != "M=<D,I>":
        raise ValueError("First line must be 'M = <D, I>'")

    if len(string_list) == 1:
        raise ValueError("Please enter a domain")

    if string_list[1].replace(" ", "")[:3] != "D={" or string_list[1][-1] != '}':
        raise ValueError("Second line must have form 'D = {...}'")

    if string_list[1].replace(" ", "") == "D={}":
        raise ValueError("Domain cannot be empty")

    domain_string = string_list[1].replace(" ", "")[3:-1]
    if '{' in domain_string or '}' in domain_string or '<' in domain_string or '>' in domain_string:
        raise ValueError("Domain cannot contain sets or tuples")

    if len(string_list) == 2:
        raise ValueError("You must enter interpretations for the individual constants and predicates")

    model = dict()
    model['Domain'] = domain_string.split(",")

    for line in string_list[2:]:
        line2 = line.replace(" ", "")
        if line2[:2] != 'I(' or line[3] != ')':
            raise ValueError(f"Error in line {string_list.index(line)+1}: All lines must begin with I(...)")

        term = line2[2]

        # CONSTANTS
        if term in FOL_individual_constants:
            if line2[4] != "=":
                raise ValueError(f"Error in line {string_list.index(line)+1}: "
                                 f"Individual constant lines must begin with I(...) =")

            denotation = line2[5:]
            if denotation not in model["Domain"]:
                raise ValueError(f"Error in line {string_list.index(line)+1}: "
                                 f"{denotation} does not belong to the specified domain")

            model[term] = denotation

        # PREDICATES
        elif term in FOL_predicates:
            if line2[4] != "+" and line2[4] != "-":
                raise ValueError(f"Error in line {string_list.index(line)+1}: "
                                 f"Predicate lines must begin with I(...)+ = or I(...)- =")
            sign = line2[4]

            if line2[5] != "=":
                raise ValueError(f"Error in line {string_list.index(line)+1}: "
                                 f"Missing equality sign after I(...)+/-")
            if line2[6] != "{" or line2[-1] != '}':
                raise ValueError(f"Error in line {string_list.index(line)+1}: "
                                 f"Predicate interpretations must be sets")

            if line2[6:] == '{}':
                model[term+sign] = list()
            else:
                elements = line2[7:-1]
                if '{' in elements:
                    raise ValueError(f"Error in line {string_list.index(line)+1}: "
                                     f"Predicate interpretations cannot contain sets, only tuples")

                # Relation
                if '<' in elements:
                    denotation = elements.split('<')[1:]
                    denotation2 = list()
                    for index in range(len(denotation)):
                        tup_elem = denotation[index]
                        tup_elem = '<' + tup_elem
                        if tup_elem[-1] == ',':
                            tup_elem = tup_elem[:-1]
                        if tup_elem[0] != '<' or tup_elem[-1] != '>':
                            raise ValueError(f"Error in line {string_list.index(line)+1}: "
                                             f"Elements of a relation must begin and end with <,>")
                        tup_elem = tuple(tup_elem[1:-1].split(','))

                        for elem in tup_elem:
                            if elem not in model["Domain"]:
                                raise ValueError(
                                    f"Error in line {string_list.index(line)+1}: "
                                    f"{elem} does not belong to the specified domain")

                        denotation2.append(tup_elem)
                        model[term+sign] = list(set(denotation2))

                # Property
                else:
                    denotation = elements.split(',')
                    for index in range(len(denotation)):
                        if denotation[index] not in model["Domain"]:
                            raise ValueError(
                                f"Error in line {string_list.index(line)+1}: "
                                f"{denotation[index]} does not belong to the specified domain")
                    model[term+sign] = list(set(denotation))

        else:
            raise ValueError(f"Error in line {string_list.index(line)+1}: "
                             f"{term} is not a valid term, please see below")

    # Check that all the constants and predicates that are named in the formula appear in the model
    # And that every predicate has the correct arity
    constants_in_formula = [x for x in unparsed_formula if x in FOL_individual_constants]
    for c in constants_in_formula:
        if c not in model:
            raise ValueError(f"Constant {c} appears in the formulae but is not assigned a denotation in the model")

    predicates_in_formula = [x for x in unparsed_formula if x in FOL_predicates]
    for p in predicates_in_formula:
        arity = 0
        for index in range(len(unparsed_formula)):
            if unparsed_formula[index] == p:
                for index2 in range(index+1, len(unparsed_formula)):
                    if unparsed_formula[index2] in FOL_individual_constants \
                            or unparsed_formula[index2] in FOL_variables:
                        arity += 1
                    else:
                        break
                break

        if p+"+" not in model or p+"-" not in model:
            raise ValueError(f"Predicate {p} appears in the formulae but is not assigned an extension or anti-extension"
                             f" in the model")
        for sign in ("+", "-"):
            for elem in model[p+sign]:
                if arity == 1:
                    if type(elem) != str:
                        raise ValueError(f"Predicate {p} is unary but tuples were given as its interpretation")
                if arity > 1:
                    if type(elem) != tuple:
                        raise ValueError(f"Predicate {p} is a relation but tuples were not given as its interpretation")
                    if len(elem) != arity:
                        raise ValueError(f"Predicate {p} must be a {arity}-ary relation")

    # And that every element in the domain is the denotation of one (and only one) ind constant
    for elem in model['Domain']:
        present = False
        repeated = False
        for term in model:
            if term in FOL_individual_constants:
                if model[term] == elem:
                    if present:
                        repeated = True
                    present = True
        if not present:
            raise ValueError(f"Element {elem} does not have a constant naming it")
        if repeated:
            raise ValueError(f"Element {elem} has more than one constant naming it")

    # And that every predicate has an assigned extension and anti-extension
    for term in model:
        if term[:-1] in FOL_predicates:
            pred = term[:-1]
            if pred + "+" not in model or pred + "-" not in model:
                raise ValueError(f"Predicate {pred} does not have either an extension or anti-extension assigned")

    # Checks that restrictions on predicate extension and anti-extension are satisfied
    try:
        check_model(model, logic_name)
    except ValueError as e:
        raise ValueError(str(e))

    return model


def check_model(model, logic_name):
    """Checks that the restrictions of each logic for models are satisfied"""

    predicates_checked = list()

    for x in model:
        if x[:-1] in FOL_predicates:
            pred = x[:-1]

            if pred not in predicates_checked:
                if (logic_name == 'K3' or logic_name == 'Ł3' or logic_name == 'FDE') and model[pred+"+"] == list() \
                        and model[pred+"-"] == list():
                    pass

                else:
                    if model[pred + "+"] != list():
                        if type(model[pred + "+"][0]) == str:
                            arity = 1
                        else:
                            arity = len(model[pred + "+"][0])
                    else:
                        if model[pred + "-"] == list():
                            raise ValueError(f"Predicate {pred} has empty extension and antiextension"
                                             f" (not allowed in {logic_name} logic)")
                        if type(model[pred + "-"][0]) == str:
                            arity = 1
                        else:
                            arity = len(model[pred + "-"][0])

                    if arity == 1:
                        all_tuples = model["Domain"]
                    elif arity > 1:
                        all_tuples = list(product(model["Domain"], repeat=arity))

                    extension = set(model[pred + "+"])
                    anti_extension = set(model[pred + "-"])

                    if logic_name == "Classical" or logic_name == "K3" or logic_name == 'Ł3':
                        if extension & anti_extension:
                            raise ValueError(f"Intersection between extension and anti-extension is not empty"
                                             f" for predicate {pred} (not valid in {logic_name} logic)")
                    if logic_name in ("Classical", "LP", "RM3", "LFI1"):
                        if extension | anti_extension != all_tuples:
                            raise ValueError(f"Some element does not belong to either the extension or anti extension"
                                             f" of predicate {pred} (not valid in {logic_name} logic)")

            predicates_checked.append(pred)


def unparse_model(model):
    model_string = "M = <D, I>\n"
    dom = str(model["Domain"]).replace("'", "").replace('"', '').replace("[", "{").replace("]", "}")
    model_string += f"D = {dom}\n"
    model_cts = sorted([x for x in model if x in FOL_individual_constants])
    for x in model_cts:
        denotation = model[x].replace("'", "").replace('"', '')
        model_string += f"I({x}) = {denotation}\n"
    model_predicates = [x[0] for x in model if x[0] in FOL_predicates]
    model_predicates = sorted(list(set(model_predicates)))
    for x in model_predicates:
        extension = str(model[x + "+"]).replace("'", "").replace('"', '').replace("[", "{").replace("]", "}")
        extension = extension.replace("(", "<").replace(")", ">")
        antiextension = str(model[x + "-"]).replace("'", "").replace('"', '').replace("[", "{").replace("]", "}")
        antiextension = antiextension.replace("(", "<").replace(")", ">")
        model_string += f"I({x})+ = {extension}\n"
        model_string += f"I({x})- = {antiextension}\n"
    return model_string[:-1]


# ----------------------------------------------------------------------------------------------------------------------
# OTHER FUNCTIONS CALLED IN THE HTMLS


def parse_custom_constants(string):
    if string == '':
        return list()
    string = '(' + string + ')'
    args = separate_arguments(string)
    for arg in args:
        if len(arg) != 1:
            raise ValueError('Truth values and logical constant symbols must be one character long')
        if arg in reserved_terms:
            raise ValueError(f'{arg} is a reserved term')
        if args.count(arg) > 1:
            raise ValueError("Repeated symbol")
    return args


def parse_on_steps(string):
    args = separate_arguments('(' + string + ')')
    args = sorted(list({int(x) for x in args}))  # Made a set to eliminate repeated steps first
    return args


def parse_valuation_line(string, logic):
    """Input must be a string of format 'v(unp_formula) = value', returns [formula, value]"""
    string = string.replace(" ", "")
    if string[:2] != 'v(' or ')' not in string or '=' not in string or string[-1] == '=':
        raise ValueError
    value = string[string.index('=')+1:]
    if value not in logic.values:
        raise ValueError
    unp_formula = string[2:string.rfind(')')]
    formula = parse_propositional(unp_formula, logic)
    return [formula, value]


def parse_valuation_line2(string, logic):
    """Input must be a string of format 'v(unp_formula) = value', returns [formula, value]"""
    string = string.replace(" ", "")
    if string[:2] != 'v(' or ')' not in string or '=' not in string or string[-1] == '=':
        raise ValueError
    value = string[string.index('=')+1:]
    if value not in logic.values:
        raise ValueError
    unp_formula = string[2:string.rfind(')')]
    formula = parse_predicate_formula(unp_formula, logic)[0]
    return [formula, value]


# ----------------------------------------------------------------------------------------------------------------------
# AUXILIARY FUNCTIONS


def separate_arguments(string):
    """Given a string in forrmat '(x,y,z...)' returns a list with format ['x', 'y', 'z', ...]"""

    # If the string is in incorrect format, raises an error
    if string[0] != '(' or string[-1] != ')':
        raise ValueError('Incorrect format for separate_arguments function (missing initial or final parentheses)')

    # If given a single argument '(x)', returns ['x']
    elif ',' not in string:
        return [string[1:-1]]

    else:
        num_parentheses_left = 0
        num_parentheses_right = 0
        comma_indexes = [0]
        argum_list = list()

        for x in range(0, len(string)):
            if string[x] == '(':
                num_parentheses_left += 1
            elif string[x] == ')':
                num_parentheses_right += 1
            elif string[x] == ',':
                if num_parentheses_left == num_parentheses_right + 1:
                    argum_list.append(string[comma_indexes[-1] + 1:x])
                    comma_indexes.append(x)
        argum_list.append(string[comma_indexes[-1] + 1:-1])
        return argum_list
