try:
    from utils_formula_parser import atomics, parse_propositional
except ModuleNotFoundError:
    from exercises.templates.exercises.utils_formula_parser import atomics, parse_propositional


def get_columns(unparsed_formula, logic):
    """Separates an unparsed formula into a list of strings that represent the columns"""

    columns = ['']

    for x in unparsed_formula:
        if x == ')':
            columns[-1] += x
        else:
            if columns[-1] == '':
                columns = [x]
            elif columns[-1][-1] == '(':
                columns[-1] += x
            else:
                columns.append(x)

    # Make a dict that says which column (number) corresponds to which subformula
    subformula_dict = dict()
    col_number = 1
    for index in range(len(unparsed_formula)):

        char = unparsed_formula[index]

        # Atomic
        if char in atomics:
            subformula_dict[col_number] = [char]
            col_number += 1

        # Unary connective
        if char in logic.constants(1):
            reach = get_right_reach(unparsed_formula[index + 1:], logic)
            formula = parse_propositional(char + reach, logic)
            subformula_dict[col_number] = formula
            col_number += 1

        # Binary connective
        if char in logic.constants(2):
            left_reach = get_left_reach(unparsed_formula[:index], logic)
            right_reach = get_right_reach(unparsed_formula[index + 1:], logic)
            unp_formula = left_reach + char + right_reach
            formula = parse_propositional(unp_formula, logic)
            subformula_dict[col_number] = formula
            col_number += 1

    return [columns, subformula_dict]


def get_right_reach(string, logic):

    # The next character is an atomic
    if string[0] in atomics:
        return string[0]

    reach = ''
    # The next character is a unary connective
    if string[0] in logic.constants(1):
        reach += string[0]
        reach += get_right_reach(string[1:], logic)
        return reach

    # The next character is a parenthesis
    if string[0] == '(':
        # Look for the closing parenthesis
        open_left = 0
        closing_right = 0
        for index2 in range(len(string)):
            char2 = string[index2]
            if char2 == '(':
                open_left += 1
            if char2 == ')':
                closing_right += 1
                if open_left == closing_right:
                    return string[:index2 + 1]


def get_left_reach(string, logic):

    # The previous character is an atomic
    if string[-1] in atomics:
        reach = string[-1]
        # Look for unary connectives behind it. If you find a left parenthesis, stop
        for index2 in range(len(string) - 1, -1, -1):
            char2 = string[index2]
            if char2 in logic.constants(1):
                reach = char2 + reach
            if char2 == '(':
                break
        return reach

    # The previous character is a parenthesis
    if string[-1] == ')':
        # Look for the opening parenthesis
        open_right = 0
        closing_left = 0
        for index2 in range(len(string) - 1 , -1, -1):
            char2 = string[index2]
            if char2 == ')':
                open_right += 1
            if char2 == '(':
                closing_left += 1
                if open_right == closing_left:
                    # Look for unary connectives behind it
                    while True:
                        if index2 == 0:
                            return string[index2:]
                        else:
                            prev_char = string[index2 - 1]
                            if prev_char not in logic.constants(1):
                                return string[index2:]
                            else:
                                index2 -= 1


def get_rows(unparsed_formula, logic):
    formula_atomics = {x for x in unparsed_formula if x in atomics}

    return len(logic.values) ** len(formula_atomics)


def get_argument_rows(unparsed_premises, unparsed_conclusion, logic):
    argument_atomics = set()
    for p in unparsed_premises:
        argument_atomics = argument_atomics | {x for x in p if x in atomics}
    argument_atomics = argument_atomics | {x for x in unparsed_conclusion if x in atomics}

    return len(logic.values) ** len(argument_atomics)


def get_argument_columns(unparsed_premises, unparsed_conclusion, logic):
    """Separates an unparsed argument into a list of strings that represent the columns"""

    for x in range(len(unparsed_premises)):
        unparsed_premises[x] = unparsed_premises[x].replace(" ","")
    unparsed_conclusion = unparsed_conclusion.replace(" ", "")

    columns = ['']
    premise_breaks = []

    for prem in unparsed_premises:
        for x in prem:
            if x == ')':
                columns[-1] += x
            else:
                if columns[-1] == '':
                    columns = [x]
                elif columns[-1][-1] == '(':
                    columns[-1] += x
                else:
                    columns.append(x)
        premise_breaks.append(len(columns))
    for x in unparsed_conclusion:
        if x == ')':
            columns[-1] += x
        else:
            if columns[-1] == '':
                columns = [x]
            elif columns[-1][-1] == '(':
                columns[-1] += x
            else:
                columns.append(x)


    # Make a dict that says which column (number) corresponds to which subformula
    subformula_dict = dict()
    col_number = 1
    for prem in unparsed_premises:
        for index in range(len(prem)):

            char = prem[index]

            # Atomic
            if char in atomics:
                subformula_dict[col_number] = [char]
                col_number += 1

            # Unary connective
            if char in logic.constants(1):
                reach = get_right_reach(prem[index + 1:], logic)
                formula = parse_propositional(char + reach, logic)
                subformula_dict[col_number] = formula
                col_number += 1

            # Binary connective
            if char in logic.constants(2):
                left_reach = get_left_reach(prem[:index], logic)
                right_reach = get_right_reach(prem[index + 1:], logic)
                unp_formula = left_reach + char + right_reach
                formula = parse_propositional(unp_formula, logic)
                subformula_dict[col_number] = formula
                col_number += 1

    for index in range(len(unparsed_conclusion)):

        char = unparsed_conclusion[index]

        # Atomic
        if char in atomics:
            subformula_dict[col_number] = [char]
            col_number += 1

        # Unary connective
        if char in logic.constants(1):
            reach = get_right_reach(unparsed_conclusion[index + 1:], logic)
            formula = parse_propositional(char + reach, logic)
            subformula_dict[col_number] = formula
            col_number += 1

        # Binary connective
        if char in logic.constants(2):
            left_reach = get_left_reach(unparsed_conclusion[:index], logic)
            right_reach = get_right_reach(unparsed_conclusion[index + 1:], logic)
            unp_formula = left_reach + char + right_reach
            formula = parse_propositional(unp_formula, logic)
            subformula_dict[col_number] = formula
            col_number += 1

    return [columns, subformula_dict, premise_breaks]