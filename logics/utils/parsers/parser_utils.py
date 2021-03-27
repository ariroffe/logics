from logics.classes.exceptions import NotWellFormed


def separate_arguments(string, comma_separator):
    """
    Given a string in forrmat '(x,y,z...)' returns a list with format ['x', 'y', 'z', ...]
    Takes into account nested parentheses. For instance, '(1,(2,3),4)' will return ['1', '(2,3)', '4']
    WILL NOT ELIMINATE WHITESPACES, if you give it '(1, 2, 3)' it will return ['1', ' 2', ' 3']
    """
    # If the string is in incorrect format, raises an error
    if string[0] != '(' or string[-1] != ')':
        raise NotWellFormed(f"'{string}' missing initial or final parentheses")

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
            elif string[x] == comma_separator:
                if num_parentheses_left == num_parentheses_right + 1:
                    argum_list.append(string[comma_indexes[-1] + 1:x])
                    comma_indexes.append(x)
        argum_list.append(string[comma_indexes[-1] + 1:-1])  # the last argument
        return argum_list


def get_main_constant(string, infix_cts, outer_parentheses=True):
    """
    Searches for a constant that has 1 more left parenthesis open than right
    (or the same amount if outer_parentheses is set to False)
    Returns the constant and its index in the string
    If it does not find one, returns None
    If it finds more than one, raises NotWellFormed
    """
    num_parentheses_left = 0
    num_parentheses_right = 0

    ct_present = False
    binary_ct = None
    binary_ct_index = None
    for x in range(len(string)):
        if string[x] == '(':
            num_parentheses_left += 1
        elif string[x] == ')':
            num_parentheses_right += 1
        else:
            for infix_ct in infix_cts:
                if string[x:x+len(infix_ct)] == infix_ct:
                    if (outer_parentheses and num_parentheses_left == num_parentheses_right + 1) or \
                            (not outer_parentheses and num_parentheses_left == num_parentheses_right):
                        # Do this instead of returning immediately to avoid things like (p v q v r)
                        if ct_present:
                            raise NotWellFormed(f"{string} contains more than one top-level binary operator")
                        binary_ct = infix_ct
                        binary_ct_index = x
                        ct_present = True

    return binary_ct, binary_ct_index


def get_last_opening_parenthesis(string):
    """
    Returns index of the the parenthesis that opens the last closing parenthesis
    For example, in "∀x ∈ f(x) (Px v (Qx v Rx))" will return the index of the parenthesis before Px
    """
    num_parentheses_left = 0
    num_parentheses_right = 0

    for char_index in range(len(string)-1, -1, -1):
        if string[char_index] == '(':
            num_parentheses_left += 1
            if num_parentheses_left == num_parentheses_right:
                return char_index
        elif string[char_index] == ')':
            num_parentheses_right += 1


def get_closing_parenthesis(string):
    """
    Given a string that starts with a parenthesis, e.g. (1+1)v0=0
    returns the index of the closing parenthesis of the initial parenthesis
    """
    num_parentheses_left = 0
    num_parentheses_right = 0
    for char_index in range(len(string)):
        if string[char_index] == '(':
            num_parentheses_left += 1
        elif string[char_index] == ')':
            num_parentheses_right += 1
            if num_parentheses_right == num_parentheses_left:
                return char_index


# ----------------------------------------------------------------------------------------------------------------------
# Standard Godel encoding and decoding

def godel_encode(string):
    """Godel encoding function for the language logics.instances.predicate.languages.arithmetic_truth_language

    Codes an *unparsed sentence* (the string you would give to the parser). Works as follows:

    * Constant ``"0"`` is represented by 0
    * Auxiliary symbols begin with 1 (e.g. ``"("`` is 19, ``")"`` is 199)
    * Connectives begin with 2 (e.g. ``"~"`` is 29, ``"∧"`` is 299, ``"∨"`` is 2999)
    * Quantifiers begin with 3 (e.g. ``"∀"`` is 39, ``"∃"`` is 399)
    * Predicates begin with 4 (e.g. ``"="`` is 49, ``"Tr"`` is 49999)
    * Variables with 5, Predicate variables with 6 (e.g. ``"x"`` is 51, ``"x1"`` is 519, ``"X"`` is 61)
    * Metavariables and sentential constants begin with 7 (e.g. ``"A"`` is 79, ``"λ"`` is 79999)
    * Function symbols begin with 8 (e.g. ``"s"`` is 89, ``"+"`` is 899)

    Returns
    -------
    str
        The *numeral* representing the Godel number of the sentence

    Raises
    ------
    logics.classes.exceptions.NotWellFormed
        If it detects a character that is none of the above. Note that whitespace is taken as non-recognized.

    Examples
    --------
    >>> from logics.utils.parsers.parser_utils import godel_encode
    >>> godel_encode('0=0')
    '0490'
    >>> godel_encode('0 = 0')
    Traceback (most recent call last):
    ...
    logics.classes.exceptions.NotWellFormed: Non-recognized character   in Godel encoding
    >>> godel_encode('s(0)+s(0)=s(s(0))')
    '891901998998919019949891989190199199'
    >>> godel_encode('1+1=2')  # Remember that arithmetic has only 0 as individual constant
    Traceback (most recent call last):
    ...
    logics.classes.exceptions.NotWellFormed: Non-recognized character 1 in Godel encoding
    >>> godel_encode('∀x(~0=0)')
    '395119290490199'
    >>> godel_encode('forall x (0=0)')
    Traceback (most recent call last):
    ...
    logics.classes.exceptions.NotWellFormed: Non-recognized character f in Godel encoding

    Notes
    -----
    You will probably not need to call this function directly, the parser will call it for you, see below.
    """
    new_string = ''
    current_index = 0
    skip_characters = 0
    for char in string:
        if skip_characters != 0:
            skip_characters -= 1
        else:
            # Constant 0 is represented by 0
            if char == '0':
                new_string += '0'

            # Auxiliary symbols begin with 1
            elif char == '(':
                new_string += '19'
            elif char == ')':
                new_string += '199'
            elif char == ',':
                new_string += '1999'

            # Connectives begin with 2
            elif char == '~':
                new_string += '29'
            elif char == '∧':
                new_string += '299'
            elif char == '∨':
                new_string += '2999'
            elif char == '→':
                new_string += '29999'
            elif char == '↔':
                new_string += '299999'

            # Quantifiers begin with 3
            elif char == '∀':
                new_string += '39'
            elif char == '∃':
                new_string += '399'
            elif char == '∈':
                new_string += '3999'

            # Predicates 4
            elif char == '=':
                new_string += '49'
            elif char == '>':
                new_string += '499'
            elif char == '<':
                new_string += '4999'
            elif char == 'T' and string[current_index+1 == 'r']:
                new_string += '49999'
                skip_characters += 1

            # Variables 5, Predicate variables 6
            elif char == 'x' or char == 'y' or char == 'z' or char == 'X' or char == 'Y' or char == 'Z':
                # begin with x 51
                if char == 'x':
                    new_string += '51'
                # begin with y 52
                elif char == 'y':
                    new_string += '52'
                # begin with z 53
                elif char == 'z':
                    new_string += '53'
                # begin with X 61
                elif char == 'X':
                    new_string += '61'
                # begin with Y 62
                elif char == 'Y':
                    new_string += '62'
                # begin with Z 63
                elif char == 'Z':
                    new_string += '63'
                var_number = 0
                for char2_index in range(current_index + 1, len(string)):
                    if string[char2_index].isdigit():
                        var_number = int(string[current_index+1:char2_index+1])
                        skip_characters += 1
                    else:
                        break
                if var_number != 0:
                    new_string += '9' * var_number

            # Metavariables and sentential constants 7
            elif char == 'A':
                new_string += '79'
            elif char == 'B':
                new_string += '799'
            elif char == 'C':
                new_string += '7999'
            elif char == 'λ':
                new_string += '79999'

            # Function symbols 8
            elif char == 's':
                new_string += '89'
            elif char == '+':
                new_string += '899'
            elif char == '*' and string[current_index + 1] != '*':
                new_string += '8999'
            elif char == '*' and string[current_index + 1] == '*':
                new_string += '89999'
                skip_characters += 1
            elif char == 'q' and string[current_index:current_index + 5] == 'quote':
                new_string += '899999'
                skip_characters += 4

            else:
                raise NotWellFormed(f'Non-recognized character {char} in Godel encoding')

        current_index += 1

    return new_string


def godel_decode(string):
    """Godel decoding function for the language logics.instances.predicate.languages.arithmetic_truth_language

    Reverses the function above.

    Examples
    --------
    >>> from logics.utils.parsers.parser_utils import godel_decode
    >>> godel_decode('0490')
    '0=0'
    >>> godel_decode('891901998998919019949891989190199199')
    's(0)+s(0)=s(s(0))'
    >>> godel_decode('395119290490199')
    '∀x(~0=0)'
    """
    new_string = ''
    current_index = 0
    skip_characters = 0
    for char in string:
        if skip_characters != 0:
            skip_characters -= 1
        else:
            # Individual constant 0
            if char == '0':
                new_string += '0'

            # Auxiliary symbols 1
            elif char == '1':
                if string[current_index:current_index + 4] == '1999':
                    new_string += ','
                    skip_characters += 3
                elif string[current_index:current_index + 3] == '199':
                    new_string += ')'
                    skip_characters += 2
                elif string[current_index:current_index + 2] == '19':
                    new_string += '('
                    skip_characters += 1
                else:
                    raise NotWellFormed(f'Incorrect Godel encoding')

            # Connectives 2
            elif char == '2':
                if string[current_index:current_index + 6] == '299999':
                    new_string += '↔'
                    skip_characters += 5
                elif string[current_index:current_index + 5] == '29999':
                    new_string += '→'
                    skip_characters += 4
                elif string[current_index:current_index + 4] == '2999':
                    new_string += '∨'
                    skip_characters += 3
                elif string[current_index:current_index + 3] == '299':
                    new_string += '∧'
                    skip_characters += 2
                elif string[current_index:current_index + 2] == '29':
                    new_string += '~'
                    skip_characters += 1
                else:
                    raise NotWellFormed(f'Incorrect Godel encoding')

            # Quantifiers 3
            elif char == '3':
                if string[current_index:current_index + 4] == '3999':
                    new_string += '∈'
                    skip_characters += 3
                elif string[current_index:current_index + 3] == '399':
                    new_string += '∃'
                    skip_characters += 2
                elif string[current_index:current_index + 2] == '39':
                    new_string += '∀'
                    skip_characters += 1
                else:
                    raise NotWellFormed(f'Incorrect Godel encoding')

            # Predicates 4
            elif char == '4':
                if string[current_index:current_index + 5] == '49999':
                    new_string += 'Tr'
                    skip_characters += 4
                elif string[current_index:current_index + 4] == '4999':
                    new_string += '<'
                    skip_characters += 3
                elif string[current_index:current_index + 3] == '499':
                    new_string += '>'
                    skip_characters += 2
                elif string[current_index:current_index + 2] == '49':
                    new_string += '='
                    skip_characters += 1
                else:
                    raise NotWellFormed(f'Incorrect Godel encoding')

            # Variables 5 and 6
            elif char == '5' or char == '6':
                if string[current_index:current_index + 2] == '51':
                    new_string += 'x'
                elif string[current_index:current_index + 2] == '52':
                    new_string += 'y'
                elif string[current_index:current_index + 2] == '53':
                    new_string += 'z'
                elif string[current_index:current_index + 2] == '61':
                    new_string += 'X'
                elif string[current_index:current_index + 2] == '62':
                    new_string += 'Y'
                elif string[current_index:current_index + 2] == '63':
                    new_string += 'Z'
                skip_characters += 1
                var_number = 0
                for char2_index in range(current_index + 2, len(string)):
                    if string[char2_index] == '9':
                        var_number += 1
                        skip_characters += 1
                    else:
                        break
                if var_number != 0:
                    new_string += str(var_number)

            # Metavariables 7
            elif char == '7':
                if string[current_index:current_index + 5] == '79999':
                    new_string += 'λ'
                    skip_characters += 4
                elif string[current_index:current_index + 4] == '7999':
                    new_string += 'C'
                    skip_characters += 3
                elif string[current_index:current_index + 3] == '799':
                    new_string += 'B'
                    skip_characters += 2
                elif string[current_index:current_index + 2] == '79':
                    new_string += 'A'
                    skip_characters += 1
                else:
                    raise NotWellFormed(f'Incorrect Godel encoding')

            # Function symbols 8
            elif char == '8':
                if string[current_index:current_index + 6] == '899999':
                    new_string += 'quote'
                    skip_characters += 5
                elif string[current_index:current_index + 5] == '89999':
                    new_string += '**'
                    skip_characters += 4
                elif string[current_index:current_index + 4] == '8999':
                    new_string += '*'
                    skip_characters += 3
                elif string[current_index:current_index + 3] == '899':
                    new_string += '+'
                    skip_characters += 2
                elif string[current_index:current_index + 2] == '89':
                    new_string += 's'
                    skip_characters += 1
                else:
                    raise NotWellFormed(f'Incorrect Godel encoding')

            else:
                raise NotWellFormed(f'Non-recognized character {char} in Godel encoding')

        current_index += 1

    return new_string
