def validate_input(n, p, C):
    """
    Validates that the input provided is in the correct form
    :param n: zero or positive integer (to be correct)
    :param p: positive integer (to be correct)
    :param C: dict, keys: positive integers, values: sets of strings (to be correct)
    :return: None. Raises an exception if the parameters are in incorect format
    """
    if type(n) != int or n < 0:
        raise ValueError("Profundity must be a natural number")

    if type(p) != int or p < 1:
        raise ValueError("Number of atomics must be a positive integer")

    if type(C) != dict or C == {}:
        raise ValueError("C must be a non-empty dict")
    constants = list()
    for key in C:
        if type(key) != int or key < 1 or type(C[key]) != set:
            raise ValueError("Keys of C must be positive integers, and values must be sets")
        for value in C[key]:
            if type(value) != str:
                raise ValueError("Logical constants must be given as strings")
            else:
                if value in constants:
                    raise ValueError("Repeated constant name")
                else:
                    constants.append(value)


def validate_input2(n, P, C):
    """
    Validates that the input provided is in the correct form
    :param n: zero or positive integer (to be correct)
    :param P: set of strings (to be correct)
    :param C: dict, keys: positive integers, values: sets of strings (to be correct)
    :return: None. Raises an exception if the parameters are in incorect format
    """
    if type(n) != int or n < 0:
        raise ValueError("Profundity must be a natural number")

    if type(P) != set or P == set():
        raise ValueError("P must be a non-empty set of propositional letters")
    for p in P:
        if type(p) != str:
            raise ValueError("Propositional letters must be given as strings")

    if type(C) != dict or C == {}:
        raise ValueError("C must be a non-empty dict")
    constants = list()
    for key in C:
        if type(key) != int or key < 1 or type(C[key]) != set:
            raise ValueError("Keys of C must be positive integers, and values must be sets")
        for value in C[key]:
            if type(value) != str:
                raise ValueError("Logical constants must be given as strings")
            else:
                if value in constants:
                    raise ValueError("Repeated constant name")
                else:
                    constants.append(value)
