try:
    from utils_formula_parser import separate_arguments
except ModuleNotFoundError:
    from exercises.templates.exercises.utils_formula_parser import separate_arguments


def solve_set_operation(sets, operation):

    if operation[0] == '℘':
        operation_inside = operation[2:-1]
        denotation_inside = solve_set_operation(sets, operation_inside)
        powerset = [[]]
        for elem in denotation_inside:
            powerset.extend([x + [elem] for x in powerset])
        denot1 = []
        for x in powerset:
            denot1.append(frozenset(x))
        denot = frozenset(denot1)
        return denot

    elif operation[0] == '∪':
        operations_inside = separate_arguments(operation[1:])
        denotations_inside = [solve_set_operation(sets, x) for x in operations_inside]
        return frozenset(denotations_inside[0] | denotations_inside[1])

    elif operation[0] == '∩':
        operations_inside = separate_arguments(operation[1:])
        denotations_inside = [solve_set_operation(sets, x) for x in operations_inside]
        return frozenset(denotations_inside[0] & denotations_inside[1])

    elif operation[0] == '−':
        operations_inside = separate_arguments(operation[1:])
        denotations_inside = [solve_set_operation(sets, x) for x in operations_inside]
        return frozenset(denotations_inside[0] - denotations_inside[1])

    elif operation[0] == '×':
        operations_inside = separate_arguments(operation[1:])
        denotations_inside = [solve_set_operation(sets, x) for x in operations_inside]
        prod = [(x, y) for x in denotations_inside[0] for y in denotations_inside[1]]
        return frozenset(prod)

    else:
        return sets[operation[0]]
