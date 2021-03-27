from logics.classes.predicate.semantics import Model


class ArithmeticModel(Model):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.fixed_denotations.update({
            '0': 0,
            's': lambda x: x + 1,
            '+': lambda x, y: x + y,
            '*': lambda x, y: x * y,
            '**': lambda x, y: x ** y,
            '=': lambda x, y: '1' if x == y else '0',
            '>': lambda x, y: '1' if x > y else '0',
            '<': lambda x, y: '1' if x < y else '0',
        })


class RealNumberArithmeticModel(Model):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.fixed_denotations.update({
            '+': lambda x, y: x + y,
            '-': lambda x, y: x - y,
            '*': lambda x, y: x * y,
            '/': lambda x, y: x / y,
            '//': lambda x, y: x // y,
            '**': lambda x, y: x ** y,
            '=': lambda x, y: '1' if x == y else '0',
            '>': lambda x, y: '1' if x > y else '0',
            '<': lambda x, y: '1' if x < y else '0',
        })

    def denotation(self, term, free_variable_denotation_dict=None):
        """In real number arithmetic have every numeral as constant"""
        if type(term) == str:
            try:
                num = int(term)
                return num
            except ValueError:
                try:
                    num = float(term)
                    return num
                except ValueError:
                    pass
        return super().denotation(term, free_variable_denotation_dict)
