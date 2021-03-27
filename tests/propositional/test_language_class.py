import unittest

from logics.classes.propositional import Language, InfiniteLanguage


class TestLanguageClass(unittest.TestCase):
    def setUp(self):
        at = ['p', 'q', 'r']
        cad = {'~': 1, '*': 1, '&': 2, '^': 2, '#': 3}
        sc = ['⊥', '⊤']
        self.language = Language(atomics=at, constant_arity_dict=cad, sentential_constants=sc)
        self.infinite_language = InfiniteLanguage(atomics=at, constant_arity_dict=cad, sentential_constants=sc)

    def test_constants(self):
        self.assertEqual(self.language.constants(), {'~', '*', '&', '^', '#'})
        self.assertEqual(self.language.constants(1), {'~', '*'})
        self.assertEqual(self.language.constants(2), {'&', '^'})
        self.assertEqual(self.language.constants(3), {'#'})
        self.assertEqual(self.language.constants(4), set())

        self.assertEqual(self.language.arity('~'), 1)
        self.assertEqual(self.language.arity('^'), 2)

    def test_is_atomic_string(self):
        self.assertTrue(self.language.is_atomic_string('p'))
        self.assertFalse(self.language.is_atomic_string('h'))
        self.assertFalse(self.language.is_atomic_string('⊥'))
        self.assertFalse(self.language.is_atomic_string('p1'))
        self.assertTrue(self.infinite_language.is_atomic_string('p1'))

    def test_sentential_constants(self):
        self.assertTrue(self.language.is_sentential_constant_string('⊥'))
        self.assertFalse(self.language.is_sentential_constant_string('⊥⊥'))
        self.assertFalse(self.language.is_sentential_constant_string('p'))

    # Tests for is_well_formed are in test_formula_class


if __name__ == '__main__':
    unittest.main()
