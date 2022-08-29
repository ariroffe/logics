import unittest
import warnings

from logics.classes.propositional import Formula, Inference
from logics.instances.propositional.languages import classical_language_with_sent_constants as language
from logics.classes.exceptions import IncorrectLevels, LevelsWarning


class TestInferenceClass(unittest.TestCase):
    def setUp(self):
        self.p = Formula(['p'])
        self.q = Formula(['q'])
        self.pthenq = Formula(['→', self.p, self.q])
        self.pthenp = Formula(['→', self.p, self.p])
        self.qthenp = Formula(['→', self.q, self.p])
        # The names of the variables use _ for comma, __ for /, ___ for ///, and so on
        self.p__p = Inference([self.p], [self.p])  # p / p
        self.p__q = Inference([self.p], [self.q])  # p / q
        self.p_pthenq__q = Inference([self.p, self.pthenq], [self.q])  # p, p → q / q
        self.p__q___p_pthenq__q = Inference([self.p__q], [self.p_pthenq__q])  # metainference p / q // p, p → q / q
        self.empty_inference = Inference([], [])
        self.empty_metainference = Inference([], [], level=2)

    def test_level(self):
        self.assertEqual(self.p__p.level, 1)
        self.assertEqual(self.p_pthenq__q.level, 1)
        self.assertEqual(self.p__q___p_pthenq__q.level, 2)
        self.assertEqual(self.empty_inference.level, 1)
        self.assertEqual(self.empty_metainference.level, 2)
        m3 = Inference([self.empty_metainference], [])
        self.assertEqual(m3.level, 3)

        i4 = Inference([self.empty_inference], [self.empty_inference])
        self.assertEqual(i4.level, 2)

        # Attempting to build an inference with a premise of level 1 and a conclusion of level 2 should raise exception
        with warnings.catch_warnings(record=True) as w:
            i = Inference([self.p__p], [self.p__q___p_pthenq__q])
            self.assertEqual(i.level, 3)
            self.assertEqual(len(w), 1)
            assert issubclass(w[-1].category, LevelsWarning)
        # Same with a formula and an inference of level 1
        with warnings.catch_warnings(record=True) as w:
            i = Inference([self.p], [self.p__p])
            self.assertEqual(i.level, 2)
            self.assertEqual(len(w), 1)
            assert issubclass(w[-1].category, LevelsWarning)
        # The autodetected level does not coincide with the declared level
        self.assertRaises(IncorrectLevels, Inference, [self.p], [self.p], level=2)

    def test_atomics_inside(self):
        self.assertEqual(self.p__p.atomics_inside(language), {'p'})
        self.assertEqual(self.p__q.atomics_inside(language), {'p', 'q'})
        self.assertEqual(self.p_pthenq__q.atomics_inside(language), {'p', 'q'})
        self.assertEqual(self.p__q___p_pthenq__q.atomics_inside(language), {'p', 'q'})

        self.assertFalse(self.p__p.is_schematic(language))
        self.assertTrue(Inference([Formula(['A'])], [Formula(['p'])]).is_schematic(language))

    def test_subformulae(self):
        self.assertEqual(self.empty_inference.subformulae, [])
        self.assertEqual(self.empty_metainference.subformulae, [])
        self.assertEqual(self.p__q.subformulae, [self.p, self.q])
        self.assertEqual(self.p__p.subformulae, [self.p])  # There should not be repetitions
        self.assertEqual(self.p_pthenq__q.subformulae, [self.p, self.q, self.pthenq])
        self.assertEqual(Inference([self.p__p], [self.p__p]).subformulae, [self.p])

    def test_substitute(self):
        # Substitute subformulae inside inferences
        self.assertEqual(self.p__p.substitute(self.p, self.q), Inference([self.q], [self.q]))
        self.assertEqual(self.p_pthenq__q.substitute(self.q, self.p), Inference([self.p, self.pthenp], [self.p]))
        self.assertEqual(self.p_pthenq__q.substitute(self.pthenq, self.qthenp),
                         Inference([self.p, self.qthenp], [self.q]))

        # Substitute inferences inside inferences
        self.assertEqual(self.p__p.substitute(self.p__p, self.p__p), self.p__p)  # p / p for itself in p / p
        self.assertEqual(self.p__p.substitute(self.p__p, self.p__q), self.p__q)  # p / p for for p / q in p / p
        self.assertEqual(self.p__q___p_pthenq__q.substitute(self.p__q, self.p__p),
                         Inference([self.p__p], [self.p_pthenq__q]))  # p / q for for p / p in p / q // p, p → q / q

    def test_is_instance_of(self):
        A = Formula(['A'])
        B = Formula(['B'])
        AthenB = Formula(['→', A, B])

        # Inferences
        self.assertTrue(Inference([], []).is_instance_of(Inference([], []), language))
        self.assertTrue(Inference([], []).is_instance_of(Inference([], []), language, order=True))
        self.assertTrue(self.p__p.is_instance_of(Inference([A], [A]), language))
        self.assertTrue(self.p__p.is_instance_of(Inference([A], [B]), language))
        self.assertFalse(self.p__p.is_instance_of(Inference([A], [B]), language, subst_dict={'B': self.q}))
        self.assertTrue(self.p__q.is_instance_of(Inference([A], [B]), language))
        self.assertFalse(self.p__q.is_instance_of(Inference([A], [A]), language))
        self.assertFalse(self.p__q.is_instance_of(Inference([A], [A]), language, order=True))
        self.assertFalse(self.p_pthenq__q.is_instance_of(Inference([A], [A]), language))
        self.assertTrue(self.p_pthenq__q.is_instance_of(Inference([A, AthenB], [B]), language))
        self.assertTrue(self.p_pthenq__q.is_instance_of(Inference([AthenB, A], [B]), language))
        self.assertTrue(self.p_pthenq__q.is_instance_of(Inference([A, AthenB], [B]), language, order=True))
        self.assertFalse(self.p_pthenq__q.is_instance_of(Inference([AthenB, A], [B]), language, order=True))

        # Metainferences
        meta_identity = Inference([self.p__p],[self.p__p])
        wrong_meta_identity = Inference([self.p__p],[Inference([self.q], [self.q])])
        meta_identity_scheme = Inference([Inference([A], [A])], [Inference([A], [A])])
        self.assertTrue(meta_identity.is_instance_of(meta_identity_scheme, language))
        self.assertFalse(wrong_meta_identity.is_instance_of(meta_identity_scheme, language))

        self.assertFalse(self.p__q___p_pthenq__q.is_instance_of(meta_identity_scheme, language))
        self.assertTrue(self.p__q___p_pthenq__q.is_instance_of(Inference([Inference([A], [B])],
                                                                         [Inference([A, AthenB], [B])]),
                                                               language))
        self.assertTrue(self.p__q___p_pthenq__q.is_instance_of(Inference([Inference([A], [B])],
                                                                         [Inference([AthenB, A], [B])]),
                                                               language))
        self.assertTrue(self.p__q___p_pthenq__q.is_instance_of(Inference([Inference([A], [B])],
                                                                         [Inference([A, AthenB], [B])]),
                                                               language, order=True))
        self.assertFalse(self.p__q___p_pthenq__q.is_instance_of(Inference([Inference([A], [B])],
                                                                          [Inference([AthenB, A], [B])]),
                                                                language, order=True))

    def test_associated_conditional(self):
        # p / q
        inf = Inference([self.p], [self.q])
        assoc = Formula(["→", self.p, self.q])
        self.assertEqual(inf.associated_conditional(), assoc)

        # p, q / r, s
        inf = Inference([self.p, self.q], [Formula(["r"]), Formula(["s"])])
        assoc = Formula(["→", ["∧", self.p, self.q], ["∨", Formula(["r"]), Formula(["s"])]])
        self.assertEqual(inf.associated_conditional(), assoc)

        # (p, q / r) // (p1 / p2, p3)
        inf = Inference([Inference([self.p, self.q], [Formula(["r"])])],
                        [Inference([Formula(["p1"])], [Formula(["p2"]), Formula(["p3"])])])
        assoc = Formula(["→",
                         ["→", ["∧", self.p, self.q], Formula(["r"])],
                         ["→", Formula(["p1"]), ["∨", Formula(["p2"]), Formula(["p3"])]]
                         ])
        self.assertEqual(inf.associated_conditional(), assoc)

        # Empty inference ( / )
        self.assertEqual(Inference([], []).associated_conditional(), Formula(["⊥"]))

        # Empty premises ( / p, q)
        inf = Inference([], [self.p, self.q])
        assoc = Formula(["∨", self.p, self.q])
        self.assertEqual(inf.associated_conditional(), assoc)

        # Empty conclusions (p, q /)
        inf = Inference([self.p, self.q], [])
        assoc = Formula(["~", ["∧", self.p, self.q]])
        self.assertEqual(inf.associated_conditional(), assoc)

        # Meta emptyness
        # //
        self.assertEqual(Inference([], [], level=2).associated_conditional(), Formula(["⊥"]))

        # (/) // (/)
        self.assertEqual(Inference([Inference([], [])], [Inference([], [])]).associated_conditional(),
                         Formula(["→", ["⊥"], ["⊥"]]))

        # // /
        self.assertEqual(Inference([], [Inference([], [])]).associated_conditional(), Formula(["⊥"]))

        # / //
        self.assertEqual(Inference([Inference([], [])], []).associated_conditional(), Formula(["~", ["⊥"]]))


if __name__ == '__main__':
    unittest.main()
