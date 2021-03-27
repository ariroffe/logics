import unittest

from logics.classes.propositional import Language, InfiniteLanguage, Formula


class TestFormulaClass(unittest.TestCase):
    def setUp(self):
        at = ['p', 'q', 'r']
        mt = ['A', 'B', 'C']
        cad = {'~': 1, '&': 2}
        sc = ['⊥']
        self.language = Language(atomics=at, metavariables=mt, constant_arity_dict=cad, sentential_constants=sc)
        self.infinite_language = InfiniteLanguage(atomics=at, metavariables=mt,
                                                  constant_arity_dict=cad, sentential_constants=sc)

    def test_atomics(self):
        p = Formula(['p'])
        s = Formula(['s'])
        p1 = Formula(['p1'])
        pq = Formula(['pq'])

        self.assertTrue(p.is_well_formed(self.language))
        self.assertTrue(p.is_atomic)
        self.assertEqual(p.subformulae, [p])
        self.assertEqual(p.atomics_inside(self.language), {'p'})
        self.assertEqual(p.depth, 0)

        for f in (s, p1, pq):
            self.assertFalse(f.is_well_formed(self.language))

    def test_inifite_language_atomics(self):
        p = Formula(['p'])
        s = Formula(['s'])
        p1 = Formula(['p1'])
        q545 = Formula(['q545'])
        pq = Formula(['pq'])

        for f in (p, p1, q545):
            self.assertTrue(f.is_well_formed(self.infinite_language))
            self.assertTrue(f.is_atomic)
            self.assertEqual(f.subformulae, [f])

        for f in (s, pq):
            self.assertFalse(f.is_well_formed(self.infinite_language))

    def test_molecular_formulae(self):
        p = Formula(['p'])
        q = Formula(['q'])
        notp = Formula(['~', ['p']])
        notnotp = Formula(['~', ['~', ['p']]])
        notnotpandnotp = Formula(['&', notnotp, notp])
        p123 = Formula(['p123'])
        notpandp123 = Formula(['&', notp, p123])
        qandp = Formula(['&', q, p])

        # Test init method
        self.assertTrue(isinstance(notnotp[1], Formula))
        self.assertTrue(isinstance(notnotp[1][1], Formula))

        # Test is_well_formed
        for x in [notnotp, notnotpandnotp]:
            self.assertTrue(x.is_well_formed(self.language))
            self.assertFalse(x.is_atomic)
        for x in [p123, notpandp123]:
            self.assertFalse(x.is_well_formed(self.language))
            self.assertTrue(x.is_well_formed(self.infinite_language))

        # Test main symbol
        self.assertEqual(notnotp.main_symbol, '~')
        self.assertEqual(notnotpandnotp.main_symbol, '&')

        # Test depth, subformulae and atomics_inside methods
        self.assertEqual(notp.depth, 1)
        self.assertEqual(notnotp.depth, 2)
        self.assertEqual(Formula(['&', notnotp, notnotp]).depth, 3)
        notnotp_sf = notnotp.subformulae

        for x in [p, notp, notnotp]:
            self.assertIn(x, notnotp_sf)
        notnotpandnotp_sf = notnotpandnotp.subformulae
        for x in [p, notp, notnotp, notnotpandnotp]:
            self.assertIn(x, notnotpandnotp_sf)
            self.assertEqual(notnotpandnotp_sf.count(x), 1)

        self.assertEqual(p.atomics_inside(self.language), {'p'})
        self.assertEqual(notnotpandnotp.atomics_inside(self.language), {'p'})
        self.assertEqual(qandp.atomics_inside(self.language), {'p', 'q'})

    def test_sentential_constants(self):
        self.assertTrue(Formula(['⊥']).is_well_formed(self.language))
        self.assertFalse(Formula(['*']).is_well_formed(self.language))

    def test_substitute_subformulae(self):
        p = Formula(['p'])
        q = Formula(['q'])
        notp = Formula(['~', ['p']])
        qandq_andp = Formula(['&', ['&', ['q'], ['q']], ['p']])  # (q & q) & p

        self.assertEqual(p.substitute(p, p), p)
        self.assertEqual(p.substitute(p, q), q)
        self.assertEqual(p, Formula(['p']))  # check that the original formula did not change
        self.assertEqual(p.substitute(p, notp), notp)
        self.assertEqual(notp.substitute(p, notp), Formula(['~', ['~', ['p']]]))  # watch that f2 is not in itself
        self.assertEqual(type(notp.substitute(p, notp)), Formula)

        self.assertEqual(qandq_andp.substitute(p, q), Formula(['&', ['&', ['q'], ['q']], ['q']]))
        self.assertEqual(qandq_andp.substitute(Formula(['&', q, q]), q), Formula(['&', ['q'], ['p']]))
        self.assertEqual(qandq_andp, Formula(['&', ['&', ['q'], ['q']], ['p']]))
        
    def test_instantiate(self):
        A = Formula(['A'])
        B = Formula(['B'])
        C = Formula(['C'])

        AandB = Formula(['&', A, B])
        BandC = Formula(['&', B, C])
        subst_dict = {'A': B, 'B': C}
        self.assertEqual(AandB.instantiate(self.language, subst_dict), BandC)

        p = Formula(['p'])
        pandp = Formula(['&', p, p])
        subst_dict = {'A': pandp, 'B': C}
        self.assertEqual(AandB.instantiate(self.language, subst_dict), Formula(['&', pandp, C]))
        self.assertRaises(ValueError, BandC.instantiate, self.language, subst_dict)

        pandA = Formula(['&', p, A])
        subst_dict = {'A': pandp, 'p': C}  # substitutions for non-schematic formulae should be ignored
        self.assertEqual(pandA.instantiate(self.language, subst_dict), Formula(['&', p, pandp]))

    def test_schematic_substitute(self):
        cond = Formula(['→', ['A'], ['B']])
        disj = Formula(['∨', ['~', ['A']], ['B']])

        f = Formula(['→', ['p'], ['→', ['p'], ['q']]])
        self.assertEqual(f.schematic_substitute(self.language, cond, disj),
                         Formula(['∨', ['~', ['p']], ['∨', ['~', ['p']], ['q']]]))
        # Might need more testing than this

    def test_metavariables(self):
        A = Formula(['A'])
        R = Formula(['R'])
        A1 = Formula(['A1'])
        A545 = Formula(['A545'])
        AB = Formula(['AB'])

        self.assertTrue(A.is_well_formed(self.language))
        self.assertTrue(A.is_well_formed(self.infinite_language))
        self.assertTrue(A.is_atomic)
        self.assertTrue(A.is_schematic(self.language))
        self.assertEqual(A.subformulae, [A])

        for m in (A1, A545):
            self.assertFalse(m.is_well_formed(self.language))
            self.assertTrue(m.is_well_formed(self.infinite_language))
            self.assertTrue(m.is_atomic)
            self.assertTrue(m.is_schematic(self.infinite_language))
            self.assertEqual(m.subformulae, [m])

        for m in (R, AB):
            self.assertFalse(m.is_well_formed(self.infinite_language))

        p = Formula(['p'])
        # Substitute A for p, and it should stop being schematic
        subs = A.substitute(A, p)
        self.assertEqual(subs, p)
        self.assertFalse(subs.is_schematic(self.language))
        # Substitute back and it should be schematic again
        subs2 = subs.substitute(p, A)
        self.assertEqual(subs2, A)
        self.assertTrue(subs2.is_schematic(self.language))

        # Test is_instance_of method
        self.assertTrue(p.is_instance_of(p, self.language))  # p of p
        self.assertTrue(p.is_instance_of(A, self.language))  # p of A
        self.assertTrue(Formula(['~', p]).is_instance_of(A, self.language))  # ~p of A
        self.assertTrue(Formula(['~', ['∨', p, p]]).is_instance_of(A, self.language))  # ~(p ∨ p) of A
        self.assertTrue(Formula(['∨', p, p]).is_instance_of(Formula(['∨', A, A]), self.language))  # p ∨ p of A ∨ A
        self.assertTrue(Formula(['∨', p, p]).is_instance_of(Formula(['∨', p, A]), self.language))  # p ∨ p of p ∨ A

        self.assertFalse(p.is_instance_of(Formula(['∨', A, A]), self.language))  # p of A ∨ A
        # ~(p ∨ p) of A ∨ A
        self.assertFalse(Formula(['~', ['∨', p, p]]).is_instance_of(Formula(['∨', A, A]), self.language))
        # q ∨ p of p ∨ A
        self.assertFalse(Formula(['∨', ['q'], p]).is_instance_of(Formula(['∨', p, A]), self.language))
        f = Formula(['→', ['p'], ['→', ['p'], ['q']]])
        m = Formula(['→', ['A'], ['→', ['B'], ['A']]])
        self.assertFalse(f.is_instance_of(m, self.language))  # p → (p → q) of A → (B → A)  (check uniform substitution)
        self.assertFalse(Formula(['∨', A, A1]).is_instance_of(Formula(['∨', A, A]), self.language))  # A v A1 of A ∨ A

        # A few tests with a substitution dict
        self.assertFalse(p.is_instance_of(A, self.language, {'A': Formula({'q'})}))
        self.assertTrue(p.is_instance_of(A, self.language, {'A': Formula({'p'})}))
        self.assertFalse(Formula(['∨', p, p]).is_instance_of(Formula(['∨', p, A]), self.language,
                                                             subst_dict={'A': Formula({'q'})}))

        # Return a subst dict
        self.assertEqual(p.is_instance_of(A, self.language, return_subst_dict=True), (True, {'A': p}))
        self.assertEqual(Formula(['∨', Formula({'q'}), p]).is_instance_of(Formula(['∨', Formula(['B']), A]),
                                                                          self.language, return_subst_dict=True),
                         (True, {'A': p, 'B': Formula({'q'})}))


if __name__ == '__main__':
    unittest.main()
