from logics.classes.propositional import Formula, Inference
from logics.classes.propositional.proof_theories import AxiomSystem
from logics.instances.propositional.languages import classical_infinite_language_only_negation_conditional


classical_logic_axioms = {
    # ax1:  A → (B → A)
    'ax1': Formula(['→', ['A'], ['→', ['B'], ['A']]]),
    # ax2: (A → (B → C)) → ((A → B) → (A → C))
    'ax2': Formula(['→', ['→', ['A'], ['→', ['B'], ['C']]], ['→', ['→', ['A'], ['B']], ['→', ['A'], ['C']]]]),
    # ax3: (~A → ~B) → (B → A)
    'ax3': Formula(['→', ['→', ['~', ['A']], ['~', ['B']]], ['→', ['B'], ['A']]]),
}
classical_logic_rules = {
    # Modus ponens A, A → B / B
    'mp': Inference([Formula(['A']), Formula(['→', ['A'], ['B']])], [Formula(['B'])])
}

classical_logic_axiom_system = AxiomSystem(language=classical_infinite_language_only_negation_conditional,
                                           axioms=classical_logic_axioms, rules=classical_logic_rules)
