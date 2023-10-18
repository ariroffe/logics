from logics.instances.propositional.languages import classical_infinite_language
from logics.classes.propositional import Formula, Inference
from logics.classes.propositional.proof_theories.metainferential_tableaux import (
    MetainferentialTableauxStandard, MetainferentialTableauxNode, MetainferentialTableauxSystem
)
from logics.utils.solvers.tableaux import metainferential_tableaux_solver

# The following rules have no children because we apply them in a different, hardcoded, way
inf0 = MetainferentialTableauxNode(
    content=Inference(premises=[Formula(['Γ'])], conclusions=[Formula(['Δ'])]),
    index=MetainferentialTableauxStandard(['X', 'Y'], bar=True),
)

inf1 = MetainferentialTableauxNode(
    content=Inference(premises=[Formula(['Γ'])], conclusions=[Formula(['Δ'])]),
    index=MetainferentialTableauxStandard(['X', 'Y'], bar=False),
)

complement = MetainferentialTableauxNode(
    content=Formula(['A']),
    index=MetainferentialTableauxStandard('X', bar=True),
)

intersection = MetainferentialTableauxNode(
    content=Formula(['A']),
    index=MetainferentialTableauxStandard('X', bar=False),
)
MetainferentialTableauxNode(
    content=Formula(['A']),
    index=MetainferentialTableauxStandard('Y', bar=False),
    parent=intersection,
)

singleton = MetainferentialTableauxNode(
    content=Formula(['A']),
    index=MetainferentialTableauxStandard('X', bar=False),
)


metainferential_tableaux_rules = {
    'inf0': inf0,
    'inf1': inf1,
    'complement': complement,
    'intersection': intersection,
    'singleton': singleton,
}

sk_metainferential_tableaux_system = MetainferentialTableauxSystem(
    base_indexes={'1', 'i', '0'},
    language=classical_infinite_language,
    rules=metainferential_tableaux_rules,
    closure_rules= [],
    solver=metainferential_tableaux_solver,
)