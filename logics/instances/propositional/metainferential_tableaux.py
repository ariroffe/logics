from logics.classes.propositional import Formula, Inference
from logics.classes.propositional.proof_theories.metainferential_tableaux import (
    MetainferentialTableauxStandard, MetainferentialTableauxNode
)

inf0 = MetainferentialTableauxNode(
    content=Inference(premises=[Formula(['Γ'])], conclusions=[Formula(['Δ'])]),
    index=MetainferentialTableauxStandard(['X', 'Y']),
)
# Has no children because we apply it in a different, hardcoded, way


metainferential_tableaux_rules = {
    'inf0': inf0,
}
