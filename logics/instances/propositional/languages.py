from copy import deepcopy

from logics.classes.propositional.language import Language, InfiniteLanguage

# LANGUAGES FOR CLASSICAL LOGIC (and many non-classical)
atomics = ['p', 'q', 'r', 's', 't']  # atomics will be any of them followed by an integer
metavariables = ['A', 'B', 'C', 'D']
constant_arity_dict = {'~': 1, '∧': 2, '∨': 2, '→': 2, '↔': 2}
sentential_constants = ['⊥', '⊤']
context_variables = ['Γ', 'Δ', 'Σ', 'Λ', 'Π', 'Θ']

classical_language = Language(atomics=atomics, metavariables=metavariables, constant_arity_dict=constant_arity_dict,
                              context_variables=context_variables)

classical_infinite_language = InfiniteLanguage(atomics=atomics, metavariables=metavariables,
                                               constant_arity_dict=constant_arity_dict,
                                               context_variables=context_variables)

classical_language_with_sent_constants = Language(atomics=atomics, metavariables=metavariables,
                                                  constant_arity_dict=constant_arity_dict,
                                                  sentential_constants=sentential_constants,
                                                  context_variables=context_variables)

classical_infinite_language_with_sent_constants = InfiniteLanguage(atomics=atomics, metavariables=metavariables,
                                                                   constant_arity_dict=constant_arity_dict,
                                                                   sentential_constants=sentential_constants,
                                                                   context_variables=context_variables)

classical_infinite_language_noconditional = InfiniteLanguage(atomics=atomics, metavariables=metavariables,
                                                             constant_arity_dict={'~': 1, '∧': 2, '∨': 2},
                                                             context_variables=context_variables)

classical_infinite_language_nobiconditional = InfiniteLanguage(atomics=atomics, metavariables=metavariables,
                                                               constant_arity_dict={'~': 1, '∧': 2, '∨': 2, '→': 2},
                                                               context_variables=context_variables)

classical_infinite_language_with_sent_constants_nobiconditional = InfiniteLanguage(atomics=atomics,
                                                                                   metavariables=metavariables,
                                                                constant_arity_dict={'~': 1, '∧': 2, '∨': 2, '→': 2},
                                                                sentential_constants=sentential_constants,
                                                                context_variables=context_variables)

classical_infinite_language_only_negation_conditional = InfiniteLanguage(atomics=atomics, metavariables=metavariables,
                                                                         constant_arity_dict={'~': 1, '→': 2},
                                                                         context_variables=context_variables)

# LFIs
LFI_language = deepcopy(classical_infinite_language_with_sent_constants)
LFI_language.constant_arity_dict["•"] = 1
LFI_language.constant_arity_dict["◦"] = 1

# MODAL LOGIC
modal_arity_dict = {'~': 1, '□': 1, '◇': 1, '∧': 2, '∨': 2, '→': 2, '↔': 2}
modal_language = Language(atomics=atomics, metavariables=metavariables,
                          constant_arity_dict=modal_arity_dict, context_variables=context_variables)
modal_infinite_language = InfiniteLanguage(atomics=atomics, metavariables=metavariables,
                                           constant_arity_dict=modal_arity_dict, context_variables=context_variables)
modal_infinite_language_with_sent_constants = InfiniteLanguage(atomics=atomics, metavariables=metavariables,
                                                               constant_arity_dict=modal_arity_dict,
                                                               sentential_constants=sentential_constants,
                                                               context_variables=context_variables)
