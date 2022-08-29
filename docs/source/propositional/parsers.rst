Parsers
=======

.. autoclass:: logics.utils.parsers.standard_parser.StandardParser
   :members:


Instances
---------

.. data:: logics.utils.parsers.classical_parser

    Parser for classical languages (with or without sentential constants and infinite atomics and metavariables).
    Its parse_replacement_dict looks as follows:

.. code-block:: python

    parse_replacement_dict = {
        # For negation
        '¬': '~',
        'not ': '~',

        # For conjunction
        '&': '∧',
        ' and ': '∧',

        # For disjunction
        'v': '∨',  # The key is a letter v, so if you plan to use this parser dont use that as an atomic of Language
        ' or ': '∨',

        # For conditional
        ' then ': '→',
        '-->': '→',
        'if ': '',  # if you write 'if p then q' it will just leave 'p then q'

        # For biconditional
        ' iff ': '↔',
        '<->': '↔',

        # For the semantic hammer
        '|=': '/',

        # Sentential constants
        'falsum': '⊥',
        'Falsum': '⊥',
        'bottom': '⊥',
        'Bottom': '⊥',
        'verum': '⊤',
        'Verum': '⊤',
        'Top': '⊤',
        'top': '⊤',

        # For sequent calculi
        '==>': '⇒',
        'Gamma': 'Γ',
        'Delta': 'Δ',
        'Sigma': 'Σ',
        'Pi': 'Π',
        'Theta': 'Θ',
        'Lambda': 'Λ',
    }

.. data:: logics.utils.parsers.modal_parser

    Similar to the parser above, but modal languages. Adds the following replacement rules:

.. code-block:: python

    modal_replacement_dict.update({
        'box ': '□',
        'Box ': '□',
        'necessary ': '□',
        'nec ': '□',
        '◻': '□',
        'diamond ': '◇',
        'Diamond ': '◇',
        'possible ': '◇',
        'pos ': '◇'
    })

.. data:: logics.utils.parsers.LFI_parser

    Similar to the classical parser, but contains the unary connective °. Adds the following replacement rules:

.. code-block:: python

    LFI_replacement_dict.update({
        "°": "∘",
        "circ": "∘",
    })
