Contributing Guidelines
=======================

* To install all dependencies (including testing and documentation dependencies) run:

  .. code:: bash

     $ pip install -r requirements.txt

* If you are planning on adding a new feature, please open a new branch in the git repository, named
  ``feature-<name of your feature>``. To apply a hotfix, do so in a branch ``hotfix-<what is being fixed>``. When you
  are done with your code, make a Pull Request on GitHub into de ``develop`` branch, so that administrators can review
  your code.

* Please follow the OOP style used throughout the project. Placing your new code in new files is preferred.

* Please comment and *document* your code. Use the
  `NumPy format <https://numpydoc.readthedocs.io/en/latest/format.html#docstring-standard>`_ for docstrings.

* The project documentation is built using
  `Sphinx and autodoc <https://www.sphinx-doc.org/en/master/usage/extensions/autodoc.html>`_ , with the napoleon
  extension. In other words, the documentation is automatically built from the docstrings of your classes, methods,
  functions, etc. To build the documentation open a terminal, cd into the ``docs`` folder and type:

  .. code:: bash

     $ make html

  (in Windows, it may be ``.\make html``). The generated HTML files will be under ``docs/build/html``.
  Make sure the ``docs/build`` folder is in your .gitignore file.

* Please *test* your code. Tests live in the `tests` folder, and are built using Python's native ``UnitTest`` library.
  To run all tests open a terminal in the project source and type:

  .. code:: bash

     $ python -m unittest discover

  The tests might take some time, depending on the hardware you are running them on.
