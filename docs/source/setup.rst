Installation and Setup
======================

Easy Install
------------

To install using ``pip``:

.. code:: bash

   $ pip install logics


Cloning From the Repo
---------------------

If you wish to collaborate with this project, you can clone the GitHub repository:

.. code:: bash

   $ git clone https://github.com/ariroffe/logics.git


Before installing the dependencies, make sure to create and activate a virtual environment
(`this <https://www.digitalocean.com/community/tutorials/how-to-install-python-3-and-set-up-a-local-programming-environment-on-ubuntu-16-04#step-2-—-setting-up-a-virtual-environment>`_
is one way to do that). After that, you can install all dependencies by running:

.. code:: bash

   $ pip install -r requirements.txt

After ``pip`` is done installing, you can check that everything is working properly by running the test suite:

.. code:: bash

   $ python -m unittest discover
