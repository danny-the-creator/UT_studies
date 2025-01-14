Info Gain
=========

For computing the information gain, students must implement the :py:meth:`entropy` and :py:meth:`conditional_entropy` functions.
Both of these functions are used by the :py:meth:`info_gain` method to compute the information gain.

.. automethod:: ml4sec.Assignment.entropy

.. automethod:: ml4sec.Assignment.conditional_entropy

.. automethod:: ml4sec.Assignment.info_gain

Visualisation methods
^^^^^^^^^^^^^^^^^^^^^

To compute the information gain for each feature extracted in your :py:meth:`extract` function, we provide the :py:meth:`show_info_gain` method.

.. automethod:: ml4sec.Assignment.show_info_gain

Submitting
^^^^^^^^^^

To submit the repair assignment, please use the following :py:meth:`submit_repair` function.

.. note::
   Please remember to submit **both** the :py:meth:`submit_repair` function as well as the :py:meth:`submit` function (see :ref:`Submit`) for the entire assignment.

.. automethod:: ml4sec.Assignment.submit_repair
