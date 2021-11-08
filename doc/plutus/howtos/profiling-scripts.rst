.. highlight:: haskell
.. _profiling_scripts:

How to profile the budget usage of Plutus scripts
=================================================

Figuring out why your script takes more CPU or memory units than you expect can be tricky.
You can find out more detail about how these resources are being used in your script by *profiling* it, and viewing the results in a flamegraph.

Compiling a script for profiling
--------------------------------

Profiling requires compiling your script differently so that it will emit information that we can use to analyse its performance.

.. note:: As with profiling in other languages, this additional instrumentation can affect how your program is optimized, so its behaviour may not be identical to the non-profiled version.

To do this, you need to give an option to the Plutus Tx plugin in the source file where your script is compiled.

.. code-block:: haskell

   {-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:profile-all #-}

This instructs the plugin to insert profiling instrumentation for all functions.
In the future there may be the option to profile a more targeted set of functions.

Acquiring an executable script
------------------------------

Profiling works by seeing how the budget is used as the script runs.
It therefore requires an executable script, which means that you need not only the validator script but all the arguments it receives.
You can get this fully-applied script from the emulator or from the Cardano node.

Running the script
------------------

You can run the script with the ``uplc`` executable.

.. note:: All the executables referred to here can be built from the ``plutus`` repository using ``cabal build``.

.. code-block:: bash

   uplc evaluate -i myscript.flat --if flat --trace-mode LogsWithBudgets -o logs

This runs the script using the trace mode that emits budget information, and puts the resulting logs in a file.
This will be a CSV file with three columns: a message indicating which function we are entering or exiting; the cumulative CPU used at that time; and the cumulative memory used at that time.

Analysing the results
---------------------

We can then convert the logs into a flamegraph using the standard ``flamegraph.pl`` tool.
The ``traceToStacks`` executable turns the logs into a format that ``flamegraph.pl`` understands

.. code-block:: bash

   cat logs | traceToStacks | flamegraph.pl > cpu.svg
   cat logs | traceToStacks --column 2 | flamegraph.pl > mem.svg

Since ``flamegraph.pl`` can only handle one metric at a time, ``traceToStacks`` has a ``--column`` argument to select the other column if you want to get a memory flamegraph.

You can then view the resulting SVGs in a viewer of your choice, e.g. a web browser.
