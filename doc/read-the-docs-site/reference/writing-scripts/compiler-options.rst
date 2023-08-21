.. _plutus_tx_options:

Plutus Tx Compiler Options
==========================

These options can be passed to the compiler via the ``OPTIONS_GHC`` pragma, for instance

.. code-block:: haskell

   {-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:dump-uplc #-}
   {-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations=3 #-}

For each boolean option, you can add a ``no-`` prefix to switch it off, such as
``no-typecheck``, ``no-simplifier-beta``.

.. include:: ./compiler-options-table.rst
