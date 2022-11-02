Optimization techniques for Plutus scripts
==========================================

Identifying problem areas
~~~~~~~~~~~~~~~~~~~~~~~~~

In order to identify which parts of the script are responsible for significant resource consumption, you can use the :ref:`profiling support <profiling_scripts>`.

Using strict let-bindings to avoid recomputation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Let-bindings in Haskell are translated to strict let-bindings in Plutus IR, unless they look like they might do computation, in which case they are translated to non-strict let-bindings.
This is to avoid triggering effects (e.g. errors) at unexpected times.

However, non-strict let-bindings are less efficient.
They do not evaluate their right-hand side immediately, instead they do so where the variable is used.
But they are not *lazy* (evaluating the right-hand side at most once), instead it may be evaluated once each time it is used.
You may wish to explicitly mark let-bindings as strict in Haskell to avoid this.

.. code-block:: haskell

    -- This may be compiled non-strictly, which could result
    -- in it being evaluated multiple times. However, it will
    -- not be evaluated if we take the branch where it is not used.
    let x = y + z
    in if b then x + x else 1

    -- This will be compiled strictly, but this will mean it
    -- is evaluated even if we take the branch where it is not used.
    let !x = y + z
    in if b then x + x else 1

Specializing higher-order functions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The use of higher-order functions is a common technique to facilitate code reuse.
Higher-order functions are widely used in the Plutus libraries but can be less efficient than specialized versions.

For instance, the Plutus function ``findOwnInput`` makes use of the higher-order function ``find`` to search for the current script input.

.. code-block:: haskell

    findOwnInput :: ScriptContext -> Maybe TxInInfo
    findOwnInput ScriptContext{scriptContextTxInfo=TxInfo{txInfoInputs},
                 scriptContextPurpose=Spending txOutRef} =
        find (\TxInInfo{txInInfoOutRef} -> txInInfoOutRef == txOutRef) txInfoInputs
    findOwnInput _ = Nothing

This can be rewritten with a recursive function specialized to the specific check in question.

.. code-block:: haskell

    findOwnInput :: ScriptContext -> Maybe TxInInfo
    findOwnInput ScriptContext{scriptContextTxInfo=TxInfo{txInfoInputs},
                 scriptContextPurpose=Spending txOutRef} = go txInfoInputs
        where
            go [] = Nothing
            go (i@TxInInfo{txInInfoOutRef} : rest) = if txInInfoOutRef == txOutRef
                                                     then Just i
                                                     else go rest
    findOwnInput _ = Nothing

Common sub-expression elimination
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When several instances of identical expressions exist within a function’s body, it’s worth replacing them with a single (strict) let-bound variable to hold the computed value.

In this example, the cost of storing and retrieving ``n * c`` in a single variable is significantly less than recomputing it several times.

.. code-block:: haskell

    let a' = a `divide` n * c
        -- occurrence 1
        b' = b * (n * c)
        -- occurrence 2
        C' = c + (n * c)
    in
      foo a' b' c' n

    -- Only one occurrence
    let !t_mul = n * c
        a' = a `divide` t_mul
        b' = b * t_mul
        c' = c + t_mul
    in
      foo a' b' c' n

Using ``error`` for faster failure
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Plutus scripts have access to one impure effect, ``error``, which immediately terminates the script evaluation and will fail validation.
This failure is very fast, but it is also unrecoverable, so only use it in cases where you want to fail the entire validation if there is a failure.

The Plutus libraries have some functions that fail with ``error``.
Usually these are given an ``unsafe`` prefix to their name.
For example, :hsobj:`PlutusTx.IsData.Class.FromData` parses a value of type ``Data``, returning the result in a ``Maybe`` value to indicate whether it succeeded or failed; whereas :hsobj:`PlutusTx.IsData.Class.UnsafeFromData` does the same but fails with ``error``.
