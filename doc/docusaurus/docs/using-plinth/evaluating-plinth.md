---
sidebar_position: 12
---

# Evaluating CompiledCode

`CompiledCode` is intended to be evaluated by Cardano nodes during transaction validation. For this purpose, it is serialized and included in a transaction.

However, it is also possible to evaluate `CompiledCode` without running a node. The Plutus evaluator, called the CEK Machine, can be used independently of the Cardano node for testing and troubleshooting. By evaluating Plinth programs locally, developers can not only obtain the immediate result of the code but also access the traces emitted during evaluation and the consumed execution budget.

:::info Version Information
This functionality was released in version 1.47.
:::

Let's consider the following example Plinth program:
<LiteralInclude 
  file="Example/Evaluation/Main.hs" 
  language="haskell" 
  title="Example Plinth code" 
  start="-- BEGIN Plinth" 
  end="-- END Plinth" />

This code defines a function that expects an `Integer` argument and returns an `Integer` value.

To compile it, use the `compile` function as described earlier in the [Compiling Plinth code](./compiling-plinth.md) section:

<LiteralInclude 
  file="Example/Evaluation/Main.hs" 
  language="haskell" 
  title="Plinth code compiled" 
  start="-- BEGIN CompiledCode" 
  end="-- END CompiledCode" />

To evaluate `compiledCode`, add the following dependencies to your cabal file:
```cabal
build-depends: 
  plutus-tx, 
  plutus-tx:plutus-tx-testlib, 
  plutus-ledger-api 
```

This allows you to import the necessary functionality:

<LiteralInclude 
  file="Example/Evaluation/Main.hs" 
  language="haskell" 
  title="Required imports" 
  start="-- BEGIN Imports" 
  end="-- END Imports" />

You can evaluate this compiled code without applying it to any arguments. The evaluation will succeed, returning a value of type `Integer -> Integer`:

```haskell
result :: EvalResult
result = evaluateCompiledCode compiledCode
```

The `EvalResult` type is declared as follows:

```haskell
data EvalResult = EvalResult
  { evalResult
      :: Either
           (CekEvaluationException NamedDeBruijn DefaultUni DefaultFun)
           (NTerm DefaultUni DefaultFun ())
  , evalResultBudget :: ExBudget
  , evalResultTraces :: [Text]
  }
  deriving stock (Show)
```

The `evalResult` field contains the result of the evaluation, which can be either a successful result or an error.

The `evalResultBudget` field contains the execution budget used during evaluation, including CPU and memory usage.

The `evalResultTraces` field contains any traces emitted during evaluation.

The `evaluateCompiledCode` function is the main workhorse of the evaluation process. Under the hood, it uses the Plutus Core evaluator (CEK machine) configured with the latest cost model stored statically in the Plutus repository.

:::caution Caveat
The execution budget reported by `evaluateCompiledCode` is not guaranteed to exactly match the execution budget spent by Cardano mainnet nodes. This discrepancy arises because the cost model used by `evaluateCompiledCode` may differ from the cost model active on the Cardano chain at a specific moment. The definitive values for on-chain cost calculations are protocol parameters, which are part of the chain's state. In practice, these parameters are typically derived from the cost model stored in the Plutus repository at some earlier point, though this is not guaranteed. During on-chain evaluation, the ledger provides a cost model to the Plutus Core evaluator.
:::

The companion function `evaluateCompiledCode'` is a more general version of `evaluateCompiledCode`, allowing you to specify the cost model via the `MachineParameters` type. This function is useful for testing, but in most cases, you can use `evaluateCompiledCode` without worrying about these details.

To use it, supply a `MachineParameters` value like this:

<LiteralInclude 
  file="Example/Evaluation/Main.hs" 
  language="haskell" 
  title="Evaluating with custom MachineParameters" 
  start="-- BEGIN MachineParameters" 
  end="-- END MachineParameters" />

You can use the `Show` instance of `EvalResult` to print the result of the evaluation:
<details>
<summary>Show raw <code>EvalResult</code> output</summary>

```haskell
EvalResult
  { evalResult =
      Right
        ( LamAbs
            ()
            (NamedDeBruijn{ndbnString = "x", ndbnIndex = 0})
            ( Apply
                ()
                ( Apply
                    ()
                    (Builtin () AddInteger)
                    ( Apply
                        ()
                        ( Apply
                            ()
                            ( Force
                                ()
                                (Builtin () Trace)
                            )
                            ( Constant
                                ()
                                (Some (ValueOf DefaultUniString "Evaluating x"))
                            )
                        )
                        (Var () (NamedDeBruijn{ndbnString = "x", ndbnIndex = 1}))
                    )
                )
                ( Apply
                    ()
                    ( Apply
                        ()
                        (Force () (Builtin () Trace))
                        (Constant () (Some (ValueOf DefaultUniString "Evaluating constant")))
                    )
                    (Constant () (Some (ValueOf DefaultUniInteger 2)))
                )
            )
        )
  , evalResultBudget =
      ExBudget
        { exBudgetCPU = ExCPU 16100
        , exBudgetMemory = ExMemory 200
        }
  , evalResultTraces = []
  }
```
</details>

However, there is a dedicated function, `displayEvalResult`, that prints the result in a more concise and human-readable format:

```
Evaluation was SUCCESSFUL, result is:
  \x ->
    addInteger
      (force trace "Evaluating x" x)
      (force trace "Evaluating constant" 2)

Execution budget spent:
  CPU 16,100
  MEM 200

No traces were emitted
```

This output shows that the evaluation was successful, and the resulting UPLC value is an (unapplied) lambda abstraction.

To apply the compiled lambda abstraction to an argument, you need a compiled argument. There are several ways to obtain it from a Haskell value known at compile time:
1. "Lift" it into `CompiledCode`. See the [Lifting Values into CompiledCode](./lifting.md) section for more details.
    <LiteralInclude 
      file="Example/Evaluation/Main.hs" 
      language="haskell" 
      title="Lift a constant value into CompiledCode" 
      start="-- BEGIN LiftedArgument" 
      end="-- END LiftedArgument" />

2. Use `$(compile [|| ... ||])` in the same way as when compiling the function itself.
    <LiteralInclude 
      file="Example/Evaluation/Main.hs" 
      language="haskell" 
      title="Compile a constant value into CompiledCode" 
      start="-- BEGIN CompiledArgument" 
      end="-- END CompiledArgument" />

Once you have an argument of type `CompiledCode a`, you can apply it to the compiled function using either the [`applyCode`](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Code.html#v:applyCode) function

<LiteralInclude 
  file="Example/Evaluation/Main.hs" 
  language="haskell" 
  title="Applying compiled function to an argument (type-safe way)" 
  start="-- BEGIN SafeApplicationResult" 
  end="-- END SafeApplicationResult" />

or the [`unsafeApplyCode`](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Code.html#v:unsafeApplyCode) function.

<LiteralInclude 
  file="Example/Evaluation/Main.hs" 
  language="haskell" 
  title="Applying compiled function to an argument (unsafe way)" 
  start="-- BEGIN UnsafeApplicationResult" 
  end="-- END UnsafeApplicationResult" />

Let's print the result of the evaluation:

<LiteralInclude 
  file="Example/Evaluation/Main.hs" 
  language="haskell" 
  title="Pretty-printng the result" 
  start="-- BEGIN PrintResult" 
  end="-- END PrintResult" />

```
Simulating latest Plutus Ledger Language and
the latest Protocol Version evaluation:
--------------------------------------------
Evaluation was SUCCESSFUL, result is:
  4

Execution budget spent:
  CPU 508,304
  MEM 1,966
```

Nice! Now we can see that calculating `2 + 2 = 4` using the CEK Machine (UPLC interpreter) requires 508,304 CPU and 1,966 MEM units.

For completeness, here is an example of a failed evaluation:

```
Evaluation FAILED:
  An error has occurred:
  The machine terminated because of an error,  
  either from a built-in function or from an explicit use of 'error'.

Execution budget spent:
  CPU 220,304
  MEM 166

Evaluation traces:
  1. Evaluating x
  2. Evaluating constant
```

Both example outputs include execution traces emitted during evaluation. These can be helpful when debugging your Plinth code.

Caveat: traces add to the script size, so make sure to remove them when you are done debugging.

You can find the complete example code in [`Example/Evaluation/Main.hs`](../../static/code/Example/Evaluation/Main.hs) in the Plutus repository.
