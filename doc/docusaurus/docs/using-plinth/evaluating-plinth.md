---
sidebar_position: 12
---

# Evaluating CompiledCode for testing

The `CompiledCode` is intended to be evaluated by Cardano nodes when 
transaction validation occurs. For this purpose, it is serialized and included in a transaction.

However, it is also possible to evaluate `CompiledCode` in a test environment. 
This is useful for testing and troubleshooting. By doing so, Plinth developers can
not only get the immediate result of the code but also obtain the traces emitted 
during the evaluation, as well as the consumed execution budget.

Let's consider the following example Plinth program:
<LiteralInclude 
  file="Example/Evaluation/Main.hs" 
  language="haskell" 
  title="Example Plinth code" 
  start="-- BEGIN Plinth" 
  end="-- END Plinth" />

This code represents a function that expects an `Integer` argument
and returns the `Integer` value. 

To compile it, we can use the `compile` function as described earlier in the "[Compiling Plinth code](./compiling-plinth.md)" section:

<LiteralInclude 
  file="Example/Evaluation/Main.hs" 
  language="haskell" 
  title="Plinth code compiled" 
  start="-- BEGIN CompiledCode" 
  end="-- END CompiledCode" />

In order to evaluate `compiledCode`, we need to add the `plutus-tx:plutus-tx-testlib` 
dependency to our cabal file:
```cabal
  build-depends:
    , plutus-tx:plutus-tx-testlib
```

So that we can import the necessary functionality:

```haskell
import PlutusTx.Test (
  EvalResult,
  applyLifted,
  evaluateCompiledCode,
  prettyEvalResult
 )
```

It is possible to evaluate this compiled code without applying it to any arguments, 
and evaluation will succeed, returning the value of type `Integer -> Integer`:

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

The `evalResult` field contains the result of the evaluation, which can either be a successful evaluation or an error.

The `evalResultBudget` field contains the execution budget used during the evaluation,
which includes the CPU and memory usage.

The `evalResultTraces` field contains the traces emitted during the evaluation.

One can use its `Show` instance to print the result of the evaluation:
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

The output is quite verbose and not very readable.
To make it more readable, we can use the `prettyEvalResult` function, 
which formats the output in a prettier way:

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

This output reveals that the evaluation was successful, and the resultng UPLC 
value is an (un-applied) lambda abstraction. 

To apply the compiled lambda abstraction to an argument we need to have a compiled argument, 
and there are several ways of obtaining it from a Haskell value known at compile time:
1. "lift" it into `CompiledCode`. See the [Lifting Values into CompiledCode](./lifting.md) section for more details.
    <LiteralInclude 
      file="Example/Evaluation/Main.hs" 
      language="haskell" 
      title="Lift a constant value into CompiledCode" 
      start="-- BEGIN LiftedArgument" 
      end="-- END LiftedArgument" />

2. `$(compile [|| ... ||])` it the same way we compiled the function itself.
    <LiteralInclude 
      file="Example/Evaluation/Main.hs" 
      language="haskell" 
      title="Compile a constant value into CompiledCode" 
      start="-- BEGIN CompiledArgument" 
      end="-- END CompiledArgument" />

Once we have an argument of type `CompiledCode a`, we can apply it to the compiled function
using either the [`applyCode`](https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Code.html#v:applyCode) function 

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

Lets print the result of the evaluation:

<LiteralInclude 
  file="Example/Evaluation/Main.hs" 
  language="haskell" 
  title="Pretty-printng the result" 
  start="-- BEGIN main" 
  end="-- END main" />

```
Evaluation was SUCCESSFUL, result is:
  4

Execution budget spent:
  CPU 508,304
  MEM 1,966

Evaluation traces:
  1. Evaluating x
  2. Evaluating constant
```

Nice! Now we can see that calculating `2 + 2 = 4` using the CEK Machine (UPLC interpreter)
requires 508,304 CPU and 1,966 MEM units.

For the sake of completeness, here is an example of an evaluation that fails:

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

Both example outputs include execution traces emited during the evaluation.
These can come in handy when debugging your Plinth code.

Caveat: traces add up to the script size, so make sure to remove them 
when you are done debugging. 
