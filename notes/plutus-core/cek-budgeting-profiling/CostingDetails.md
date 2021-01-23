## A closer look at budgeting costs

[January 2020, Plutus repository at 9c95674]

Following on from [CekProfiling.md](./CekProfiling.md), this takes a closer look at
how cost accounting affects execution costs.

`Language.PlutusCore.Evaluation.Machine.ExBudgeting` defines the following types for
budgeting:

```
data ExBudget = ExBudget { _exBudgetCPU :: ExCPU, _exBudgetMemory :: ExMemory }
-- `ExCPU` and `ExMemory` are just wrappers around `Integer`

newtype ExRestrictingBudget = ExRestrictingBudget ExBudget deriving (Show, Eq)

data ExBudgetMode =
      Counting -- ^ For precalculation
    | Restricting ExRestrictingBudget -- ^ For execution, to avoid overruns

data ExBudgetState exBudgetCat = ExBudgetState
    { _exBudgetStateTally  :: ExTally exBudgetCat
    , _exBudgetStateBudget :: ExBudget
    }
```

It also declares the `SpendBudget` class:

```
class (ExBudgetBuiltin fun exBudgetCat, ToExMemory term) =>
            SpendBudget m fun exBudgetCat term | m -> fun exBudgetCat term where
    spendBudget :: exBudgetCat -> ExBudget -> m ()
```

This contains a single method `spendBudget`, which is called during execution.
The intention is that `spendBudget` accumulates costs in an `ExBudgetState`
object in the monad `m`. In `Counting` mode execution costs (possibly
partitioned so that costs of particular operations are collected separately)
are accumulated to find the total cost of executing a program, and in
`Restricting` mode the program is supplied with an initial budget limit, and
execution is terminated if the limit is exceeded at any point during execution.

The `StrictData` option is turned on in `ExBudgeting.hs` to avoid a memory leak
that occurred in an earlier version of the code, where costs were being
accumulated lazily; in fact making just the `ExBudget` and `ExBudgetState` types
strict was sufficient to remove the leak, but `StrictData` seemed simpler and
unlikely to cause any trouble.


The CEK machine (`Language.UntypedPlutusCore.Evaluation.Machine.Cek`) declares the following
types

```
data ExBudgetCategory fun = BTyInst | BApply | BIWrap | BUnwrap | BVar | BBuiltin fun  | BAST
type CekExBudgetState fun = ExBudgetState (ExBudgetCategory fun)
type CekExTally       fun = ExTally       (ExBudgetCategory fun)
```

and an instance of `SpendBudget`:
```
instance (Eq fun, Hashable fun, ToExMemory term) =>
            SpendBudget (CekCarryingM term uni fun) fun (ExBudgetCategory fun) term where
    spendBudget key budget = do
        modifying exBudgetStateTally
                (<> (ExTally (singleton key budget)))
        newBudget <- exBudgetStateBudget <%= (<> budget)
        mode <- asks cekEnvBudgetMode
        case mode of
            Counting -> pure ()
            Restricting resb ->
                when (exceedsBudget resb newBudget) $
                    throwingWithCause _EvaluationError
                        (UserEvaluationError $ CekOutOfExError resb newBudget)
                        Nothing  -- No value available for error
```

The machine runs in a monad containing a `CekBudgetState` object recording
costs.  Note that `spendBudget` updates both `_exBudgetStateTally` and
`_exBudgetStateBudget`: the `modifying` line updates the accumulated
per-operation costs with the costs of the current operation, and the line
`newBudget <- exBudgetStateBudget <%= (<> budget)` adds the cost of the current
operation to the total consumed so far (and returns the updated result for
further use).  Both fields are updated irrespective of
whether we're in `Counting` mode or `Restricting` mode, which may explain why
the figures in [CekProfiling.md](./CekProfiling.md) don't show much difference
between execution times for the two modes.  To attempt to remedy this, it seems
sensible to refactor `spendBudget` so that it's only updating the field relevant
to the current mode:

```
    spendBudget key budget = do
        mode <- asks cekEnvBudgetMode
        case mode of
            Counting -> modifying exBudgetStateTally (<> (ExTally (singleton key budget)))
            Restricting resb -> do
                newBudget <- exBudgetStateBudget <%= (<> budget)
                when (exceedsBudget resb newBudget) $
                    throwingWithCause _EvaluationError
                        (UserEvaluationError $ CekOutOfExError resb newBudget)
                        Nothing
```

This does reduce execution times noticeably in `Restricting` mode (see table
later), but for some reason it reintroduces a memory leak in `Counting` mode:
many of the `nofib` examples fail to complete because they consume large amounts
of memory very quickly.  Changing the code to 

```
    spendBudget key budget = do
        newBudget <- exBudgetStateBudget <%= (<> budget)
        mode <- asks cekEnvBudgetMode
        case mode of
            Counting -> modifying exBudgetStateTally (<> (ExTally (singleton key budget)))
            Restricting resb -> 
                when (exceedsBudget resb newBudget) $
                    throwingWithCause _EvaluationError
                        (UserEvaluationError $ CekOutOfExError resb newBudget)
                        Nothing
```

eliminates the leak again, but it's not clear to me why.  Possibly `modifying`
is accumulating costs lazily and updating `_exBudgetStateBudget` prevents this
for some reason, but I don't understand why that would be the case.

**Update**: thanks to some detective work from @effectfullly, it turns out that
[`modifying`](https://hackage.haskell.org/package/lens-4.19.2/docs/Control-Lens-Combinators.html#v:modifying)
uses the lazy function
[`Control.Modad.State.Lazy.modify`](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-State-Lazy.html#v:modify).
Because of this, `modifying` accumulates costs as chains of unevaluated thunks,
and if these are never forced then we get a leak.  When we use `<%=`, it forces
its first argument (because `_exBudgetStateBudget` is a field of a record of
type `ExBudgetState`, which is strict because of the `StrictData` pragma
mentioned earlier).  This causes any thunks associated with the previous value
to be forced; however, the second argument of `<%=` and both arguments of
`modifying` are created as thunks, and are not forced until the next time
`spendBudget` is appplied.  Thus the code aboves leaks a small amount of memory
every time the method is applied, but it is reclaimed the next time round
and the major leak disappears.  There's some discussion of the underlying
issue [here](https://github.com/ekmett/lens/issues/863).

### Further experiments

I updated the code so that `spendBudget` just operated in `Counting` mode all
the time and didn't have to branch on `mode` every time, and this again produced
noticeable reductions in execution time: see the table below.  The CEK monad
also involves a `Reader` monad which contains the budgeting mode and the table
of builtin functions.  I tried removing the `Reader` monad and threading the
builtins through the machine, but this didn't seem to help (in fact, it may have
slowed things down a bit).


### Benchmark  results

Here's a table of figures for the benchmarks with various refactorings as mentioned
above.  All benchmarks were run in `Restricting` mode (with a large initial limit
(`ExRestrictingBudget (ExBudget 10000000000 10000000000)`)
to make sure that the programs all ran to completion).

* A. Original code

* B. Refactored to separate the updates to `_exBudgetStateBudget` and
     `_exBudgetStateTally` (this is where we get a memory leak in `Counting`
     mode, but that doesn't happen in `Restricting` mode).

* C. Refactored so that `spendBudget` only contains the code relevant
     to `Restricting` mode and doesn't have to consult the `mode` parameter.

All times are in milliseconds.


#### Validation

Benchmark             |     A      |     B      |    C    
----------------------|-----------:|-----------:|--------:
crowdfunding/1        |    6.540   |   4.253    |  3.895
crowdfunding/2        |    6.534   |   4.286    |  3.921
crowdfunding/3        |    6.564   |   4.300    |  3.947
crowdfunding/4        |    3.763   |   2.788    |  2.550
crowdfunding/5        |    3.763   |   2.812    |  2.546
future/1              |    3.870   |   2.606    |  2.366
future/2              |    7.734   |   4.936    |  4.535
future/3              |    7.777   |   4.863    |  4.460
future/4              |    10.42   |   6.815    |  6.233
future/5              |    12.39   |   8.029    |  7.342
future/6              |    10.33   |   6.994    |  6.416
future/7              |    12.42   |   8.063    |  7.302
multisigSM/1          |    7.264   |   5.245    |  4.848
multisigSM/2          |    7.403   |   5.380    |  4.969
multisigSM/3          |    7.494   |   5.435    |  5.015
multisigSM/4          |    7.599   |   5.369    |  5.101
multisigSM/5          |    8.999   |   6.049    |  5.587
multisigSM/6          |    7.231   |   5.229    |  4.892
multisigSM/7          |    7.401   |   5.300    |  4.970
multisigSM/8          |    7.550   |   5.358    |  4.963
multisigSM/9          |    7.619   |   5.304    |  5.045
multisigSM/10         |    9.085   |   6.115    |  5.621
vesting/1             |    6.569   |   4.372    |  3.907
vesting/2             |    5.841   |   3.881    |  3.634
vesting/3             |    6.542   |   4.368    |  3.888
marlowe/trustfund/1   |    21.17   |   14.27    |  13.36
marlowe/trustfund/2   |    16.35   |   11.86    |  10.98
marlowe/zerocoupon/1  |    22.17   |   14.83    |  13.33
marlowe/zerocoupon/2  |    15.06   |   11.10    |  10.33

#### Nofib

Benchmark             |     A      |     B      |    C    
----------------------|-----------:|-----------:|--------:
clausify/formula1     |    345.9   |   152.1    |  123.1  
clausify/formula2     |    427.6   |   189.7    |  153.3  
clausify/formula3     |    1183    |   525.3    |  421.7  
clausify/formula4     |    1562    |   698.9    |  568.4  
clausify/formula5     |    7704    |   3413     |  2717   
knights/4x4           |    882.6   |   397.3    |  337.0  
knights/6x6           |    2771    |   1195     |  1002   
knights/8x8           |    4766    |   2047     |  1712   
primetest/05digits    |    495.9   |   276.2    |  257.4  
primetest/08digits    |    909.0   |   521.7    |  492.0  
primetest/10digits    |    1206    |   755.9    |  714.1  
primetest/20digits    |    2679    |   1565     |  1478   
primetest/30digits    |    3885    |   2287     |  2165   
primetest/40digits    |    5417    |   3224     |  3069   
primetest/50digits    |    5516    |   3435     |  3289   
queens4x4/bt          |    154.0   |   70.10    |  59.75  
queens4x4/bm          |    200.3   |   90.11    |  78.07  
queens4x4/bjbt1       |    184.9   |   83.34    |  70.69  
queens4x4/bjbt2       |    192.3   |   86.33    |  72.96  
queens4x4/fc          |    428.1   |   184.5    |  154.9  
queens5x5/bt          |    2068    |   940.5    |  801.2  
queens5x5/bm          |    2154    |   1020     |  867.6  
queens5x5/bjbt1       |    2373    |   1074     |  907.4  
queens5x5/bjbt2       |    2469    |   1113     |  943.4  
queens5x5/fc          |    5450    |   2364     |  1954


### Suggestions

The results for the validation benchmarks above show that apparently small
changes in the costing code can make quite a large difference to the execution
times.  In column C all of our sample validations are comfortably under the 20ms
budget that's been mentioned in the past (at least on my machine), and some of
the nofib examples are approaching a 3x speedup.

Here are some suggestions about how to speed things up even more:

* Remove the lens operations and make everything explicit: this may make it
  easier to see what's going on and help avoid memory leaks.
* Try to make `Restricting` mode and `Counting` mode completely separate
  so that we don't have to examine the mode every time we want to spend
  some of the budget.  Using a typeclass makes this a bit difficult because
  we can only have one instance per type.  Could we (a) provide two methods,
  one for each mode, or (b) dispense with the `SpendBudget` class altogether
  and pass an accounting function as a parameter to the machine?  The latter would
  avoid overhead due to calling typeclass methods (see [CekProfiling.md](./CekProfiling.md)),
  so might be better.
* In `Restricting` mode, decrement the cost at every step and fail it if goes
  below zero.  It's conceivable that it'd be cheaper to check whether an Integer
  is negative rather than compare two (possibly large) Integers.
* Maybe don't use a monoid to accumulate costs in `Restricting` mode.  Michael
  has suggested using `STRef`s to accumulate costs, but I haven't tried that yet
  because it'd require some monadic re-plumbing.
