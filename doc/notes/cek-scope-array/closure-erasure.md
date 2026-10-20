# Scope-independent closure erasure and reusable array tails

Follow-up to the [original array experiment](README.md), on the same
`sho/scopeCheckOpt` worktree and master commit
`5d9feef021f94c0162c8ddcd6b4ec4780d37a5e5`.

**RAList closure erasure is independent of scope checking.** It follows from
local syntax and CEK continuation frames, not from an up-front scope proof or
capacity analysis. The earlier roughly 5% CEK improvement and 5.8% allocation
reduction below therefore do not demonstrate a scope-checking optimization.

Array borrowing removes some copies, but the tested arrays still lose
substantially to master. Those variants use a maximum lexical depth traversal
to size their buffers; the closure-erasure rules themselves use no scope
information. Combined array variants are available as standalone
[patches](patches/README.md). No scope-dependent variant beats the original CEK.

See the [expanded comparison](comprehensive.md) for the subsequent ten-round
comparison, all native validation benchmarks, full validation including decoding,
and the additional Marlowe, nofib, and force/delay workloads. The measurements
below are the earlier experiments and retain their original protocols.

## First comparison

Continuation-based closure erasure is promising on the existing environment.
It improves the equal-script geometric mean by **4.59%**, with **5.79% less
allocation** summed across the 89 validation scripts. Its process-bootstrap
interval is **2.04%–6.52% faster**. 71 of 89 scripts improve after averaging the
five rounds; individual script ratios range from 0.854× to 1.083× baseline.
Syntactic erasure alone is inconclusive.

Temporary borrowing reduces the original COW overhead, but all tested array
variants in this comparison remain slower on every real script. Small
differences among the new array variants are obscured by process variability.

Five processes per variant, target 50 ms per script; positive time changes mean
slower. Intervals resample paired process rounds on this fixed corpus.

| Variant | CEK time change | 95% process interval | Sum-of-times change | Allocated bytes |
| --- | ---: | ---: | ---: | ---: |
| Original fixed COW | +136.87% | +134.02% to +139.54% | +205.36% | 2.320× |
| Reuse, no erasure | +88.53% | +84.70% to +91.71% | +143.66% | 2.091× |
| Reuse, syntactic erasure | +106.07% | +88.36% to +143.43% | +166.19% | 2.070× |
| Reuse, broader erasure | +98.07% | +89.42% to +114.72% | +154.07% | 2.108× |
| RAList, syntactic erasure | −0.02% | −0.34% to +0.32% | +0.51% | 0.979× |
| RAList, broader erasure | **−4.59%** | **−6.52% to −2.04%** | **−3.87%** | **0.942×** |

The machine is shared: unrelated Lean and Z3 workloads were observed during
this comparison. No other user's processes or affinity settings were changed.
Both wall and process CPU times varied, so the effect is not just scheduling
delay. Raw rounds are retained; the intervals describe the observed process
variation, not a guarantee on other hardware or workloads.

## Second comparison: snapshot on escape

A separate five-round comparison repeats master, RAList erasure, and reusable
arrays, and adds the snapshot-on-escape candidate. It confirms the modest
RAList improvement and the large array regression.

| Variant | CEK time change | 95% process interval | Sum-of-times change | Allocated bytes |
| --- | ---: | ---: | ---: | ---: |
| RAList, broader erasure | **−5.40%** | **−7.00% to −2.87%** | **−4.78%** | **0.942×** |
| Reuse, broader erasure | +87.63% | +86.86% to +88.34% | +140.01% | 2.108× |
| Snapshot on escape, broader erasure | +252.19% | +251.05% to +253.34% | +429.99% | 2.715× |

The RAList binary was rebuilt from the same generated source while building
the canonical benchmark before this second comparison. Both binary hashes are
recorded in `results/closure-environment.json`; its allocation ratio is unchanged.
No instrumented binary was used in either comparison.

Including a full scope pass in both sides, RAList erasure is **6.54% faster**
(process interval 6.08%–7.04%; summed time 5.36% faster). Snapshot-on-escape is
**219.02% slower** (216.97%–221.00%; summed time 369.52% slower). These are
separate five-round measurements, excluding decoding and transaction processing.
They confirm the direction of the result; differences in speedup between these
and CEK-only timings should not be interpreted as an optimization of scope checking.

The repository's independent Criterion `validation --quick` benchmark also
improves on its 14-script subset: paired process-round changes are −4.62%,
−23.24%, and −9.93% (geometric mean −12.96%). The much larger spread, shared-host
activity, and different subset make this corroboration of direction rather
than a reliable estimate of the full-corpus speedup. All raw Criterion rows and
logs are retained, including the unusually large second-round difference.

## Did it actually remove copies?

Yes, but far fewer copies than closures. Separate instrumented binaries count
one execution of each of the 89 real scripts. Every variant performs exactly
422,084 environment extensions. The reusable variants account for the same
532,344 lambda/delay creation events through captures plus erased closures.

| Policy | Erased closures | Prefix copies | Copied slots | Slots versus original COW |
| --- | ---: | ---: | ---: | ---: |
| Original COW | — | 142,678 | 6,045,648 | 1.000× |
| Temporary reuse | 0 | 122,762 | 5,277,921 | 0.873× |
| Reuse + syntactic erasure | 67,797 | 122,524 | 5,271,305 | 0.872× |
| Reuse + broader erasure | 336,034 | 117,389 | 5,080,990 | 0.840× |
| Snapshot on escape + broader erasure | 336,034 | 192,494 | 13,045,673 | 2.158× |

Broader erasure eliminates **63.12%** of the closure-creation events. Together
with borrowing it removes **17.72%** of copies and **15.96%** of copied slots
versus original COW. Relative to temporary reuse alone, broader erasure removes
only another 4.38% of copies. Eliminating a closure allocation does not translate
one-for-one into eliminating a prefix copy.

The broader reusable-array path also performs 788,925 temporary borrows versus
581,890 without erasure. It replaces permanent capture with temporary protection
while arguments run, adding bookkeeping that the RAList version does not need.
These counts identify a plausible source of overhead; they are not a profile
attributing each elapsed-time difference to one operation.

Snapshotting escaping captures is counterproductive here: it increases copy
count by **34.91%** and copied slots by **115.79%**. Moving a copy to closure
creation can pay for captures whose buffers would never have needed to fork.
Its average copied prefix is also longer (67.8 slots versus 42.4 for original
COW). The instrumented binaries are excluded from all performance measurements.

## What was tested

The first copy-on-write prototype never reused a written slot, even after the
computation that needed it had finished. This follow-up distinguishes an active
environment, an environment borrowed by a continuation, and one retained by an
escaping value.

| Variant | Environment | Closure treatment |
| --- | --- | --- |
| `baseline` | Master's skew-binary RAList | Unchanged |
| `fixed-cow-checked` | Original append-only array | Every published prefix remains protected |
| `fixed-reuse-checked` | Fixed array with permanent and temporary barriers | All lambda/delay values capture their environment |
| `fixed-reuse-erased` | Same reusable array | Erase syntactically immediate lambda applications and delay/force pairs |
| `fixed-reuse-erased-context` | Same reusable array | Also erase closures proved to be immediately consumed by their continuation |
| `fixed-escape-erased-context` | Reusable array with snapshots on escaping capture | Same broader erasure; escaping captures copy only if their prefix is not already frozen |
| `ra-erased` | Master's RAList | Syntactic erasure only |
| `ra-erased-context` | Master's RAList | Syntactic and continuation-based erasure |

All reads remain checked. Capacity is still the maximum lexical lambda depth,
computed at evaluator entry for array variants and included in their timings.
The erasure-only RAList variants require no scope analysis or preparation pass.

## Erasure rules

For `Apply (LamAbs body) argument`, the evaluator keeps the environment and body
in a dedicated argument frame rather than allocating a lambda value. For
`Force (Delay body)`, it enters the body directly. Both rules retain the original
machine-step charges in their original order, including slippage checks.

The broader version also examines the continuation when evaluating a lambda or
delay. `FrameAwaitFunTerm`, `FrameAwaitFunConN`, and `FrameAwaitFunValueN` prove
that a freshly created lambda will immediately be applied; `FrameForce` proves
that a delay will immediately be forced. This covers closures produced through
cases, forces, and intermediate stages of multi-argument applications.

An erased lambda waiting for an argument borrows its environment until the
argument finishes. A lambda passed as an argument, stored in a constructor,
handed to a builtin, or returned as a result still captures a stable environment.
This is a local evaluator optimization, not a whole-program escape analysis or
a UPLC rewrite that changes execution costs.

## Array invariants

Each buffer has two barriers: the highest prefix permanently captured by a
value, and the highest prefix currently borrowed by a continuation. Extending
an environment of length `n` may write slot `n` only when both barriers are at
most `n`. Otherwise it copies the prefix to a fresh buffer. This lets a later
call reuse a dead tail without changing any live prefix.

Continuation borrows are nested. Each saved environment remembers the previous
temporary barrier, which is restored when its frame is consumed. Permanent
capture is tracked separately, so restoring an older temporary barrier cannot
erase a capture made while that borrow was live. Argument, constructor-field,
and case continuations all participate. Reads of active environments execute
in the evaluator monad before subsequent writes.

The snapshot-on-escape policy changes the permanent-capture rule: an escaping
closure receives a fresh buffer containing its prefix unless that prefix is
already frozen. The original active buffer remains reusable. Captured buffers
also reserve the scope-derived capacity, allowing repeated calls to reuse their
own uncaptured tails. This trades copies on later calls for copies at capture.

The persistent `cons` fallback always copies and freezes, so the steppable
evaluator and existing persistent-environment clients retain their semantics.
Only the sequential CEK engine calls the explicit borrowing/mutation API.

These remain prototypes. The array representation uses `RealWorld` through an
ST bridge to fit the existing public `CekValue` type. A production design should
thread the evaluator's state type and hide the ownership API. Neither policy
reclaims captured prefixes when their last closure dies; invisible suffixes can
retain values. The tests are regression evidence, not a formal lifetime proof.

## Correctness checks

The differential harness compares full discharged results, errors and their
causes, execution budgets, and logs. Besides the original 89 validation scripts
and 14 synthetic cases, `ClosureChecks.hs` adds 11 focused cases and 256
deterministically generated, scoped integer-producing programs. It evaluates
these 267 cases in counting mode and at five CPU-budget limits (1,602 reports).
Two focused cases intentionally contain invalid indices to test error behavior.

All six new variants match master byte-for-byte on both the original 103-case
output and all 1,602 expanded reports. The results include fully discharged
returned closures, delays, constructors, and error causes; timing alone would
not have checked these lazy results.

All **919 upstream untyped-core tests** pass separately for RAList broader
erasure, reusable arrays with syntactic erasure, reusable arrays with broader
erasure, and snapshot-on-escape with broader erasure. Baseline's full suite was
already run in the original experiment. Python syntax checks, shell syntax
checks, and patch-application checks also pass.

Cases include nested argument evaluation, closures made during argument
evaluation, closures retained by partially applied polymorphic builtins,
constructor fields, repeated forcing, returned closures and delays, trace order,
and error causes. There are also 64 concurrent evaluations of shared ASTs,
the original persistent-prefix/concurrent-fork checks, and 2,000 mutable-tail
iterations with nested borrows and surviving captured prefixes.

The evaluator is restored to the recorded master. This branch retains
experiment templates, runners, patches, and evidence; no experimental evaluator
is enabled by default.

## Reproduction

Use the same GHC 9.6.7/Cabal development environment and local package settings
as the original experiment. From the worktree root:

```bash
e=doc/notes/cek-scope-array/experiment
bash "$e/build.sh" fixed-reuse-erased-context
bash "$e/build-closure-checks.sh"
# Select and build the other variants in the table likewise.
python3 "$e/run-matrix.py" --prefix closure --rounds 5 --seconds .05 \
  --variants baseline fixed-cow-checked fixed-reuse-checked \
  fixed-reuse-erased fixed-reuse-erased-context ra-erased ra-erased-context
python3 "$e/analyze.py" --prefix closure-cek --output closure-summary
# Separate instrumented builds: NEVER use these for timing.
bash "$e/build-closure-stats.sh" fixed-reuse-erased-context
python3 "$e/select-variant.py" baseline
```

`summarize-closure-counts.py` recomputes the copy counters and canonical summary
after all five instrumented variants and all three Criterion pairs have run.
`analyze.py --prefix escape-cek --output escape-summary` and
`analyze.py --prefix closure-pipeline-full --group scope+cek/ --output closure-pipeline-summary`
recompute the remaining timing summaries.

`closure-variants.py` contains the evaluator edits; `ReuseEnv.hs` contains the
borrowing implementation; `escape-env.py` supplies the alternative capture
policy. The selector always derives production source from the recorded master
commit and refuses to overwrite unrelated edits.

Focused patches are also saved as `results/ra-erased-context.patch.gz`,
`results/fixed-reuse-erased-context.patch.gz`, and
`results/fixed-escape-erased-context.patch.gz`. All three pass `git apply --check`
against the recorded master. The RAList patch is 74 lines of unified diff and
changes only `Cek/Internal.hs`. For example, on a clean checkout of that commit:

```bash
gzip -cd doc/notes/cek-scope-array/results/ra-erased-context.patch.gz | git apply
```

The follow-up comparison and full-pipeline checks can be reproduced after
building their uninstrumented binaries:

```bash
python3 "$e/run-matrix.py" --prefix escape --rounds 5 --seconds .05 \
  --variants baseline ra-erased-context fixed-escape-erased-context fixed-reuse-erased-context
python3 "$e/run-matrix.py" --prefix closure-pipeline --group full --rounds 5 --seconds .03 \
  --variants baseline ra-erased-context fixed-escape-erased-context
SCOPE_BUILD_CANONICAL=1 bash "$e/build.sh" ra-erased-context
bash "$e/run-closure-criterion.sh"
python3 "$e/select-variant.py" baseline
```
