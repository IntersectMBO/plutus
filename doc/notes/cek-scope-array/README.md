# Scope-derived CEK environment experiments

Experiment date: 2026-10-08, America/Chicago. Worktree:
`/home/sho/io/plutus-scopeCheckOpt`; branch: `sho/scopeCheckOpt`.
All variants start from freshly fetched `origin/master`,
`5d9feef021f94c0162c8ddcd6b4ec4780d37a5e5`.

This investigates the array/frame question in
[CIP PR #1278](https://github.com/cardano-foundation/CIPs/pull/1278).
The accompanying [source investigation](research.md) explains the proposal,
previous experiments, and the environment invariants.

## Result

**No tested scope-dependent implementation beats the original CEK.**
The fixed-capacity, copying, borrowing, and snapshotting array experiments all
lose on the validation corpus. The current evaluator on this branch is the
recorded master implementation; experiments are retained as source templates,
[independently applicable patches](patches/README.md), runners, and raw evidence.

`ra-erased-context` is **not a scope-checking optimization**. It uses local
syntax and CEK continuation frames to avoid allocating closures that will be
immediately consumed. It needs neither a closedness proof nor a scope-derived
capacity, and does not change scope checking. Its performance results do not
answer the original question about making scope checking useful for evaluation.

The [closure-erasure follow-up](closure-erasure.md) records that independent
optimization and its combinations with reusable arrays. The combined array
variants still regress; removing closure wrappers did not make the tested
scope-derived arrays faster than master.

The [expanded performance comparison](comprehensive.md) covers all 89 validation
scripts, their full deserialization/evaluation path, 200 Marlowe transaction
cases, 22 nofib inputs, and 16 force/delay inputs. It includes per-workload time,
allocation, GC measurements, and complete native Criterion cross-checks.
It also records native process variability and confirmed per-script regressions;
the paired-harness average is not an established production performance gain,
and is not evidence of a benefit from scope checking.

## What depends on scope information

| Experiment | Information used | Where it is obtained |
| --- | --- | --- |
| Checked compact arrays | None; representation control | Allocate exactly the current length on extension |
| Unchecked compact arrays | Proof that the input is closed | The harness runs `checkScope Full` before evaluation |
| Fixed arrays, including COW/reuse/snapshot variants | Maximum lexical lambda depth | A separate `maxDepth` traversal at evaluator entry, included in timing |
| Unchecked fixed arrays | Both the depth bound and closedness | Depth traversal plus the harness's full scope check |
| Scope-and-capacity analysis | Closedness and maximum lexical depth in one traversal | Standalone `Prep.hs` experiment, measured separately |
| RAList closure erasure | Local syntax and immediate continuation | The CEK machine itself; no scope information |

The fixed-array experiments do **not** integrate the fused scope-and-capacity
prototype into the production scope checker. They test the environment layouts
using a separate capacity traversal. Full checking is a precondition of the
unchecked experiments; the raw patched evaluator does not enforce that check.

## Array measurements

Scope traversal can determine the required capacity of an individual environment, but none of the tested array layouts improves validation performance. Every array variant is slower on every one of the 89 real scripts after averaging the five runs. Keep the current skew-binary environment on this evidence. This does not rule out closure conversion, smaller selectively captured frames, or a different persistent-array design.

Five independent processes per variant, all 89 validation scripts; positive percentages mean slower. The confidence interval resamples paired process rounds. Allocation is the ratio of summed bytes per evaluation.

| Environment | CEK time change | 95% process interval | Sum-of-times change | Allocated bytes |
| --- | ---: | ---: | ---: | ---: |
| Compact, checked | +75.75% | +74.40% to +77.04% | +91.33% | 1.93× |
| Compact, unchecked | +75.26% | +73.78% to +76.19% | +90.87% | 1.93× |
| Fixed capacity, checked | +208.51% | +205.09% to +210.75% | +286.61% | 3.96× |
| Fixed capacity, unchecked | +208.30% | +205.97% to +210.29% | +286.52% | 3.96× |
| Fixed COW, checked | +134.20% | +131.97% to +136.01% | +204.12% | 2.32× |
| Fixed COW, unchecked | +132.79% | +130.85% to +134.40% | +201.48% | 2.32× |

The repository’s independent Criterion `validation --quick` benchmark corroborates this: compact checked arrays are **73.0% slower** across 14 scripts and three paired process rounds (individual round changes: +72.6%, +75.0%, +71.5%).

Including the full scope pass in both runs, compact unchecked arrays remain **68.67% slower** (95% process interval: 68.01%–69.47%; sum-of-times increase: 83.63%). Thus the evaluation-only conclusion survives accounting for the preparation needed to justify unchecked reads. These timings exclude decoding and transaction processing.

Isolating lookup bounds checks within the same layout gives only a **0.28%** speedup for compact arrays (interval −0.60% to +0.04% elapsed-time change, inconclusive) and a **0.60%** speedup for COW (interval −1.02% to −0.30%). That is much smaller than the environment-representation regression.

Arrays do improve a deliberately lookup-heavy example: at depth 256 with 4,096 reads of the oldest binding, compact checked arrays are **6.1% faster**. But extending an environment to depth 256 is **4.09× slower**, and repeated reads of the newest binding are **30.4% slower** in that prototype. Cheap deep lookup alone does not predict validator performance.

Copying and additional allocation outweigh the lookup advantage in these prototypes. COW lowers allocation from 3.96× to 2.32× baseline compared with full-capacity snapshots, but remains slower than compact copying. It also adds a high-water mark, an ownership claim, mutable-buffer operations, and retains written suffix slots even through shorter logical prefixes.

## Cost of obtaining capacity

The full scope pass takes a median **10.4 µs** per script. A direct recursive
scope-and-maximum-depth prototype takes **26.7 µs**; its maximum must be forced,
otherwise timing only the outer `Right` constructor undercounts the work.
Threading a strict high-water accumulator, updated only at lambdas, reduces
that median to **15.7 µs**. The latter is 43.6% slower than ordinary scope checking
by equal-script geometric mean, or 38.3% by summed pass times.

Combining separately measured component times estimates a 5.64% scope-pass
share of scope-plus-CEK time for this corpus. Replacing it with the strict
capacity-producing pass would add about 2.16% to that sum before changing the
environment. These are component estimates, not full transaction-validation
measurements. The capacity pass is a standalone prototype; it is not fused into
the evaluator entry point used by the array variants. Fixed variants instead
include their own maximum-depth traversal in the timed evaluation.

## Correctness

- All six array variants exactly match baseline results, fully discharged values, execution budgets, and logs on all 89 real scripts and 14 synthetic inputs.
- Baseline, compact checked, and COW checked each pass all **919 upstream untyped-core tests**, including open-term and discharge behavior. Unchecked variants are exercised only through the full-scope-guarded corpus harness.
- Every array layout passes retained-prefix tests, 2,000 branch extensions, invalid indices 0/length+1/maxBound, and 64 concurrently forced sibling branches.
- Scope regressions distinguish full checking from legacy accepted open constructor subterms; unused binders contribute to the capacity bound.
- The fixed-capacity overflow guard does not fire on the corpus. This is experimental confirmation of the source-derived bound, not a formal proof.

Production sources match the recorded master. Select an experiment explicitly
with `experiment/select-variant.py`, then select `baseline` to restore the
original evaluator. The [patch catalog](patches/README.md) includes ten complete
array variants, each independently applicable to the same baseline.

## Question and implementation

A full scope traversal can calculate maximum lexical lambda depth `D`. This
bounds one CEK environment's length, including unused binders. It does not bound
the number of simultaneously live environments. The 89 validation scripts have
maximum depths between 46 and 292 (median 129).

Current master uses a persistent skew-binary random-access list: O(1) extension,
O(log n) lookup. Lambdas, delays, and continuation frames retain older versions.
The experiments preserve those versions in three ways:

- **Compact:** an immutable `SmallArray` containing exactly the live bindings;
  extension allocates `n+1` slots and copies `n` bindings.
- **Fixed:** every extension allocates `D` slots and copies the live prefix.
- **Fixed COW:** an append-only `D`-slot mutable buffer plus logical length and
  a high-water mark. An extension claims an unused slot; extending an older
  prefix copies it into a fresh buffer. Published prefix slots are never changed.

Each layout has checked and unchecked lookup variants. Unchecked evaluation is
used only after the harness's independent `checkScope Full` succeeds. Discharge
and the steppable evaluator retain checked lookup. The legacy `NoCaseConstr`
checker is insufficient authorization for unchecked reads.

The COW hot path performs updates through `CekM` using `unsafeIOToST`; its
`RealWorld` array and pure read wrapper fit the current public `CekValue` type.
It also has a pure extension wrapper for the steppable evaluator and standalone
representation tests. This is an experimental bridge, not a production state
abstraction. A production version should thread the evaluator's state type.

## Measurement protocol

- GHC 9.6.7, Cabal 3.12.1.0; evaluator at Cabal's default `-O1`, harness `-O2`.
- Full crypto enabled. Optional R and certification components disabled.
- AMD Ryzen 9 7950X, Linux, CPU 15 affinity, RTS `-N1`; SMT sibling 31.
  Existing `powersave` governor and desktop workloads retained.
- All 89 repository validation scripts, plus 14 synthetic inputs covering
  retained closures/delays, case capture, returned values, depths 8/64/256,
  near/far lookups, and extension-heavy evaluation.
- Identical production machine-parameter construction, builtin semantics E,
  restricting budgeting, and no logging in timed evaluation. Correctness uses
  counting budgeting, logs, and fully rendered/discharged results.
- Decoding, forcing the input AST, constructing machine parameters, and the
  mandatory full input-scope proof are outside CEK-only timings. Fixed variants
  compute maximum depth inside every evaluation; that traversal is included.
- Separate measurements cover full scope checking plus evaluation, the existing
  full scope pass, and a prototype fused scope-and-capacity pass. No timing here
  includes transaction processing or Flat deserialization.
- Inputs are read from an `IORef` each iteration to prevent sharing the result
  of pure evaluation across repetitions. RTS allocation deltas are measured
  across a forced collection; timed intervals include ordinary evaluator GC.
- Saved binaries run in rotated/reversed order, with independent calibration
  per process. No experiment builds/tests overlap the measurement matrix.
- Aggregate time is an equal-script geometric mean. Also report the ratio of
  summed per-script times and per-evaluation allocated bytes. Confidence
  intervals resample paired process rounds over this fixed corpus; they do not
  claim representativeness of all deployed scripts.

The corpus consists of historical validation scripts, not a survey of current
mainnet transactions. Compiler versions and optimization levels can change CEK
code generation. These experiments are evidence about these implementations and
this corpus, not a proof that every array or closure-conversion design loses.

## Reproduction

From this worktree, enter the repository's GHC 9.6 development shell. The optional
[local Cabal configuration](experiment/cabal.project.local.example) records the
configuration used here, including source-package constraints needed to resolve
the restored Nix package environment. Build at the recorded baseline commit.

```sh
experiment=doc/notes/cek-scope-array/experiment
bash "$experiment/build.sh" baseline
for variant in compact-checked compact-unchecked fixed-checked fixed-unchecked fixed-cow-checked fixed-cow-unchecked; do
  bash "$experiment/build.sh" "$variant"
done
bash "$experiment/build.sh" baseline
python3 "$experiment/run-matrix.py" --rounds 5 --seconds 0.05
python3 "$experiment/analyze.py"
bash "$experiment/run-preparation.sh"
python3 "$experiment/run-matrix.py" --rounds 5 --seconds 0.03 \
  --variants baseline compact-unchecked --group full --prefix pipeline
python3 "$experiment/analyze.py" --prefix pipeline-full --group scope+cek/ --output pipeline-summary
bash "$experiment/run-criterion.sh"
```

`build.sh` compares results, budgets, and logs to the checked-in baseline output
and runs representation tests for each array. It saves distinct binaries under
`experiment/bin`. Set `SCOPE_BUILD_CANONICAL=1` to additionally build/copy the
repository's `validation` Criterion executable for any variant. The selector
refuses to overwrite unrelated source edits. Selecting `baseline` restores all
production sources; the experiment remains under this note directory.

Unchecked variants intentionally change the raw evaluator's input precondition.
Use the guarded harness on fully scoped inputs; do not use those generated
source trees as general-purpose evaluators or run open-term tests on them.

## Evidence files

Text evidence uses normalized LF line endings and trimmed trailing whitespace.

- `results/summary.json` and `summary-per-script.csv`: primary comparisons.
- `results/matrix-cek-*.csv`, `.rts.txt`, and command manifest: five complete
  process repetitions, allocation statistics, and exact invocation order.
- `results/pipeline-full-*.csv`: scope checking included in both evaluators.
- `results/preparation-r*.csv`: fully forced scope/capacity measurements;
  `Prep.hs` includes the strict-accumulator alternative.
- `results/criterion-*.csv` and `.log`: independent repository benchmark runs.
- `results/check-baseline.tsv.gz`, `correctness-summary.json`, and compressed
  upstream test/build logs: expected outputs and validation evidence.
- `results/environment.json` and `binary-sha256.txt`: build/run provenance.
- `results/evaluation-harness.hs.gz`: source of the measured evaluation
  binaries. The current harness also forces the payload in its unused capacity
  diagnostic; timed evaluation actions are unchanged. For an exact source
  replay, decompress this snapshot and set `SCOPE_BENCH_SOURCE` when building.

The recorded process maximum residency is approximately 25.2 MB for baseline
and copied arrays and 25.6 MB for COW. The runner retains all decoded input ASTs,
so these process-wide values do not isolate closure-environment residency.
Per-evaluation allocation, reported above, is the more informative measure here.
