# Patches for the scope-information experiments

Every patch applies **independently** to original CEK commit
`5d9feef021f94c0162c8ddcd6b4ec4780d37a5e5`. Patches include the environment module,
CEK/steppable integration, and Cabal module registration. Do not stack them.
The branch itself leaves production sources at this baseline.

**None of these implementations beats the original CEK on the validation
corpus.** RAList closure erasure (`ra-erased-context`) is not a scope-dependent
optimization and is not included in this array patch catalog. Its separate
results remain in [closure-erasure.md](../closure-erasure.md).

## Implementations and measured outcomes

Positive time changes mean slower. Each measurement covers all 89 validation
scripts in five process rounds, using the equal-script geometric mean of
candidate/baseline ratios. These are CEK measurements with any fixed-array
capacity traversal included. Full scope checking is outside this timed region;
separate scope-plus-CEK results are retained in the reports.

| Patch | Role of scope information | CEK time change | Evidence |
| --- | --- | ---: | --- |
| [compact-checked](compact-checked.patch) | None; exact-length array control with checked reads | +75.75% | [Original comparison](../README.md#array-measurements) |
| [compact-unchecked](compact-unchecked.patch) | Full closedness proof justifies unchecked reads | +75.26% | [Original comparison](../README.md#array-measurements) |
| [fixed-checked](fixed-checked.patch) | Maximum lexical depth sizes copied arrays | +208.51% | [Original comparison](../README.md#array-measurements) |
| [fixed-unchecked](fixed-unchecked.patch) | Same capacity bound plus closedness proof | +208.30% | [Original comparison](../README.md#array-measurements) |
| [fixed-cow-checked](fixed-cow-checked.patch) | Depth-sized buffers, copying when an extension forks | +134.20% | [Original comparison](../README.md#array-measurements) |
| [fixed-cow-unchecked](fixed-cow-unchecked.patch) | Same COW buffers plus closedness proof | +132.79% | [Original comparison](../README.md#array-measurements) |
| [fixed-reuse-checked](fixed-reuse-checked.patch) | Depth-sized buffers with temporary borrow barriers | +88.53% | [First follow-up](../closure-erasure.md#first-comparison) |
| [fixed-reuse-erased](fixed-reuse-erased.patch) | Same buffers plus independent syntactic closure erasure | +106.07% | [First follow-up](../closure-erasure.md#first-comparison) |
| [fixed-reuse-erased-context](fixed-reuse-erased-context.patch) | Same buffers plus independent continuation-based erasure | +98.07%; repeat +87.63% | [First follow-up](../closure-erasure.md#first-comparison), [repeat](../closure-erasure.md#second-comparison-snapshot-on-escape) |
| [fixed-escape-erased-context](fixed-escape-erased-context.patch) | Depth-sized buffers, snapshots for escaping captures, and independent erasure | +252.19% | [Snapshot comparison](../closure-erasure.md#second-comparison-snapshot-on-escape) |

The original, follow-up, and repeat measurements are separate runs. Their
reports preserve uncertainty, allocation, absolute per-script times, and host
conditions; the table does not establish a precise ranking across runs.
No timings were rerun when exporting these patches.

## What was and was not implemented

Fixed variants compute maximum lexical lambda depth in a separate traversal at
evaluator entry. This is scope-related structural information, but it is not
the output of a modified production scope checker. A standalone fused
closedness/capacity analysis is implemented and measured in
[Prep.hs](../experiment/Prep.hs); it is not wired into these evaluators.

Unchecked variants require a successful `checkScope Full` in the experiment
harness. Their raw evaluator APIs do not perform that check. Legacy
`NoCaseConstr` checking is insufficient. The checked variants retain invalid
index handling. Scope information bounds the size of one environment; live
closures can retain several versions, which these array policies must preserve.

Borrowing and erasure variants combine separate mechanisms. Their capacity
comes from lexical depth, while their erasure decision comes from immediate
syntax or continuation use. A gain from erasure alone would not demonstrate
that scope checking pays for itself.

## Apply and reproduce

From this branch, production files already match the recorded baseline:

```bash
git apply --check doc/notes/cek-scope-array/patches/fixed-cow-checked.patch
git apply doc/notes/cek-scope-array/patches/fixed-cow-checked.patch
# Inspect or build this one variant, then undo it before applying another.
git apply --reverse doc/notes/cek-scope-array/patches/fixed-cow-checked.patch
```

For the existing benchmark/test runners, select the variant through their
selector rather than manually applying a patch:

```bash
e=doc/notes/cek-scope-array/experiment
bash "$e/build.sh" fixed-cow-checked
python3 "$e/select-variant.py" baseline
```

See [reproduction instructions](../README.md#reproduction) for the GHC/Cabal
environment, input guard, correctness checks, and full measurement commands.
The full reports and original raw evidence are retained, including regressions.

## Export verification

[manifest.json](manifest.json) records the common baseline, patch hashes,
resulting source hashes, scope information, and erasure policy. Regenerate or
check all ten exports without modifying production files:

```bash
python3 doc/notes/cek-scope-array/experiment/export-patches.py
python3 doc/notes/cek-scope-array/experiment/export-patches.py --check
```

The exporter checks each patch in an isolated directory, applies it, compares
every resulting source file with the original variant generator, and checks
reverse applicability. Previously archived patches for the combined variants
are also applied and checked against the same source. This verifies the exports;
the runtime correctness and performance evidence comes from the recorded runs.
