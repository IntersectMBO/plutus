# Scope information and array-backed CEK environments

Research snapshot: 2026-10-08 (America/Chicago). Local baseline:
`IntersectMBO/plutus` commit `5d9feef021f94c0162c8ddcd6b4ec4780d37a5e5`,
branch `sho/scopeCheckOpt`. CIP PR #1278 was open at head
`bd4fca0344a34128963ab242bbfd0ff1983a76c4` when inspected. This note reports
source investigation and design deductions; it contains no new measurements.

The subsequent [experiments](README.md) found no faster scope-dependent
implementation. The RAList closure-erasure result is a separate local CEK
optimization and uses no scope information. [Standalone patches](patches/README.md)
preserve the tested array implementations, including the slower outcomes.

## What the proposal changes

[CIP-0205 as inspected][cip] would retain the scope check for UPLC language
versions 1.0.0 and 1.1.0, and remove it for 1.2.0 onward. Evaluation of a free
variable would charge a `BVar` step and fail with
`OpenTermEvaluatedMachineError`; an unevaluated free variable could remain in a
successful program. The proposal explicitly permits an implementation to run a
scope check for optimization and fall back to a checked evaluator on failure.
It also calls for an equivalence proof for closed terms.

[Wadler's comment, relayed by Krijnen][wadler], asks precisely whether a frame
representation could make scope checking worthwhile. [Krijnen's response][reply]
identifies the current skew-binary representation and earlier array experiments.
The earlier reported 3% scope-check overhead is a benchmark result, not a bound
on a future implementation's benefit. A newer [88-script reproduction][scopebench]
reports approximately 4% improvement for full preparation plus execution, and
22% for preparation alone, on that author's machine. These are historical
measurements, not results from this branch.

## What the current environment actually is

The CEK's `CekValEnv` is a **skew-binary random-access list**, not a conventional
linked list. It is a persistent strict list of complete binary trees. Its
`cons` is worst-case O(1); lookup follows tree sizes and branches and is
O(log n) in environment length. Closures share immutable structure instead of
copying whole environments. The implementation already has a carefully inlined,
continuation-based lookup to avoid intermediate allocations.
Sources: [environment alias and closure constructors][values],
[RAList representation and insertion][ral], [lookup implementation][lookup].

`VLamAbs` and `VDelay` retain the current environment. The continuation frames
for pending arguments, constructors, and cases retain environments too.
Applying a lambda extends its **captured** environment; it does not extend an
arbitrary current global stack. Sources: [closure creation][capture],
[continuation types][contexts], [lambda application][apply].

This persistence requirement is the central constraint on an array experiment.
Replacing the environment with one array whose slots are overwritten on entry
and exit changes semantics when older closures or continuations remain live.
For example, in named pseudocode, `make = λx. λu. x` can be called twice to
produce closures retaining different `x` values; a later call to the first
closure must still observe its original value. This is a deduction from the
capture/application rules above, not a separate claim made by the CIP.

## What scope traversal can and cannot determine

The existing [full check][scope] carries lexical lambda depth `lvl`, requires
`1 <= variableIndex <= lvl`, checks binder index zero, and increments depth at
each lambda. Extending that traversal to return the maximum depth `D` provides
a static upper bound on **each individual environment's logical length** for
ordinary CEK evaluation of that input term from an empty environment.

The bound follows by induction over the CEK transitions: evaluating a subterm
uses its lexical environment; making a closure captures it; applying that
closure adds the one binding belonging to its lambda. `Case` passes constructor
fields through the ordinary application machinery. Repeated calls can construct
many different environments of the same bounded length. They do not increase
the lexical depth of the source lambda. Sources for this deduction:
[full traversal][scope], [capture][capture], [application][apply],
[case return transitions][case].

Consequently:

- `D` does **not** bound the number of live environments, values retained inside
  environments, pending continuation frames, or total allocation. Recursion can
  create arbitrarily many instances of the same lexical frame before the
  execution budget stops it. A fixed array of `D` values is not a bound on the
  entire evaluator's storage.
- Computing `D` does not itself require rejecting free variables: it is a
  syntactic maximum. Well-scopedness is the additional fact that can justify
  omitting variable-lookup bounds checks, assuming correct environment handling.
- Maximum variable index alone is not the required capacity. For example,
  `λx. λy. constant` contains no variable occurrences but the current evaluator
  still creates two bindings when fully applied.
- An array with capacity `D` needs a separate logical length. Checked lookup
  must reject indices above that length, even when they fit in the backing
  allocation. Otherwise an open term can read an uninitialized or stale slot.

These are design deductions from the source transitions, rather than existing
formal proof artifacts. A production optimization needs its own invariant and
validation for the chosen representation.

## Legacy scope checking is insufficient proof

`ScopeCheckMode.NoCaseConstr` deliberately skips the entire `Constr` and `Case`
subtrees, preserving an older bug. `mkTermToEvaluate` selects that mode before
`dijkstraPV`, and `Full` thereafter. Therefore success of the ledger's legacy
scope check cannot authorize unchecked array access and cannot supply the full
maximum-depth bound. Sources: [checker modes][scope], [protocol gating][ledger].

A compatible fast path can do a complete internal traversal and use the old
checked evaluator whenever it fails. It must not start rejecting scripts just
because the stronger internal check fails under legacy protocol semantics.
Likewise, the public [raw CEK entry point][entry] starts evaluation directly and
does not perform scope checking; changing every call to unchecked lookup would
silently change that API's assumptions.

Open-term result comparison also needs care: [issue #7526][discharge] remains
open and describes variable capture while discharging a value. The CIP
acknowledges this separate machinery; it is not on-chain variable lookup.

## Safe array designs worth distinguishing

| Design | Why closures remain valid | Main tradeoff |
| --- | --- | --- |
| Immutable exact-length array per extension | Copy the previous bindings and add the new value; old arrays never change | O(1) lookup, O(n) copying/insertion instead of O(1) persistent cons |
| Fixed-capacity array snapshot per extension | Allocate `D` slots, copy the logical prefix, initialize the new slot | Directly tests scope-derived capacity, but can allocate much more than the logical environment requires |
| Append-only shared buffer with copying on branches | Store logical length and a monotonically increasing written-prefix high-water mark; append only when length equals that mark, otherwise copy into a new buffer | Saves copying along linear extension paths; needs state/lifetime machinery and must never overwrite a published prefix |
| Closure conversion with compact capture arrays | Assign explicit slots to captured free variables and retain the correct frame in each closure | Can reduce retained data, but adds a transformation, rewritten variable addressing, and capture construction |
| Selective global slots plus ordinary local environments | Only bindings proven single-assignment share the global array | Requires analysis stronger than a scope check; has prior experimental precedent |

The first three rows are proposed experimental designs inferred from the
current persistence requirement. In particular, the append-only design is not
permission to freeze an array and continue mutating it through an unsafe alias;
the implementation must obey the chosen array API's lifetime rules and preserve
results/error terms that escape evaluation. Closure conversion and global slots
are more substantial transformations than merely returning a depth from the
scope check; [the original global-array experiment][globals-code] illustrates
that distinction.

A checked-array run and an otherwise identical full-proof/unchecked-array run
would isolate the value of *scope proof* from the value of *array layout*.
Neither should be compared only on variable-lookup microbenchmarks: insertion,
closure retention, allocation, garbage collection, and preparation cost can
dominate the gain.

## Earlier experiments and useful controls

1. **SkewBinarySlab, PR #4506 (merged).** This variant remains in the repository
   and stores either one value or a vector at each tree node. Its source note
   reports faster bulk insertion/lookup workloads but a slowdown on ordinary
   single-binding workloads. Singleton vectors were also slower. The PR did not
   switch the CEK to this environment. Sources: [module design note][slab],
   [PR][slab-pr], [clarification about the CEK][slab-comment]. The existing
   [index-envs benchmark][envbench] compares this variant with SkewBinary,
   RelativizedMap, and another RAList package, including front/back/random
   lookups and mixed insertion workloads.

2. **Global mutable array, PR #4500 (closed, unmerged).** It introduced a
   `SmallMutableArray` for selected global bindings while retaining the local
   RAList. Its `globalifyTerm` transform recognized lambdas intended to be called
   once and introduced a separate addressing convention. The CEK-only benchmark
   explicitly ran the transformation before the timed evaluation. The author
   raised transformation overhead and maintenance concerns; a reviewer asked
   for `validation-full` including the optimization cost. Sources:
   [experimental source and benchmark changes][globals-code],
   [author assessment][globals-author], [full-cost caveat][globals-cost]. These
   results do not establish a gain for replacing every environment with an
   array, or a gain for a pass fused with today's scope checker.

3. **Existing lookup optimization, PR #6663.** [Issue #7368][redundant] points
   to this earlier investigation of up-front scope information. Its conclusion
   concerns the existing tree lookup. It does not prove that a different array
   representation cannot benefit. The modern continuation-based implementation
   should therefore be the baseline, as used by the requested master commit.

4. **Fused decoding and scope checking.** A [previous prototype][fused]
   reported a 6.6% geometric-mean reduction for full validation. This is an
   alternative means of amortizing a necessary traversal, not evidence about
   array environments, and needs independent reproduction before adoption.

For new experiments, include preparation in at least one reported timing and
preserve the same terms, budgets, logs, success/failure behavior, and discharged
results. Include retained sibling closures, delayed values, deep captures,
repeated closure calls, constructor/case paths, zero/oversized free indices, and
legacy accepted open subterms. These cases exercise the invariants identified
above; runtime alone would not establish that the optimization is valid.

[cip]: https://github.com/cardano-foundation/CIPs/blob/bd4fca0344a34128963ab242bbfd0ff1983a76c4/CIP-0205/README.md
[wadler]: https://github.com/cardano-foundation/CIPs/pull/1278#issuecomment-5990188416
[reply]: https://github.com/cardano-foundation/CIPs/pull/1278#issuecomment-6069580762
[scopebench]: https://github.com/IntersectMBO/plutus/issues/7368#issuecomment-6058191207
[values]: https://github.com/IntersectMBO/plutus/blob/5d9feef021f94c0162c8ddcd6b4ec4780d37a5e5/plutus-core/untyped-plutus-core/src/UntypedPlutusCore/Evaluation/Machine/Cek/Internal.hs#L289-L322
[ral]: https://github.com/IntersectMBO/plutus/blob/5d9feef021f94c0162c8ddcd6b4ec4780d37a5e5/plutus-core/index-envs/src/Data/RandomAccessList/SkewBinary.hs#L27-L77
[lookup]: https://github.com/IntersectMBO/plutus/blob/5d9feef021f94c0162c8ddcd6b4ec4780d37a5e5/plutus-core/index-envs/src/Data/RandomAccessList/SkewBinary.hs#L87-L131
[capture]: https://github.com/IntersectMBO/plutus/blob/5d9feef021f94c0162c8ddcd6b4ec4780d37a5e5/plutus-core/untyped-plutus-core/src/UntypedPlutusCore/Evaluation/Machine/Cek/Internal.hs#L833-L856
[contexts]: https://github.com/IntersectMBO/plutus/blob/5d9feef021f94c0162c8ddcd6b4ec4780d37a5e5/plutus-core/untyped-plutus-core/src/UntypedPlutusCore/Evaluation/Machine/Cek/Internal.hs#L719-L745
[apply]: https://github.com/IntersectMBO/plutus/blob/5d9feef021f94c0162c8ddcd6b4ec4780d37a5e5/plutus-core/untyped-plutus-core/src/UntypedPlutusCore/Evaluation/Machine/Cek/Internal.hs#L980-L992
[scope]: https://github.com/IntersectMBO/plutus/blob/5d9feef021f94c0162c8ddcd6b4ec4780d37a5e5/plutus-core/untyped-plutus-core/src/UntypedPlutusCore/Check/Scope.hs#L15-L73
[case]: https://github.com/IntersectMBO/plutus/blob/5d9feef021f94c0162c8ddcd6b4ec4780d37a5e5/plutus-core/untyped-plutus-core/src/UntypedPlutusCore/Evaluation/Machine/Cek/Internal.hs#L916-L950
[ledger]: https://github.com/IntersectMBO/plutus/blob/5d9feef021f94c0162c8ddcd6b4ec4780d37a5e5/plutus-ledger-api/src/PlutusLedgerApi/Common/Eval.hs#L119-L134
[entry]: https://github.com/IntersectMBO/plutus/blob/5d9feef021f94c0162c8ddcd6b4ec4780d37a5e5/plutus-core/untyped-plutus-core/src/UntypedPlutusCore/Evaluation/Machine/Cek/Internal.hs#L1091-L1103
[discharge]: https://github.com/IntersectMBO/plutus/issues/7526
[slab]: https://github.com/IntersectMBO/plutus/blob/5d9feef021f94c0162c8ddcd6b4ec4780d37a5e5/plutus-core/index-envs/src/Data/RandomAccessList/SkewBinarySlab.hs#L25-L54
[slab-pr]: https://github.com/IntersectMBO/plutus/pull/4506
[slab-comment]: https://github.com/IntersectMBO/plutus/pull/4506#issuecomment-1080496343
[envbench]: https://github.com/IntersectMBO/plutus/blob/5d9feef021f94c0162c8ddcd6b4ec4780d37a5e5/plutus-core/index-envs/bench/Main.hs#L24-L94
[globals-code]: https://github.com/IntersectMBO/plutus/pull/4500/files
[globals-author]: https://github.com/IntersectMBO/plutus/pull/4500#issuecomment-1077449555
[globals-cost]: https://github.com/IntersectMBO/plutus/pull/4500#issuecomment-1077456923
[redundant]: https://github.com/IntersectMBO/plutus/issues/7368
[fused]: https://github.com/IntersectMBO/plutus/issues/7368#issuecomment-3686732448
