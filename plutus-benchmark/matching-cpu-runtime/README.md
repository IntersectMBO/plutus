# Nested, shallow, traditional, and `matchDataConstr` matching: CEK wall time

This compares four implementations of the same 22 `Data.Constr` matches:

- one recursive nested `Match` pattern;
- continuation-nested shallow `Match` terms; and
- traditional `UnConstrData`, `Case`, and list builtins, with no `Match` AST; and
- the type-directed `matchDataConstr` builtin returning a `VConstr` directly to `Case`.

`Data.List` traverses fields like `Data.Constr`, so the suite does not duplicate every topology for
both discriminators. This is not cost-model calibration: Criterion reports only CEK wall time.

## Target structure

Every case has one explicit closed argument and one explicit matcher per implementation. Small
helpers fill a constructor or pattern node, but each case declares its own width, tags, child
positions, captures, and recursion. There is no generated Cartesian suite or runtime tree spec.

- `D`: maximum number of nested `Data.Constr` nodes on a root-to-leaf path.
- `W`: exact number of immediate fields in every constructor.
- `C`: number of integer fields captured and summed.
- Nodes have 1-based preorder IDs, visiting children from the lowest field index to the highest.
- Node `n` uses constructor tag `n`.
- At node `n`, an ordinary zero-based field `f` is
  `I ((n - 1) * W + f + 1)`.
- A child at field `f` replaces that integer. Children appear at front, middle, last, and irregular
  positions, including repeated tree branches.
- Every structural pattern requires exactly `W` fields.
- Nested and shallow matching use a plain wildcard for every unselected integer field;
  traditional matching skips it without calling `UnIData`; and `matchDataConstr` omits it from the
  returned constructor captures.
- One capture is returned directly. `C > 1` uses exactly `C - 1` `addInteger` operations; no
  matcher evaluates `addInteger 0 x`.

The notation below abbreviates repeated scalar fields only. Each `*_arg :: Term` still spells out
its own layout with local folds or node bindings.

```text
Node(n, W, childrenByField) =
  Constr n [
    childrenByField[f]                         if field f contains a child
    I (((n - 1) * W) + f + 1)                 otherwise
    | f = 0 .. W-1
  ]
```

## Matching pseudo-UPLC

For example:

```text
argument =
  Constr 1 [
    Constr 2 [I 5, I 6, I 7, I 8],
    I 2,
    Constr 3 [I 9, I 10, I 11, I 12],
    I 4
  ]

captures = [2, 7, 10]
expected = 19
```

Nested matching puts the complete structure in one pattern:

```text
lambda arg.
  match arg with
    Constr 1 exact [
      Constr 2 exact [_, _, I @, _],
      I @,
      Constr 3 exact [_, I @, _, _],
      _
    ] -> lambda i7 i2 i10.
           addInteger (addInteger i7 i2) i10
```

Shallow matching binds immediate `Data` fields, then continues with another `Match` for every
child or selected `I` field:

```text
lambda arg.
  match arg with
    Constr 1 exact [@child2, @d2, @child3, _]
    -> lambda child2 d2 child3.
         match child2 with
           Constr 2 exact [_, _, @d7, _]
           -> lambda d7.
                match d7 with I @ -> lambda i7.
                  match d2 with I @ -> lambda i2.
                    match child3 with
                      Constr 3 exact [_, @d10, _, _]
                      -> lambda d10.
                           match d10 with I @ -> lambda i10.
                             addInteger (addInteger i7 i2) i10
```

Traditional matching directly cases the builtin pair returned by `UnConstrData`, cases the
`EqualsInteger` Bool for the tag, and threads one list cursor through selected fields:

```text
lambda arg.
  case unConstrData arg of
    (tag, fields) ->
      case equalsInteger tag 1 of
        False -> error
        True  ->
          case fields of
            child2 : fields1 -> matchConstr 2 child2 (...)
            []              -> error
```

These are builtin-pair, builtin-Bool, and builtin-list `Case` nodes; they do not use `Match`.

The PLC builtin has type
`forall S. BuiltinRep MatchDataConstr S -> Data -> S`. Its explicit checked representation is a
canonical `ByteString`, indexed by the captured result `TySOP`. The bytes encode the entry count
followed by sorted `(constructor tag, pattern byte length, field selectors)` entries; structural
numbers use canonical unsigned LEB128 and there is no in-band version tag. Every constructor field
has one selector byte: zero skips it and one captures it. The selector count checks exact arity.
Entries for tags that cannot be selected at that match site are omitted.

The witness erases to an ordinary UPLC constant and the result-type instantiation erases to one
`force`. This benchmark constructs that erased UPLC directly, so the force and retained
representation are explicit here:

```text
lambda arg.
  case ((force (builtin matchDataConstr))
          (con bytestring #01010401000000) arg) of
    tag 0 field0 ->
      matchConstr 2 field0 (...)
```

The builtin binary-searches original `Data.Constr` tags, then returns the matched entry's compact
local position. The `Case` therefore has one handler per retained plan entry rather than holes up
to the largest tag. Captures are the selected original fields in source-position order, so this
handler has one lambda rather than `W` lambdas.

For a gap of one to three ignored fields, the cursor advances with repeated `tailList`; a larger
gap uses one `dropList`. A selected field is obtained by a list `Case`, which binds its head and
tail together. A final sentinel field must exist and its tail must case to `Nil`, enforcing exactly
`W` fields. Repeated `tailList`, `dropList`, `unConstrData`, `equalsInteger`, or `unIData` builtin
values are lambda-bound once and reused; a single use stays direct. `addInteger` stays inline at
its exact `C - 1` call sites in all four implementations.

Captures use `UnIData` only after their field is selected. Its decoding expression is substituted
directly into the successful continuation, without an extra capture lambda/application. The
continuation performs the same two additions as the nested and shallow sketches:

```text
addInteger (addInteger i7 i2) i10
```

The three alternative cases place `{B @ | I @}` at the literal final visited field:

```text
argument:    Constr 1 [Constr 2 [...], ..., I terminal]

nested:      match arg with {whole structure ending B @ | whole structure ending I @}
shallow:     match shared prefix; match terminal with {B @ | I @}
traditional: case shared prefix; chooseData terminal {B -> unBData; I -> unIData}
```

Nested matching retries a complete recursive pattern. Shallow matching, traditional matching,
and `matchDataConstr` share the structural prefix and use `ChooseData` only for the scalar alternative.
All four return the same integer and perform identical explicit arithmetic.

## Explicit cases

Child positions are zero-based. Capture lists contain the actual `I q` values.

| # | Case | Topology | D | W | C | Captures | Expected | Purpose |
|---:|---|---|---:|---:|---:|---|---:|---|
| 1 | `constr_flat_d1_w1_c1` | Leaf | 1 | 1 | 1 | `[1]` | 1 | Minimum depth and width |
| 2 | `constr_flat_d1_w16_c4` | Leaf | 1 | 16 | 4 | `[1,6,11,16]` | 34 | Script-context-sized sparse record |
| 3 | `constr_flat_d1_w1000_c1` | Leaf | 1 | 1000 | 1 | `[997]` | 997 | Very wide, one late capture |
| 4 | `constr_flat_d1_w1000_c16` | Leaf | 1 | 1000 | 16 | `[7,61,118,203,277,349,412,508,577,643,711,806,872,931,977,1000]` | 8452 | Very wide, scattered captures |
| 5 | `constr_spine_front_d4_w16_c8` | Child fields `[0,0,0]` | 4 | 16 | 8 | `[2,15,21,28,40,47,51,62]` | 266 | Nested record before ordinary fields |
| 6 | `constr_spine_middle_d4_w16_c8` | Child fields `[8,8,8]` | 4 | 16 | 8 | same as #5 | 266 | Nested record in the middle |
| 7 | `constr_spine_last_d4_w16_c8` | Child fields `[15,15,15]` | 4 | 16 | 8 | same as #5 | 266 | Nested record at the end |
| 8 | `constr_spine_irregular_d4_w16_c8` | Child fields `[3,12,5]` | 4 | 16 | 8 | same as #5 | 266 | Child position changes by layer |
| 9 | `constr_spine_irregular_d8_w8_c8` | Fields `[0,4,7,2,6,1,5]` | 8 | 8 | 8 | `[4,12,20,28,36,44,52,61]` | 257 | Deeper irregular record path |
| 10 | `constr_spine_front_d64_w2_c8` | Front child throughout | 64 | 2 | 8 | `[2,20,38,56,74,92,110,128]` | 520 | Large depth, distributed captures |
| 11 | `constr_spine_zigzag_d100_w2_c10` | Child fields `0,1,0,1,...` | 100 | 2 | 10 | `[2,23,46,67,90,111,134,155,178,199]` | 1005 | Maximum depth and changing position |
| 12 | `constr_binary_d3_w16_c8` | Full binary; children `[0,15]` | 3 | 16 | 8 | `[7,21,40,59,72,88,105,112]` | 504 | Captures across independent siblings |
| 13 | `constr_ternary_d3_w8_c10` | Full ternary; children `[0,4,7]` | 3 | 8 | 10 | `[4,18,30,40,52,61,71,82,94,104]` | 556 | Three-way collection fan-out |
| 14 | `constr_quaternary_d3_w8_c17` | Full quaternary; children `[0,2,5,7]` | 3 | 8 | 17 | `[2,10,20,31,52,58,71,77,92,98,111,117,130,140,151,157,168]` | 1485 | Four subtrees, captures in every branch |
| 15 | `constr_rootfork2_d6_w12_c8` | Root `[2,10]`; branch lengths `[5,3]` | 6 | 12 | 8 | `[1,14,27,40,54,71,74,108]` | 389 | Uneven TxInfo / ScriptInfo-style fork |
| 16 | `constr_rootfork3_d5_w10_c9` | Root `[0,5,9]`; lengths `[4,3,2]` | 5 | 10 | 9 | `[5,11,27,50,52,68,74,83,99]` | 469 | Inputs / outputs / reference-input branches |
| 17 | `constr_rootfork4_d4_w8_c8` | Root `[0,2,5,7]`; lengths `[3,2,1,1]` | 4 | 8 | 8 | `[4,9,21,32,35,47,51,62]` | 261 | Sparse record with four nested fields |
| 18 | `constr_spine_stress_d10_w100_c20` | Fields `[0,50,99,20,80,10,60,30,90]` | 10 | 100 | 20 | `[17,83,117,183,217,283,317,383,417,483,517,583,617,683,717,783,817,883,917,983]` | 10000 | 1000 total field slots |
| 19 | `constr_binary_stress_d8_w8_c32` | Full binary; alternating `[0,7]` / `[2,5]` | 8 | 8 | 32 | Field 3 on the first of every four preorder leaves: `[60,116,...,1948,2004]` | 33024 | Repeated branching through 8 levels and 255 nodes |
| 20 | `constr_alt_spine_d16_w8_c8` | Spine fields `[0,7,2,5,...]`; root field 7 alternatives `{B @ \| I @}` | 16 | 8 | 8 | `[8,28,44,60,76,92,108,128]` | 544 | First pattern fails on the final visited capture |
| 21 | `constr_alt_rootfork3_d5_w10_c9` | Same Data as #16; node 9 field 9 alternatives `{B @ \| I @}` | 5 | 10 | 9 | `[11,14,27,50,52,68,74,83,90]` | 469 | First pattern fails after all three root branches |
| 22 | `constr_alt_binary_d8_w8_c32` | Same Data as #19; node 129 field 7 alternatives `{B @ \| I @}` | 8 | 8 | 32 | `[60,116,...,932,1032,...,1948,1960]` | 33024 | First pattern fails after the full binary tree |

The branching cases model real ScriptContext relationships: V1/V2 have two root children, V3 has
three, while `TxInInfo`, `Address`, interval bounds, `TxOut`, and governance records have
multiple nested siblings. Depth 64/100 and width 1000 are scaling boundaries, not literal current
ledger layouts. Cases 12-14 cover wider fan-out at depth 3; case 19 separately stresses branching
that repeats at every level, which the deep spine cases do not exercise. In cases 20-22, nested
`Match` retries after the literal final field, while shallow `Match` and traditional `ChooseData`
reuse the spine, root-fork, or full-tree prefix.

## Measurement and memory isolation

The required `*_arg :: Term` and `*_nested`, `*_shallow`, `*_traditional`, or `*_matchdataconstr`
matcher definitions are CAFs. A forced CAF cannot be reclaimed within its process, so each
executable invocation runs exactly one implementation and one selected case:

1. Select the case before constructing the Criterion tree; other argument and matcher CAFs remain
   unforced.
2. Generate that case's argument and matcher, construct `applyTerm matcher argument`, and fully
   force it in Criterion `env` setup.
3. Run CEK once outside timing and check the exact expected integer.
4. Time only `whnf runCEK appliedTerm`, with `restrictingEnormous` and no emitter.
5. Exit before selecting another case, releasing its argument and matcher with the process.

`--validate-case` is a separate untimed preflight. It checks the result, serialized script size,
and counting-mode CPU and memory against the protocol limits. Budgets are never Criterion
measurements; they use the embedded builtin and CEK cost models.

```sh
matching-cpu-runtime --validate-case constr_binary_d3_w16_c8
matching-cpu-runtime --case constr_binary_d3_w16_c8 -L 2 --csv one-case.csv
```

Invoke those commands once per ID returned by `--list-cases`.

## Recorded run

See [`RESULTS.md`](RESULTS.md) for the complete four-way, 22-case wall-time comparison, the
2026-08-17 sparse-tag rerun, and the execution-budget comparison. It also records a control run of
the same traditional UPLC under all three historical CEK evaluators.
