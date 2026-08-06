# Nested versus shallow Match: CEK wall-time benchmark

This compares recursive nested patterns with their equivalent sequence of shallow patterns. It uses
only `Data.Constr`: `Data.List` has the same field traversal behavior, so duplicating every
topology for both discriminators would add cases without improving the comparison.

This is not a cost-model calibration suite. Criterion reports CEK wall time only.

## Target structure

Every case has one explicit closed argument function and one explicit matcher function. Small
module-level helpers fill one constructor/pattern node and build the repeated capture sum; each
case still declares its own width, tags, child positions, captures, and recursion. There is no
Cartesian suite generator, runtime tree specification, or external term generator.

- `D`: maximum number of nested `Data.Constr` nodes on a root-to-leaf path.
- `W`: exact number of immediate fields in every constructor.
- `C`: number of integer fields captured and summed.
- Nodes have 1-based preorder IDs, visiting children from the lowest field index to the highest.
- Node `n` uses constructor tag `n`.
- At node `n`, an ordinary zero-based field `f` is
  `I ((n - 1) * W + f + 1)`.
- A child at field `f` replaces that integer. A node may have one to four children, placed at
  front, middle, last, or irregular positions.
- Every structural pattern requires exactly `W` fields.
- Every unselected integer field is a plain pattern wildcard; neither implementation inspects
  its `Data` discriminator.
- With one capture the result is returned directly. With `C > 1`, the captures are summed
  with exactly `C - 1` `addInteger` operations.

The following grammar is documentation notation only. Each Haskell `*_arg :: Term` definition
spells out its own layout with a small local fold or local node bindings.

```text
Node(n, W, childrenByField) =
  Constr n [
    childrenByField[f]                         if field f contains a child
    I (((n - 1) * W) + f + 1)                 otherwise
    | f = 0 .. W-1
  ]
```

## Matching pseudo-UPLC

A genuine branch with children at the front and in the middle can look like this:

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

The nested implementation uses one recursive pattern:

```text
lambda arg.
  match arg with
    data-constr 1 exact [
      data-constr 2 exact [wildcard, wildcard, data-i(bind), wildcard],
      data-i(bind),
      data-constr 3 exact [wildcard, data-i(bind), wildcard, wildcard],
      wildcard
    ]
    -> lambda i7 i2 i10.
         addInteger (addInteger (addInteger 0 i7) i2) i10
```

The shallow implementation matches one constructor at a time. Selected scalar fields and every
child are first bound as `Data`; a selected scalar then needs a separate shallow `data-i` match.
Sibling child matches are continuation-nested, so no subtree can be skipped:

```text
lambda arg.
  match arg with
    data-constr 1 exact [bind, bind, bind, wildcard]
    -> lambda child0 d2 child2.
         match child0 with
           data-constr 2 exact [wildcard, wildcard, bind, wildcard]
           -> lambda d7.
                match d7 with data-i(bind) -> lambda i7.
                  match d2 with data-i(bind) -> lambda i2.
                    match child2 with
                      data-constr 3 exact [wildcard, bind, wildcard, wildcard]
                      -> lambda d10.
                           match d10 with data-i(bind) -> lambda i10.
                             addInteger (addInteger (addInteger 0 i7) i2) i10
```

Late-failing alternative cases put the wrong tag only on the final leaf of the first alternative.
For the D=16 spine, the argument ends in `Constr 16 [I 121, I 122, I 123, I 124, ..., I 128]`:

```text
nested:
  match arg with
    Constr 1 [... Constr 2 [... ... Constr 999 [... data-i(bind) ...] ...] ...] -> unreachable
    Constr 1 [... Constr 2 [... ... Constr 16  [... data-i(bind) ...] ...] ...] -> sum captures

shallow:
  match Constr 1; ...; match Constr 15; bind leaf
  match leaf with
    Constr 999 [wildcard, wildcard, wildcard, bind, ...]
      -> lambda d124. match d124 with data-i(bind) -> unreachable
    Constr 16  [wildcard, wildcard, wildcard, bind, ...]
      -> lambda d124. match d124 with data-i(bind) -> sum captures
```

Nested matching retries two complete recursive patterns. Shallow matching traverses the shared
prefix once and keeps the alternatives only at the final leaf.

Both sides therefore validate to the same integer and perform identical explicit arithmetic. The
timing difference comes from recursive pattern traversal versus repeated shallow Match nodes and
their handler applications.

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
that repeats at every level, which the deep spine cases do not exercise. Cases 20-22 measure a
failed first pattern at the literal final field in evaluator traversal order, followed by the
matching alternative on spine, root-fork, and full-tree shapes.

## Measurement and memory isolation

The required `*_arg :: Term` and `*_nested/shallow :: Term` definitions are CAFs. A forced CAF
cannot be reclaimed within that process, so the executable deliberately runs exactly one selected
case:

1. Select one case before constructing the Criterion tree.
2. Fully construct and force `applyTerm matcher argument` in Criterion `env` setup.
3. Run CEK once outside timing and check the exact expected integer.
4. Time only `whnf runCEK appliedTerm`, with `restrictingEnormous` and no emitter.
5. Exit the process before selecting the next case.

`--validate-case` is a separate untimed preflight. It checks the output, serializes only the
matcher function as a UPLC 1.2 ledger script, and asserts the 16,384-byte script,
10,000,000,000-CPU, and 14,000,000-memory limits. Those budget values are validation metadata, not
Criterion measurements or comparison results.

```sh
matching-cpu-runtime --validate-case constr_binary_d3_w16_c8
matching-cpu-runtime --case constr_binary_d3_w16_c8 -L 2 --csv one-case.csv
```

Invoke those commands once per ID returned by `--list-cases`.

## Recorded run

See [`RESULTS.md`](RESULTS.md) for the complete 22-case wall-time comparison and untimed
correctness/protocol-limit preflight measured on 2026-08-06.
