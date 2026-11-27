# generate-conformance-tests

Exports UPLC programs from the builtin property tests, together with their
expected evaluation results and execution budgets, in the layout read by the
[`plutus-conformance`](../../../plutus-conformance) harness.

## Where the cases come from

The builtin property tests (integer arithmetic, bitwise operations, BLS12-381)
each describe their properties as values that can be sampled: a stable
identifier, a display name, and a generator of inputs. This tool samples those
generators, builds the UPLC program for each sampled input, and evaluates it
with the reference implementation to record the expected result and budget.

For the integer and BLS12-381 properties the normal Tasty tests are built from
the same list of `PropertySpec`s, so each property is defined once. The bitwise
properties are listed in the same form for this tool, but their Tasty tests are
still constructed separately (see the `TODO`s in the `Bitwise` modules).

Before a case is written it is checked against the property it came from; see
[What the cases record](#what-the-cases-record).

## Usage

```console
$ cabal run generate-conformance-tests -- --output-dir /tmp/cases --num-files 50
```

```
Usage: generate-conformance-tests [-o|--output-dir DIR] [-n|--num-files N]
                                  [-s|--seed INT] [--format flat|uplc|both]
                                  [-m|--match TEXT] [--list] [--clean]
                                  [--force] [--full-check]
```

| Option | Meaning |
| --- | --- |
| `-o`, `--output-dir` | Root of the output tree. Defaults to `conformance-property-tests`. |
| `-n`, `--num-files` | Numbered cases per property (not sampled inputs). Defaults to 200. |
| `-s`, `--seed` | QuickCheck seed for reproducible inputs. Omit for a fresh seed, which is recorded in `info.json`. |
| `--format` | `flat` (default), `uplc`, or `both`. Each format gets its own expected-result file. |
| `-m`, `--match` | Case-sensitive substring of `TYPE/MODULE/[GROUP/]PROPERTY`. Repeatable; matches any of them. |
| `--list` | Print the matching property paths without writing anything. |
| `--clean` | Remove existing cases before generating: those of the selected properties, or, with no `--match`, every directory this tool writes (`integer/`, `bitwise/`, `bls12_381/`). Other files in the output directory are never removed. |
| `--force` | Write into a non-empty output directory anyway. |
| `--full-check` | Check each case against its property with the typechecking evaluator the normal tests use, instead of the untyped CEK machine. Much slower; see [What the cases record](#what-the-cases-record). |

The output path must either not exist or be a directory. The tool refuses to
write into a directory that already contains anything, because cases are only
ever overwritten by name and stale or unrelated files would silently survive
alongside the new ones. Pass `--force` to write into a non-empty directory.
`--clean` does not imply `--force`: it only removes the selected properties'
directories once writing is allowed. Even a full `--clean` removes only the
directories this tool writes, so unrelated files in the output directory are
left alone. `--list` never writes, so it ignores this check.

## Output layout

```text
DIR/info.json
DIR/integer/RingProperties/addition_associative/
    addition_associative-00001-A/
        addition_associative-00001-A.flat
        addition_associative-00001-A.flat.expected
        addition_associative-00001-A.budget.expected
    addition_associative-00001-B/
        ...
```

Case numbers are zero-padded to five digits. Checks that compare two programs
emit both, numbered together with `-A`/`-B` suffixes. The budget file is
always `<case>.budget.expected`, independent of the input format, matching the
harness convention.

## Test counts

`--num-files` is the same for every property and applies only to generated
cases. The Tasty suite is unaffected: each internal property keeps its own
QuickCheck or Hedgehog limit, which ranges from 1 to 400 depending on the
property (for example 100, 200 or 400 for the integer properties, 50 to 99 for
the bitwise ones, and 1, 99 or 200 for the BLS12-381 ones). This is intentional:
the generated cases are meant to be a reproducible sample at a chosen size, not
a copy of the test-runner settings.

`--num-files` counts numbered cases, not sampled inputs. An equality check
(`CheckEq`) puts two programs in one numbered case, with `-A`/`-B` suffixes.
A check that combines several terms, such as `CheckBoth` (used by the bitwise
`getSet` property), contributes one numbered case per term: the two checks on a
single sampled input become consecutive cases such as `getSet-00001` and
`getSet-00002`, and the numbering carries no record of which sample they belong
to. Such a property therefore consumes several numbers per sampled input and
produces fewer samples for a given `--num-files`. It also means that an odd or
small `--num-files` can write only part of a sample's case set. The number of
programs on disk is therefore not simply `--num-files` times the number of
properties.

## Info file

Each successful run writes `info.json` at the root of the output directory.
It is removed at the start of a run and written last, through a temporary file,
so its presence means the run completed.

- `tool.name`, `tool.version` — the generator and the Plutus version it was
  built from. Versions correspond to release tags, so the version identifies the
  state of the repository the tool and its cost model came from.
- `generatedAt` — UTC timestamp.
- `options` — the effective format, `--num-files`, seed, `--match` filters,
  whether `--clean` was used, and the check mode (`fast` or `full`). A seed is
  always recorded, even when none was supplied, so any run can be repeated
  exactly with `--seed`.
- `completeTree` — true only when the run was unfiltered, the directory was
  empty or was cleaned beforehand, and nothing other than this tool's own
  output is in it, that is, when the directory contains exactly this run's
  cases.
- `costModel` — the full cost-model parameter map used to compute budgets.
- `totals` — overall counts of properties, numbered cases, programs and
  files.

The info file describes the run that wrote it, not necessarily everything in
the directory: with `--force` but without `--clean`, cases from earlier runs
may still be present, in which case `completeTree` is false.

## What the cases record

Each case records a program, its expected result and its budget, matching the
checked-in goldens. Checks that relate several programs are not represented:
for example the BLS hash-collision check becomes a set of programs that are each
compared with their recorded results, not a re-check that the results are
distinct. The same applies to other relational checks.

Before a case is written it is checked against the property it came from. If
the reference implementation does not satisfy the property for a sampled input,
generation stops at that case rather than recording behaviour that contradicts
the property as the expected result. The error names the property, the case
number, the property's description and what went wrong (for example, the two
results that an equality check produced), and the tool warns that the generated
test cases are incomplete. Cases written before the failure are left in place
and no `info.json` is produced; rerunning into the same directory needs
`--force` or `--clean`.

There are two ways of doing this check:

- By default the terms are evaluated with the untyped CEK machine, the same
  evaluation that records the expected results. This is fast and confirms that
  the reference implementation satisfies the property, but it does not typecheck
  the generated terms.
- With `--full-check` the check typechecks the terms, then evaluates them with
  exactly the evaluator the normal tests use, building a fresh typed evaluator
  for every case. A term that does not typecheck therefore stops generation. That
  setup dominates for small terms: for 5,000 cases of a simple integer property,
  generation takes about 0.4 s by default and about 7 s with `--full-check`.

In either mode the recorded expected result and budget come from the untyped CEK
machine; the check only decides whether a case is acceptable. The mode used is
recorded in `info.json`.

## Cost

The number of cases is the same for every property, so properties whose cases
are expensive take longer: the BLS12-381 hash-collision checks hash 200 messages
in every case, whereas the normal tests run them once. At the defaults a full
run (188 properties, `--num-files 200`) takes roughly 13 s on one core with the
default check and roughly 50 s with `--full-check`. Use `--match` to select a
subset, or a smaller `-n`. Properties are generated one after another and
nothing is parallelised.

## Reproducibility and size

With a fixed `--seed` the inputs and therefore the files are reproducible on a
given revision. The seed actually used is recorded in the info file. Each
property draws from its own random stream, derived from the seed and the
property's identifier, so different properties get independent inputs and the
cases for a property do not depend on which others were selected with `--match`.
Different seeds produce different cases, so the output is regenerable rather
than a fixed corpus: do not commit it, and write it outside the repository or to
a temporary directory.

As a guide, at the defaults (188 properties, `-n 200`, Flat only) the output is
about 51,800 programs in 155,400 files across about 52,000 directories. The
files hold only about 30 MB of data, but because they are so small the output
occupies roughly 620 MB on a typical filesystem. Generation time is proportional
to `-n`; one unit is about 259 programs. Cases are written as they are produced,
so memory use does not grow with `-n`.

## Cost model

Budgets are recorded with the same default testing parameters the harness uses
(`defaultCekParametersForTesting` / `defaultCostModelParamsForTesting`). If the
cost model changes, regenerate the cases rather than editing the budget files.

## Checking the output

```console
$ cabal test generated-conformance-cases-roundtrip
```

generates a small sample, using both check modes, and runs it through the
harness's own discovery and golden comparison in both textual and Flat formats.
It also checks that `info.json` is consistent with the files written. That is
the quickest way to check that this tool and the harness still agree on
encodings, expected-result files, failure markers, budgets and the info file.

## Adding a property

For the integer and BLS12-381 properties, add an entry to the relevant
`PropertySpec` list in
`plutus-core/untyped-plutus-core/testlib/Evaluation/Builtins/`; it becomes both a
Tasty test and a generated case. For the bitwise properties, add an entry to the
`conformanceProperties` list for the generator and also add the corresponding
test in `Definition.hs`, since those are not yet derived from the same list.
Keep identifiers unique within a suite: duplicates are rejected by the generator
because they would write cases to the same directories.
