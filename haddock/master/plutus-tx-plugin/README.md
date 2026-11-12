# plutus-tx-plugin: Plutus Tx compiler plugin

This contains the Plutus Tx compiler plugin itself. This should
be added as a dependency, but used via the functions in the
`plutus-tx` package.

This is in a separate package because it depends on `ghc`. Packages
which need to be cross-compiled should depend on this conditionally.
Use the following snippet:

.package.cabal
----
if !(impl(ghcjs) || os(ghcjs))
    build-depends: plutus-tx-plugin
----

## Compilation timings

The plugin reports its compilation stages through GHC's own timing mechanism.
Compile with `-ddump-timings` (or `-v2`) and each stage appears among GHC's phases:

```text
Plinth core.pir-optimization [Module:name]: alloc=56683208 time=15.571
```

`alloc` is bytes allocated and `time` is CPU milliseconds, as for GHC's own phases.
`-ddump-to-file` on the command line writes the records to a `.dump-timings` file
instead of stdout (set from an `OPTIONS_GHC` pragma, GHC redirects only its earliest
records). `+RTS -l` records each stage's start and end in the eventlog.

The scope in brackets is the module name. Per-expression stages append `:name` of
the marked variable, or `:expression` when the marked expression is not a
variable, so scopes can repeat. The driver hook runs before any module is known and
uses `<driver>`. A stage that throws prints no record.

| Stage | Work measured |
|---|---|
| `source.driver` | Driver hook updating GHC flags and extensions |
| `source.total` | Typecheck-result hook: the three stages below |
| `source.anchors` | Source-location anchor insertion, when enabled |
| `source.unsupported-markers` | Insertion of markers for unsupported constructs |
| `source.inlineable-pragmas` | Adding missing INLINEABLE pragmas |
| `core.occurrence-analysis` | GHC Core occurrence analysis of the marked expression |
| `core.expr-to-pir` | Translation from GHC Core to PIR |
| `core.pir-optimization` | `compileToReadable`, including PIR optimization |
| `core.pir-to-tplc` | `compileReadableToPlc`, including its internal transformations and checks |
| `core.tplc-typecheck` | Typechecking the resulting typed PLC, when enabled |
| `core.tplc-erasure` | Erasure of typed PLC to UPLC |
| `core.uplc-renaming` | Renaming before UPLC optimization |
| `core.uplc-optimization` | UPLC optimization |
| `core.debruijn` | Conversion to de Bruijn indices |
| `core.finalize-annotations` | Conversion of provenance annotations to source spans |
| `core.serialize-and-embed` | Serialization and construction of GHC byte-string literals |
| `core.certification` | Certificate generation, when enabled |

GHC already times the whole Core pass as `Core plugin:  Core to PLC [Module]`, and
the source stages run inside GHC's `Renamer/typechecker [Module]`. Those totals
contain the Plinth stages, so do not add them up.

### Forcing

Stage results are lazy, so by default some of a stage's work can be done, and
timed, in a later stage that consumes the result. Add
`-fplugin-opt Plinth.Plugin:force-timings` to fully evaluate each `core.*` stage's
result before its timer stops, so work is charged to the stage that produced it.
The extra traversals take time and can change allocation and GC behaviour. Forcing
only happens while timings are on; without `-ddump-timings` the option has no
effect. The source stages are never forced.
