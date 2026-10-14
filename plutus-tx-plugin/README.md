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

`-fplugin-opt Plinth.Plugin:dump-timings` prints the wall-clock and CPU time of
each compilation stage to stderr. It is off by default.

Each stage that completes writes one tab-separated line:

```text
PLINTH_TIMING<TAB>scope<TAB>stage<TAB>wall_nanoseconds<TAB>cpu_picoseconds
```

Wall time comes from a monotonic clock; CPU time is process CPU time. `scope` is
the module name. Per-expression stages append `:name` of the marked variable, or
`:expression` when the marked expression is not a variable, so scopes can repeat.
The driver hook runs before any module is known and uses `<driver>`. A stage that
throws prints nothing, so check the compiler's exit status before using the output.

| Stage | Work measured |
|---|---|
| `source.driver` | Driver hook updating GHC flags and extensions |
| `source.total` | Typecheck-result hook: the three stages below, plus the input traversal when forcing is on |
| `source.anchors` | Source-location anchor insertion, when enabled |
| `source.unsupported-markers` | Insertion of markers for unsupported constructs |
| `source.inlineable-pragmas` | Adding missing INLINEABLE pragmas |
| `core.total` | Complete Core-to-PLC plugin pass, including setup and all marked expressions |
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

### Forcing

By default each stage fully evaluates its result before its timer stops, so lazy
work is charged to the stage that produced it rather than to the first stage that
consumes it. These extra traversals take time and can change allocation and GC
behaviour. Add `-fplugin-opt Plinth.Plugin:no-force-timings` to skip them: totals
then carry less overhead, but a stage's time may include work deferred from an
earlier stage, and work deferred past the end of a hook is missing from that
hook's total. `force-timings` restores the default; neither option does anything
without `dump-timings`.

Source stages force only the typechecked bindings (`tcg_binds`) and each binder's
inline pragma, not the rest of GHC's `TcGblEnv`. With forcing on, `source.total`
also includes one traversal of the input before the first transformation. Unless
`preserve-source-locations` is on, `source.anchors` inserts nothing and measures
only the traversal of its unchanged result, or nothing when forcing is off.

### What the numbers include

- A line's own stderr write is outside its stage, but totals include the writes
  of their child stages. Totals already contain their children; do not add them up.
- Not measured: GHC's parsing, renaming, typechecking and code generation, plugin
  loading and option parsing, and the GHC simplifier run that the plugin installs
  before its own pass.
- Without `dump-timings` the plugin reads no clocks and forces nothing. With it,
  the timings describe the instrumented compiler; for end-to-end compile time,
  time the whole GHC process.
