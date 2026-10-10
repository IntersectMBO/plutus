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

Use `-fplugin-opt Plinth.Plugin:dump-timings` to report source-plugin and
Core-to-UPLC compilation timings. The option is disabled by default;
`no-dump-timings` explicitly disables it.

Each successfully completed stage writes one tab-separated record to stderr:

```text
PLINTH_TIMING<TAB>scope<TAB>stage<TAB>wall_nanoseconds<TAB>cpu_picoseconds
```

Wall time uses a monotonic clock. CPU time is process CPU time. The scope is
the module name, with the marked variable name appended for expression stages
when available. Anonymous expressions use `module:expression`, which may repeat.
The driver hook uses `<driver>` because it runs before module information is
available. Failed stages do not emit a success record; always check the compiler
exit status before interpreting the output.

| Stage | Work measured |
|---|---|
| `source.driver` | Driver hook updating GHC flags and extensions |
| `source.total` | Typecheck-result hook, enclosing the three source transformations below |
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

Enabled timers force intermediate AST results before stopping, so lazy work is
attributed to the stage producing the AST rather than a later consumer. This
adds traversal cost and can change evaluation order, allocation and garbage
collection. Disabled timers do not force results or read clocks.

Source timers traverse expressions and binding inline pragmas rather than
deep-evaluating GHC's cyclic environment. The initial input traversal is outside
`source.total`. When source-location preservation is disabled, `source.anchors`
records an identity action plus traversal overhead. These source hooks do not
measure GHC's own parsing, renaming or typechecking.

Each record excludes its own stderr write; enclosing totals include child
records' logging overhead. Do not add child stages to enclosing totals.
Source totals exclude initial option parsing and plugin loading. `core.total`
excludes the preparatory GHC simplifier installed before the plugin pass and
subsequent GHC code generation. These are instrumented timings, not exact
zero-overhead measurements of uninstrumented compilation.
