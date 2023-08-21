# Goal

We want our debugger to provide user information at runtime about which
location the currently-executing UPLC code was "sourced" from.
In GHC, such a location is called a `SrcSpan` and is `(haskellHsFilename,startline,startcol,endline,endcol)`.

Note that having the AST annotated with `SrcSpan`s may influence negatively the GHC optimizations
(mostly inlining) for the reason of not eliminating/changing `SrcSpan`s.
It does not matter for our case though, because we don't rely on GHC optimizations but
instead get the GHC core unoptimized early from the pipeline.

There are two types of `SrcSpan` locations:

## i. definition-site locations

All GHC_Core (type) variables come by default annotated with a `SrcSpan` that points
to where they are *defined* , in contrast to the current point that occur / are being called for.
To get the `SrcSpan` of a variable, you call `GHC.Types.Name.getSrcSpan` on the `Var`

e.g.

``` haskell
f = 1 + 1

main = f 3
```

The part of AST describing `f 3`, roughly in GHC_Core as  `(App (Var "f") (Lit 3))`,
contains `SrcSpan` on the `Var "f"` node on where the `f` is defined, i.e. (Line 1, Col 1,...)

## ii. call-site locations

Function calls (applications) can optionally be annotated with a `SrcSpan` pointing to
where they occur/ are called for (not where the function/arguments are defined).

In the above example, the part of AST describing `f 3` --- `(App (Var "f") (Lit 3))` --- can be
annotated with a SrcSpan of (Line 3, Col 8...).

# How

To achieve this we need:

1. to collect the `SrcSpan` locations and
2. propagate the `SrcSpans through our compilation artifacts (GHC_Core->PIR->PLC->UPLC).

## 1. Collecting SrcSpans

The definition-site locations are already provided by GHC and nothing extra needs to be done.
The more interesting call-site locations need an extra step to instruct GHC to spit them out.

There are (at least) 4 methods to make GHC annotate the GHC_Core with `SrcSpan`s,
and hand it to us to feed it to our plutus-tx-plugin (start of our compiler pipeline):

a. HPC (flag -fhpc)
b. DWARF (flag -g )
c. Prof (flag -prof)
d. Ghci

### a. HPC method

The hpc method does not annotate the GHC core ast with precises `SrcSpan`s (the 5-tuple above) but
with indices to a`SrcSpan` "array"" contained in a separately generated `mix` file.

The good thing is that the resulting annotated GHC_core will end up being smaller in overall (serialised) size.
The bad thing is that to find out the exact srcspan, we need an extra lookup at array "mix" file.

### b. DWARF method

Nothing peculiar to discuss about this method, and it looks like we already make use of it elsewhere in the plugin (for coverage):
<https://github.com/input-output-hk/plutus/blob/master/plutus-tx-plugin/src/PlutusTx/Compiler/Types.hs#L80-L88>
This gives us `SourceNote` constructors of the `Tickish` datatype.

### c. Prof method

Pros: The annotations can be controlled by the user by prepending user-interested haskell expressions in the original file
with "{-# SCC -#}" comments.

Cons: Cabal will refuse to mix the compilation of libraries compiled with -prof and libraries without it, and will try to rebuild those that miss -prof.

### d. Ghci method

I haven't found a way yet to **programmatically** get the `SrcSpan`s out of `ghci`.

Also we seem to rely in our compilation on the flag `-fobject-code` and that may be a problem perhaps for ghci.

### Comparing the detailing of annotations

Some annotate more GHC_Core AST node places than others.
In the order of most `SrcSpan` annotations generated in the GHC Core node:

`hpc > dwarf > prof = ghci`

, meaning hpc annotated the most places.

### Comparing unfoldings

Ghci does not generate any interface `.hi` files (only keeps relevant data in memory), so
that means it is going to be difficult to get the unfoldings in a later step and pass them to our `plutus-tx-plugin`.

All the other 3 methods are confirmed to include the `SrcSpan`s annotations inside the unfoldings section of the `.hi` interface files.

### Decision

Go with DWARF `-g` since it is good enough and we used it before.

## 2. Propagating SrcSpans

Our plugin can already accept `CoreExpr` annotated with `SrcSpan`s but strips them off / ignores them.

The change is simply a matter of copying these `SrcSpan` data when constructing the PIR AST.
And so forth until we reach the final UPLC.

### Note by Michael

When copying the `SrcSpan`s we should use our own `SrcSpan'` datatype, isomoprhic to GHC's https://hackage.haskell.org/package/ghc-8.2.2/docs/SrcLoc.html#t:SrcSpan
, to constrain the dependency on the `ghc` library only for the `plutus-tx-plugin` package.

### Note about missing SrcSpans

None of the above SrcSpan-collecting methods will annotate every GHC_Core node with a `SrcSpan`;
some child nodes are implied to belong inside the parent `SrcSpan`.

I don't think we have to do something about it; we may perhaps have
to make make our plutus (pir/plc/uplc) annotation to be `Maybe SrcSpan` to cover missing srcspans.

Another way is to place an early `CoreExpr->CoreExpr` traversal
that propagates missing srcspans to child nodes even before we start our pipeline
(idea taken from `https://hackage.haskell.org/package/ghc-srcspan-plugin`).

A missing srcspan will also not be a problem at runtime (during debugging),
because the debugger can use the cek `Context` (callstack) to approximate the current position.
