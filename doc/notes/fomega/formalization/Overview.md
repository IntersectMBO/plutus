# Formalization of System Fω

## Related work

### Code

[1] [Type-level lambdas + hereditary substitution at the type and term levels + shifting at variables + Agda](https://github.com/AndrasKovacs/system-f-omega), András Kovács.

[2] [No type-level lambdas + isorecursive `mu` + shifting at big lambdas + raw terms + small-step and big-step evlauation + Agda](https://github.com/sstucki/system-f-agda), Sandro Stucki.

[3] [No type-level lambdas + shifting at big lambdas + lots of proof automation via Descriptions + Agda](https://github.com/gergoerdi/system-f-agda/blob/master/src/SystemF.agda), Dr. Gergő Érdi.

[4] [No ω + shifting at variables + Agda](https://plfa.github.io/SystemF), Philip Wadler.

[5] [No type-level lambdas + abstract contexts/renamings/environments used at the type and term levels + shifting at big lambdas + Agda](https://github.com/effectfully/random-stuff/tree/master/System-F), Roman Kireev.

[6] [Type-level lambdas + hereditary substitution at the type level + isorecursive `fix` + shifting at big lambdas + no term-level substitution + Agda](https://gist.github.com/effectfully/8ae112e2a99393c493642fc52aafe87f), Roman Kireev.

[7] [No ω + locally nameless (thus no shifting) + Coq](https://github.com/heades/System-F-Coq), Harley D. Eades III.

[8] [No ω + shifting at big lambdas + Coq](https://github.com/bobatkey/system-f-parametricity-model), Bob Atkey.

[9] [No ω + locally nameless (thus no shifting) + Coq + soundness, progress, and preservation proofs](https://github.com/stepchowfun/proofs/tree/master/coq/SystemF), Stephan Boyer.

### Papers

[A Formalization of the Strong Normalization Proof for System F in Lego](http://www.cs.nott.ac.uk/%7Epsztxa/publ/tlca93.pdf), Thorsten Altenkirch.

## Design

### Type normalization

Since we have type-level lambdas, type normalization is required. There are two plausible approaches: hereditary substitution and normalization by evaluation. The former is implemented in [1]. However the author of [1] [says](https://github.com/AndrasKovacs/system-f-omega/issues/1#issuecomment-417955260) he'd prefer NbE now, because hereditary substitution makes a formalization tedious. I see two approaches to NbE that might work:

1. [readback](https://github.com/effectfully/random-stuff/blob/master/Normalization/Readback.agda)
2. [the fully eta-expanding reify/reflect machinery](https://github.com/effectfully/random-stuff/blob/master/Normalization/SystemT.agda)

I'd start from 1 and see if it works. And I think we shouldn't discard hereditary substitution right now.

### Shifting

Terms have lambdas (which bind term variables) and big lambdas (which bind type variables). And those can be interleaved. Consider for example the following term:

`/\(A :: *) -> \(x : A) -> ...`

De Bruijnified version of it looks like this:

`bigLam $ lam (var here) $ ...`

In `...` the `x` variable is written as `var here` (points to the term context) which type is `var here` (points to the type context) -- this is what `lam` receives: the type of the variable it binds. But if we add another big lambda

`/\(A :: *) -> \(x : A) -> /\(B :: *) -> ...`

then the `x` variable is still `var here`, but its type is now `var (there here)`. So we need to either shift by one the type variables occurring in the type of a variable at each place the variable is used in a term or simply shift all type variables of all types in a current type context each time `/\` is used. The former is used in [1] and [4], the latter is used in all other formalizations.

I believe the latter results in simpler proofs and should be preferred over the former. The former is more precise about the order in which types are introduced in type contexts, but

1. we do not use this information for anything
2. it can be recovered from terms if needed
3. it comes at the price of complicating a formalization
4. it doesn't allow to use the same contexts/renamings/environments machinery for both the type and term levels in the style [5] does this

### `fix`

There are several approaches for dealing with higher-kinded type-level recursion:

1. `fix` can receive a spine of arguments like it's done in [6]
2. `fix` can be of kind `((k -> *) -> k -> *) -> k -> *`
3. eliminations contexts can be used like it's in the specification

2 is *much* simpler for formalization than 1, especially in a setting without hereditary substitutions. However 2 also requires a proof that it's as strong as the other approaches.

3 is currently unexplored (this is a TODO).
