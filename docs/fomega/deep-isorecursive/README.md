# Higher-kinded `fix`

This document provides a high-level view on the problem of higher-kinded `fix` and possible solutions to it.

For the final solution (and all the implementation details), that we settled on, jump straight to [the docs in the code itself](https://github.com/input-output-hk/plutus/blob/f551aa864df1104b06cb5a0460f751e1b86d2481/language-plutus-core/stdlib/Language/PlutusCore/StdLib/Type.hs) (TODO: change the link once the PR is merged). The docs there are self-contained.

For the story about how we arrived at that solution, see below.

## Story

### Motivation

Originally, in the specification we had

```
fix :: (* -> *) -> *
wrap   (f :: * -> *) (t : f (fix f)) : fix f
unwrap (f :: * -> *) (t : fix f)     : f (fix f)
```

however we realized it's not sufficient, because

1. we need to be able to encode irregular types and `fix :: (* -> *) -> *` is not enough for that, because the recursive case is always of kind `*`, i.e. is always the same as a data type being defined, so something like

  ```haskell
  data PerfectBinaryTree a = Fringe a | Branch (PerfectBinaryTree (a, a))
  ```

  is not possible to encode with just `fix :: (* -> *) -> *`, because the `PerfectBinaryTree (a, a)` recursive case is instantiated differently than the data type being defined (`PerfectBinaryTree a`).

2. we need to be able to encode mutually recursive data types which requires at least `ifix :: ((k -> *) -> k -> *) -> k -> *)` to be admissible. Available docs are:
    1. [how to encode mutually recursive data types (an Agda doc)](../mutual-type-level-recursion/MutualData.agda)
    2. [actual System F-omega (extended with `ifix`) types and terms](TreeForest.md)

3. from the implementation point of view it's much more convenient to have a way to emulate generic `fix :: (k -> k) -> k` (see the implementation docs (the first link in this document) on that)

### "Okay, so just add `fix :: (k -> k) -> k` to the language and the problem is solved, right?"

Nope. It's perfectly fine to have `fix :: (k -> k) -> k` as a type primitive, but what are the type rules for `wrap` and `unwrap` then? For `wrap` we need a single rule that subsumes all of these:

```
wrap0 (f :: * -> *)                                                 (t : f (fix f)      ) : fix f
wrap1 (f :: (k1 -> *) -> k1 -> *)             (a1 :: k1)            (t : f (fix f) a1   ) : fix f a1
wrap2 (f :: (k1 -> k2 -> *) -> k1 -> k2 -> *) (a1 :: k1) (a2 :: k2) (t : f (fix f) a1 a2) : fix f a1 a2
...
```

I.e. to check well-typedness of an instantiation of some generic `wrap` we need to traverse a sequence of type applications in order to be able to check whether `f` from the head of application is the same thing as `f` from the first argument (`fix f`). This is not trivial to specify.

### Possible solutions

There are three serious contenders and a couple of not so serious ones. The latter are

1. give up on type inference being always possible
2. give up on irregular and mutually recursive data types

We didn't want to give up.

#### Serious contenders

1. elimination contexts. This approach is taken from [PhD Thesis "Understanding and Evolving the ML Module System", Dreyer 2005](https://people.mpi-sws.org/~dreyer/thesis/main.pdf). This is the approach we started from. Available docs are:
    1. [original proposal](proposal.md)
    2. [elaborated proposal](reasoning.tex) in the .tex format with a lot of inference rules and a bit of explanation
    3. [a critical problem](problem.md) we encountered after we'd started implementing this solution. tl;dr is, it's not possible to always infer the types of terms in this setting, because there we essentially have `wrap` that subsumes all of these:

```
wrap0 (f :: * -> *)                           (t : f (fix f)      ) : fix f
wrap1 (f :: (k1 -> *) -> k1 -> *)             (t : f (fix f) a1   ) : fix f a1
wrap2 (f :: (k1 -> k2 -> *) -> k1 -> k2 -> *) (t : f (fix f) a1 a2) : fix f a1 a2
...
```

i.e. we have `wrap` that does not store `a1`, `a2`, etc. And it turned out that we do need to store those `a1`, `a2`, etc at the term level, otherwise type inference is ambiguous.

There are ways to deal with the problem, but they all are unsatisfactory:

 - give syntax to elimination contexts and store them in terms where necessary to drive type inference -- kinda defeats the purpose of having elimination contexts, because then there is a more natural and well-known way to get the same, see the head-spine form approach below
 - generalize elimination contexts -- discussed in the problem doc itself. Basically, then we get a system that nobody fully understands

Since no satisfactory solution was proposed, we started to look at alternative solutions (see [alternatives.md](alternatives.md)):

2. the head-spine form approach. This approach is very similar to the elimination contexts one as an elimination context is just a spine in disguise. Spines do have syntax and thus the problem with elimination contexts mentioned above can be solved by simply storing spines in terms where needed. But this is not trivial to specify as well and in fact it was never specified, because it turned out we do not need this level of genericity in our syntax (see the next item)

3. just add `ifix :: ((k -> *) -> k -> *) -> k -> *` to the language as it's enough for being able to emulate generic `fix :: (k -> k) -> k`. This is elaborated in [this document](https://github.com/input-output-hk/plutus/blob/c9e78465014efe986ce4d4b569fe2b070da2b14c/docs/fomega/mutual-type-level-recursion/IFixIsEnough.agda) (TODO: change the link once the PR is merged) and in the comments in the code. This is the final solution that gets us a simple core language and the required expressiveness.
