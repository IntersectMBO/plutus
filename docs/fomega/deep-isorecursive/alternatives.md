# Alternatives to elimination contexts

Elimination contexts are problematic, see the problem.md document. Hence one option is to move away from them and use something else. This document describes possible alternatives.

## Head-spine form

An elimination context is either a type or an application of a type function (which is in the form of elimination context again) to a type argument. If the head of such application is a `fix`, then we can `wrap` and `unwrap` a term of such type. Wrapping results in the `head` of the application being substituted for the variable it binds. One of the premises `wrap` has is that the whole thing must be of kind `(type)` and the same holds for `unwrap`.

What I've just described is exactly iterated application that leads to hereditary substitution at the type level: allowing `Fix` to be applied to a bunch of arguments kinda asks for iterated application at the type level:

```
Gamma |- wrap α pat spine M : [(fix α pat) spine]
```

Also iterated application is common at the type level as it simplifies unification (which we do not care about) and can be used for the formalization, because it's required by hereditary substitution (we do not do hereditary substitution, so both the points are not important for us, but what I'm proving here is that the head-spine form at the type level is common unlike elimination contexts).

There is a [formalization sketch of this](https://gist.github.com/effectfully/8ae112e2a99393c493642fc52aafe87f#file-system-f-iso-agda).

## Replace `fix :: (* -> *) -> *` by `ifix :: ((k -> *) -> k -> *) -> k -> *`

The least invasive approach. We only need to replace `fix :: (* -> *) -> *` by `ifix :: ((k -> *) -> k -> *) -> k -> *`. The original `fix` [can be easily recovered](https://gist.github.com/effectfully/e57d2816c475928a380e5a6b897ad17d#file-ifixnat-agda).

We can emulate application of `fix` to a spine of arguments. With kind-level products we could write `fix f (a1, a2, ... an)`. We do not have kind-level products, but we can just Church-encode spines:

```
fix f (\(r :: k1 -> k2 -> ... -> kn -> *) -> r a1 a2 ... an)
```

which gives us `k ~ (k1 -> k2 -> ... -> kn -> *) -> *`. This is not a "true" Church-encoded spine, because the resulting type is limited to be of kind `*`, but this seems enough in our case ([an illustration](https://gist.github.com/effectfully/e57d2816c475928a380e5a6b897ad17d#file-ifixn-agda)).

Besides, `ifix` is what we use to [encode mutually recursive data types](https://gist.github.com/effectfully/e57d2816c475928a380e5a6b897ad17d) and having the ability to encode mutually recursive data type is the primary reason for having a higher-kinded `fix`.
