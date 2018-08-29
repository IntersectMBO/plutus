# Holed types

## Preface

Consider how the `list` data type is defined:

In readable notation:

```
\(a :: *). fix \(list :: *) -> all (r :: *). r -> (a -> list -> r) -> r
```

In Plutus Core:

```
(lam a (type) (fix list (all r (type) (fun r (fun (fun a (fun list r)) r)))))
```

Now consider how the `[]` term looks like:

In readable notation with the type `Wrap` is applied to being omitted:

```
> /\(a :: *) -> wrap /\(r :: *) -> \(z : r) (f : a -> list a -> r) -> z
```

Nice and simple.

In Plutus Core:

```
(abs a (type) (wrap list (all r (type) (fun r (fun (fun a (fun list r)) r))) (abs r (type) (lam z r (lam f (fun a (fun (fix list (all r (type) (fun r (fun (fun a (fun list r)) r)))) r)) z)))))
```

Well...

Let's fold the unfolded `list` type. We substitute `fix list (all r (type) (fun r (fun (fun a (fun list r)) r)))` with `list a` (thus this is not legal Plutus Core, just some pseudocode)

```
(abs a (type) (wrap list (all r (type) (fun r (fun (fun a (fun list r)) r))) (abs r (type) (lam z r (lam f (fun a (fun [list a] r)) z)))))
```

That's shorter, but there is still that type to which `wrap` is applied. And it's not `list` -- it's `listF`, i.e. the pattern functor of `list`:

```
all r (type) (fun r (fun (fun a (fun list r)) r))
```

This is like `list` specified to `a`, but without the `fix`. If we substitute the type above with `listF a`, we'll get

```
(abs a (type) (wrap list [listF a] (abs r (type) (lam z r (lam f (fun a (fun [list a] r)) z)))))
```

Well that's more readable.

## The problem itself

But how do we construct a term like that in Haskell? Clearly we do not want to write `listF` and `list` separately as these are very related types. However they both start by a type-level lambda, then `list` has a `fix` and `listF` has nothing and then they're identical. Compare:

```
list  = (lam a (type) (fix list (all r (type) (fun r (fun (fun a (fun list r)) r)))))
listF = (lam a (type)           (all r (type) (fun r (fun (fun a (fun list r)) r))))
```

This asks for a data type that has a hole inside it which we can instantiate by either `fix` or nothing. [Language.PlutusCore.StdLib.Type](stdlib/Language/PlutusCore/StdLib/Type.hs) defines such type:

```haskell
data HoledType tyname a = HoledType
    { _holedTypeName :: tyname a
    , _holedTypeCont :: (Type tyname a -> Type tyname a) -> Type tyname a
    }
```

This allows us to define both `list` and `listF` at the same time. Even more, we can instantiate them to a particular `a` simultaneously using

```haskell
-- | Apply a 'HoledType' to a 'Type' using computing type application under the hood.
holedTyApp :: HoledType tyname () -> Type tyname () -> HoledType tyname ()
holedTyApp (HoledType name cont) arg = HoledType name $ \hole -> TyApp () (cont hole) arg
-- TODO: the 'TyApp' must be computing.
```

using `holedTyApp` over lists defined as a `HoledType` gives us

```
list  = (fix list (all r (type) (fun r (fun (fun a (fun list r)) r)))))
listF =           (all r (type) (fun r (fun (fun a (fun list r)) r))))
```

Once we are in this state, we no longer need holes, because we can immediately compute what `Wrap` should be instantiated to, as well as return the actual recursive type. Hence we define

```haskell
-- | A 'Type' that starts with a 'TyFix' (i.e. a recursive type) packaged along with a
-- specified 'Wrap' that allows to construct elements of this type.
data RecursiveType tyname a = RecursiveType
    { _recursiveWrap :: forall name. Term tyname name a -> Term tyname name a
    , _recursiveType :: Type tyname a
    }
```

and here is a function that converts a `HoledType` into a `RecursiveType`:

```haskell
-- | Convert a 'HoledType' to the corresponding 'RecursiveType'.
holedToRecursive :: HoledType tyname () -> RecursiveType tyname ()
holedToRecursive (HoledType name cont) =
    RecursiveType (Wrap () name $ cont id) (cont $ TyFix () name)
```

where `Wrap () name $ cont id` instantiates `Wrap` to the pattern functor that a `HoledType` encodes and `cont $ TyFix () name` returns the actual recursive type that the `HoledType` encodes.

At the use side we match on a `RecursiveType` and use the specified `Wrap` to construct data at the value level and use the recursive type in type signatures.
