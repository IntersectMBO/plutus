# ifix

## Preface

Here we talk about the history of this thing:

```
ifix :: ((k -> *) -> k -> *) -> k -> *
```

It has many names in the wild: `ifix`, `hfix`, `ixfix`, `fix1` (all of those with random  capitalization), etc.

We use `ifix` for encoding mutually recursive and non-regular data types (and GADTs, but that hasn't been tested yet). It is well-known in the literature that `ifix` can be used for encoding such data types and this document aims to prove that.

## Origins

In [Type inference for arbitrary-rank types is easy](https://www.cs.tufts.edu/~nr/cs257/archive/simon-peyton-jones/higher-rank.ps) the authors (Simon Peyton Jones and Mark Shields) attribute `Hfix` to Ralf Hinze:

> When a program contains rank-2 types it is not too long before one wants to have a record with a field that has a rank-2 type, so the record constructor has a rank-3 type. Similarly, one may want to have a function parameter with rank-2 type so the function itself has a rank-3 type. And so on. That said, we have only encountered one genuine case of a rank-3 type, due to Ralf Hinze:
>
> ```haskell
> type Map f g = forall a b. (a->b) -> f a -> g b
> newtype Hfix h a = H (h (Hfix h) a)
> hmap :: forall h i. (forall f g. Map f g -> Map (h f) (i g)) -> Map (Hfix h) (Hfix i)
> ```

Unfortunately they do not specify a particular reference. But see below.

## Nested/non-regular data types

### [Polytypic values possess polykinded types -- Ralf Hinze, 2000](https://www.researchgate.net/publication/225659333_Polytypic_Values_Possess_Polykinded_Types)

Presumably, this is the reference that Simon Peyton Jones and Mark Shields had in mind. It defines

```haskell
newtype HFix H A = hin (H (HFix H) A).
```

of kind `((* -> *) -> * -> *) -> * -> *`, i.e. less general than the one we're interested in, but of the right shape.

The author uses `HFix` for encoding non-regular data types, e.g.

```haskell
data Fork A = fork A A
data Sequ A = empty | zero (Sequ (Fork A)) | one A (Sequ (Fork A))
```

gets encoded as

```haskell
data SequF S A = emptyF | zeroF (S (Fork A)) | oneF A (S (Fork A))
type Sequ = HFix SequF
```

### [Generalised folds for nested datatypes -- Richard Bird, Ross Paterson, 1999](https://www.researchgate.net/publication/220102378_Generalised_folds_for_nested_datatypes/link/5703a08008aedbac12707f40/download)

In the paper they talk about higher-order fixed points:

> Moreover, we can define a functor `T :: C^n → C` as a fixed point of a suitable higher-order functor `F :: (C^n → C) → (C^n → C)`, via the same colimit construction used in C. We shall refer to such functors as _hofunctors_.

They provide a number of examples.

1. Lists represented as a fixed point of a higher-order functor:

```haskell
data Base a b = Nil | Cons (a × b)
type ListF x a = Base a (x a)
newtype List a = In (ListF List a)

2. A nested data type similar to perfect binary trees (except it contains values not only in leaves):

```haskell
data Base a b = Nil | Cons (a × b)
type Pair a = a × a
type NestF x a = Base a (x (Pair a))
newtype Nest a = In (NestF Nest a)
```

they do not define `ifix` explicitly, but this is what their encodings amounts to. E.g. they could rewrite these two definitions

```haskell
newtype List a = In (ListF List a)
newtype Nest a = In (NestF Nest a)
```

into

```haskell
newtype IFix f a = IFix (f (IFix f) a)
type List = IFix ListF
type Nest = IFix NestF
```

## Mutually recursive data types

### [Generic programming with fixed points for mutually recursive datatypes -- Alexey Rodriguez, Stefan Holdermans, Andres Loeh, Johan Jeurin, 2009](http://www.andres-loeh.de/Rec/MutualRec.pdf)

The paper explicitly defines

```
Fixn :: ((n → ∗) → n → ∗) → (n → ∗)
```

and shows how it can be used for encoding mutually recursive data types.

There is an [associated `multirec` library](https://hackage.haskell.org/package/multirec) where we can find [this definition](https://hackage.haskell.org/package/multirec-0.7.9/docs/Generics-MultiRec-HFix.html#t:HFix):

```haskell
data HFix (h :: (* -> *) -> * -> *) ix = HIn { hout :: h (HFix h) ix }
```

### [Generic Selections of Subexpressions -- Martijn van Steenbergen, Jose Pedro Magalhaes, Johan Jeuring, 2010](https://pdfs.semanticscholar.org/02be/9f6b8e74978ce9d4e218fa55efb8c6dca581.pdf?_ga=2.195079018.774840300.1574943114-1398818701.1553460034)

The 8 section of this paper builds on top of the `multirec` library mentioned in the previous section and provides the definition of `HFix` in its full.

### [Managing Interlingual References – a Type-Generic Approach, Dissertation -- von Sebastian Menge, 2011](https://pdfs.semanticscholar.org/ebb2/046d21e9ebc38d56e036109fdb3b1502f398.pdf)

Defines

```haskell
HFix (f :: (∗ → ∗) → ∗ → ∗) (ix :: ∗) = HIn (f (HFix f) ix)
```

and uses it for encoding mutually recursive data types.

Also refers to Generic programming with fixed points for mutually recursive datatype for a more generic version of `HFix`.

## GADTs

### [Generic Zero-Cost Reuse for Dependent Types -- Larry Diehl, Denis Firsov, Aaron Stump, 2018](https://arxiv.org/pdf/1803.08150.pdf)

In the paper they introduce non-indexed fixed points of a particular form suitable for their task:

```
IdMapping : (⋆ → ⋆) → ⋆ = λ F. ∀ (X Y : ⋆). Id X Y → Id (F X) (F Y)
Fix : Π (F : ⋆ → ⋆). IdMapping F → ⋆
```

and add indexation on top of that:

```
IIdMapping : Π (I : ⋆). ((I → ⋆) → I → ⋆) → ⋆ =
  λ I F. ∀ (X Y : I → ⋆).(∀ (i : I). Id (X i) (Y i)) → ∀ (i : I). Id (F X i) (F Y i)
IFix : Π (I : ⋆). Π (F : (I → ⋆) → I → ⋆). IIdMapping I F → I → ⋆
```

So this is `ifix` + some additional structure analogous to the one that they have in the non-indexed case.

As an example they define the non-indexed pattern functor of the `List` data type and the indexed pattern functor of the `Vec` data type (a vector is a list with a statically known length) and a forgetful mapping from the latter to the former (note that the kind of the index is explicitly specified (`Nat`) unlike what we normally see in Haskell):

```
Id (IFix Nat (VecF A) imapV n) (Fix (ListF A) imapL)
```

## In the wild

`ifix` is folklore, all of these references define `ifix` directly under different names (some of them define it as having the `((* -> *) -> * -> *) -> * -> *)` kind, the others define the polymorphic version):

- [Encoding mutually recursive data types 1](https://gist.github.com/themoritz/189907f2ee41c572554eb67ffda4b130)
- [Encoding mutually recursive data types 2](https://gist.github.com/AndrasKovacs/af856be6cf816e08da95)
- [Encoding GADTs 1](https://gmalecha.github.io/reflections/2018/to-be-typed-or-untyped)
- [Encoding GADTs 2](http://www.timphilipwilliams.com/posts/2013-01-16-fixing-gadts.html)
- [Encoding GADTs 3, in Scala](https://medium.com/disney-streaming/fix-point-type-for-gadt-scala-dc4e2cde349b)
- [A core library of a set of libraries that allows to encode data types](http://hackage.haskell.org/package/hschema-0.0.1.1/docs/Control-Functor-HigherOrder.html#t:HFix)
- [Expressions and Formulae a la carte](http://hackage.haskell.org/package/expressions-0.5/docs/Data-Expression-Utils-Indexed-Functor.html)
