-- In this document we'll consider various encodings of mutual data types,
-- including those that are System Fω compatible.

module MutualData where

open import Function
open import Data.Unit.Base
open import Data.Sum
open import Data.Product

-- In the first part of this document we'll demostrate how various encodings work taking
-- the rose tree data type as an example:

mutual
  data Tree₀ (A : Set) : Set where
    node₀ : A -> Forest₀ A -> Tree₀ A

  data Forest₀ (A : Set) : Set where
    nil₀  : Forest₀ A
    cons₀ : Tree₀ A -> Forest₀ A -> Forest₀ A

module Joined where
  -- For encoding a family of mutually recursive data types in terms of a single data type we can
  -- create the type of tags each of which denotes a particular data type from the family, then
  -- merge all constructors of the original data types together into a single data type and index
  -- each of the constructors by the tag representing the data type it constructs.

  -- Since we encode a family consisting of two data types, the type of tags has two inhabitants:

  data TreeForestᵗ : Set where
    Treeᵗ Forestᵗ : TreeForestᵗ

  -- The encoding:

  mutual
    -- There is nothing inherently mutual about these data types.
    -- `Tree` and `Forest` are just aliases defined for convenience and readability.

    Tree : Set -> Set
    Tree A = TreeForest A Treeᵗ

    Forest : Set -> Set
    Forest A = TreeForest A Forestᵗ

    -- Now we have one big data type that contains all constructors of the `Tree`-`Forest` family:

    data TreeForest (A : Set) : TreeForestᵗ -> Set where
      node : A -> Forest A -> Tree A
      nil  : Forest A
      cons : Tree A -> Forest A -> Forest A

    -- Note that the constructors have exactly the same type signatures as before,
    -- but now `Tree` and `Forest` are instances of the same data type.

  -- As a sanity check we show one side (just to save space and because it's demonstrative enough)
  -- of the isomorphism between the original family and its encoded version:

  mutual
    toTree₀ : ∀ {A} -> Tree A -> Tree₀ A
    toTree₀ (node x forest) = node₀ x (toForest₀ forest)

    toForest₀ : ∀ {A} -> Forest A -> Forest₀ A
    toForest₀  nil               = nil₀
    toForest₀ (cons tree forest) = cons₀ (toTree₀ tree) (toForest₀ forest)

  -- The encoding technique described in this module is fairly well-known.

module JoinedCompute where
  -- In this section we'll make `TreeForest` a data type with a single constructor,
  -- the contents of which depends on the type being constructed.

  data TreeForestᵗ : Set where
    Treeᵗ Forestᵗ : TreeForestᵗ

  mutual
    -- Again, `Tree` and `Forest` are just aliases.

    Tree : Set -> Set
    Tree A = TreeForest A Treeᵗ

    Forest : Set -> Set
    Forest A = TreeForest A Forestᵗ

    -- `TreeForestF` matches on the `TreeForestᵗ` index in order to figure out which data type
    -- from the original family is being constructed.
    -- Like in the previous section `TreeForest` defines both the `Tree` and `Forest` data types,
    -- but now it contains a single constructor that only captures the notion of recursion.
    -- What data to store in this constructor is determined by the `TreeForestF` function.

    TreeForestF : Set -> TreeForestᵗ -> Set
    TreeForestF A Treeᵗ   = A × Forest A           -- The only constructor of `Tree` is `node` which
                                                   -- carries an `A` and a `Forest A`.
    TreeForestF A Forestᵗ = ⊤ ⊎ Tree A × Forest A  -- There are two constructors of `Forest`:
                                                   -- `nil` and `cons`. The former one doesn't
                                                   -- carry any information while the latter one
                                                   -- receives a `Tree` and a `Forest`.

    data TreeForest (A : Set) (tfᵗ : TreeForestᵗ) : Set where
      treeForest : TreeForestF A tfᵗ -> TreeForest A tfᵗ

  -- For convenience, we'll be using pattern synonyms in this module and the modules below.

  pattern node x forest    = treeForest (x , forest)
  pattern nil              = treeForest (inj₁ tt)
  pattern cons tree forest = treeForest (inj₂ (tree , forest))

  -- The sanity check.

  mutual
    toTree₀ : ∀ {A} -> Tree A -> Tree₀ A
    toTree₀ (node x forest) = node₀ x (toForest₀ forest)

    toForest₀ : ∀ {A} -> Forest A -> Forest₀ A
    toForest₀  nil               = nil₀
    toForest₀ (cons tree forest) = cons₀ (toTree₀ tree) (toForest₀ forest)

-- In the previous section we had the `TreeForest` data type and its `treeForest` constructor
-- which together captured the notion of recursion. This pattern can be abstracted, so that we can
-- tie knots in arbitrary other data types -- not just `Tree` and `Forest`. Enter `IFix`:

{-# NO_POSITIVITY_CHECK #-}
data IFix {α β} {A : Set α} (B : (A -> Set β) -> A -> Set β) (x : A) : Set β where
  wrap : B (IFix B) x -> IFix B x

module JoinedComputeIFix where
  -- In this module we define the `TreeForest` data type using `IFix`.
  -- The type of tags is as before:

  data TreeForestᵗ : Set where
    Treeᵗ Forestᵗ : TreeForestᵗ

  -- The definition of `TreeForest` is similar to the definition from the previous section:
  -- we again have the `Tree` and `Forest` type aliases, they're just local now,
  -- and as before we dispatch on `tfᵗ` and describe the constructors of the `Tree` and `Forest`
  -- data types using the sum-of-products representation:

  TreeForest : Set -> TreeForestᵗ -> Set
  TreeForest A =
    IFix λ Rec tfᵗ ->
      let Tree   = Rec Treeᵗ
          Forest = Rec Forestᵗ
        in case tfᵗ of λ
          { Treeᵗ   -> A × Forest
          ; Forestᵗ -> ⊤ ⊎ Tree × Forest
          }

  -- We've cheated a little bit here by keeping `A` outside of the pattern functor.
  -- That's just for simplicity, there is no fundamental limitation that prevents us
  -- from taking fixed points of pattern functors of arbitrary arity.
  -- Which is a topic for another document.

  Tree : Set -> Set
  Tree A = TreeForest A Treeᵗ

  Forest : Set -> Set
  Forest A = TreeForest A Forestᵗ

  pattern node x forest    = wrap (x , forest)
  pattern nil              = wrap (inj₁ tt)
  pattern cons tree forest = wrap (inj₂ (tree , forest))

  -- The sanity check.

  mutual
    toTree₀ : ∀ {A} -> Tree A -> Tree₀ A
    toTree₀ (node x forest) = node₀ x (toForest₀ forest)

    toForest₀ : ∀ {A} -> Forest A -> Forest₀ A
    toForest₀  nil               = nil₀
    toForest₀ (cons tree forest) = cons₀ (toTree₀ tree) (toForest₀ forest)

module JoinedComputeIFixFω where
  -- The types we had previously are not System Fω compatible, because we matched on tags at the
  -- type level. Can we avoid this? Yes, easily. Instead of defining data types representing tags
  -- we can just lambda-encode them, because we do have lambdas at the type level in System Fω.

  -- The Church-encoded version of `TreeForestᵗ` at the type level looks like this:

  -- ∀ R -> R -> R -> R

  -- However this is still not System Fω compatible, because here we quantify over `R` which in
  -- System Fω is a kind and we can't quatify over kinds there. But looking at

  -- TreeForestF : Set -> TreeForestᵗ -> Set
  -- TreeForestF A Treeᵗ   = A × Forest A
  -- TreeForestF A Forestᵗ = ⊤ ⊎ Tree A × Forest A

  -- we see that we match on a `TreeForestᵗ` only to return a `Set`. Hence we can just instantiate
  -- `R` to `Set` right away as we do not do anything else with tags. We arrive at

  TreeForestᵗ : Set₁
  TreeForestᵗ = Set -> Set -> Set

  Treeᵗ : TreeForestᵗ
  Treeᵗ A B = A

  Forestᵗ : TreeForestᵗ
  Forestᵗ A B = B

  -- Where `TreeForestᵗ` is the type of inlined matchers which always return a `Set` and
  -- `Treeᵗ` and `Forestᵗ` are such matchers. The rest is straightforward:

  TreeForest : Set -> TreeForestᵗ -> Set
  TreeForest A =
    IFix λ Rec tfᵗ ->
      let Tree   = Rec Treeᵗ
          Forest = Rec Forestᵗ
        in tfᵗ
             (A × Forest)         -- Returned when `tfᵗ` is `Treeᵗ`.
             (⊤ ⊎ Tree × Forest)  -- Returned when `tfᵗ` is `Forestᵗ`.

  Tree : Set -> Set
  Tree A = TreeForest A Treeᵗ

  Forest : Set -> Set
  Forest A = TreeForest A Forestᵗ

  -- All types are System Fω compatible (except the definition of `TreeForestᵗ` has to be inlined)
  -- as System Fω does not support kind aliases.

  pattern node x forest    = wrap (x , forest)
  pattern nil              = wrap (inj₁ tt)
  pattern cons tree forest = wrap (inj₂ (tree , forest))

  -- The sanity check.

  mutual
    toTree₀ : ∀ {A} -> Tree A -> Tree₀ A
    toTree₀ (node x forest) = node₀ x (toForest₀ forest)

    toForest₀ : ∀ {A} -> Forest A -> Forest₀ A
    toForest₀  nil               = nil₀
    toForest₀ (cons tree forest) = cons₀ (toTree₀ tree) (toForest₀ forest)

  -- An additional test:

  mutual
    mapTree : ∀ {A B} -> (A -> B) -> Tree A -> Tree B
    mapTree f (node x forest) = node (f x) (mapForest f forest)

    mapForest : ∀ {A B} -> (A -> B) -> Forest A -> Forest B
    mapForest f  nil               = nil
    mapForest f (cons tree forest) = cons (mapTree f tree) (mapForest f forest)

-- The first part ends here.  We've just seen how to encode mutual data types in pure System Fω
-- with build-in isorecursive `IFix :: ((k -> *) -> k -> *) -> k -> *`.

-- In the second part we'll see how to encode mutual data types with distinct kind signatures.
-- Due to my lack of imagination, we'll take the following family as an example:

mutual
  data M₀ (A : Set) : Set where
    p₀ : A -> M₀ A
    n₀ : N₀ -> M₀ A

  data N₀ : Set where
    m₀ : M₀ ⊤ -> N₀

-- `M₀` is of kind `Set -> Set` while `N₀` is of kind `Set`.

module DistinctParamsJoined where
  -- As in the first part we start with a single data type that contains all the constructors of
  -- the family of data types being encoded.

  -- The only thing we need to do, is to add all the parameters to the constructors of the type
  -- of tags. The rest just follows.

  data MNᵗ : Set₁ where
    Mᵗ : Set -> MNᵗ  -- `M` is parameterized by a `Set`, hence one `Set` argument.
    Nᵗ : MNᵗ         -- `N` is not parameterized, hence no arguments.

  -- The encoding itself follows the same pattern we've seen previously:

  mutual
    M : Set -> Set
    M A = MN (Mᵗ A)

    N : Set
    N = MN Nᵗ

    data MN : MNᵗ -> Set where
      -- `∀ {A} -> ...` is an artifact of this particular encoding, it'll disappear later.
      p : ∀ {A} -> A -> M A
      n : ∀ {A} -> N -> M A
      m : M ⊤ -> N

  -- The sanity check.

  mutual
    toM₀ : ∀ {A} -> M A -> M₀ A
    toM₀ (p x) = p₀ x
    toM₀ (n y) = n₀ (toN₀ y)

    toN₀ : N -> N₀
    toN₀ (m y) = m₀ (toM₀ y)

module DistinctParamsJoinedComputeIFix where
  -- We skip the `JoinedCompute` stage and jump straight to `JoinedComputeIFix`.

  -- Again, we just add arguments to tags and the rest follows:

  data MNᵗ : Set₁ where
    Mᵗ : Set -> MNᵗ
    Nᵗ : MNᵗ

  MN : MNᵗ -> Set
  MN =
    IFix λ Rec mnᵗ ->
      let M A = Rec (Mᵗ A)
          N   = Rec Nᵗ
        in case mnᵗ of λ
          { (Mᵗ A) -> A ⊎ N  -- `M` has two constructors: one receives an `A` and
                             -- the other receives an `N`.
          ;  Nᵗ    -> M ⊤    -- `N` has one constructor which receives an `M ⊤`.
          }

  M : Set -> Set
  M A = MN (Mᵗ A)

  N : Set
  N = MN Nᵗ

  pattern p x = wrap (inj₁ x)
  pattern n y = wrap (inj₂ y)
  pattern m y = wrap y

  -- The sanity check.

  mutual
    toM₀ : ∀ {A} -> M A -> M₀ A
    toM₀ (p x) = p₀ x
    toM₀ (n y) = n₀ (toN₀ y)

    toN₀ : N -> N₀
    toN₀ (m y) = m₀ (toM₀ y)

module DistinctParamsJoinedComputeIFixFω where
  -- Mechanically performing the restricted Church-encoding transformation that allows to bring
  -- the types into the realms of System Fω, we get

  MNᵗ : Set₁
  MNᵗ = (Set -> Set) -> Set -> Set

  Mᵗ : Set -> MNᵗ
  Mᵗ A = λ rM rN -> rM A

  Nᵗ : MNᵗ
  Nᵗ = λ rM rN -> rN

  -- Nothing new here:

  MN : MNᵗ -> Set
  MN =
    IFix λ Rec mnᵗ ->
      let M A = Rec (Mᵗ A)
          N   = Rec Nᵗ
        in mnᵗ (λ A -> A ⊎ N) (M ⊤)

  M : Set -> Set
  M A = MN (Mᵗ A)

  N : Set
  N = MN Nᵗ

  pattern p x = wrap (inj₁ x)
  pattern n y = wrap (inj₂ y)
  pattern m y = wrap y

  -- The sanity check.

  mutual
    toM₀ : ∀ {A} -> M A -> M₀ A
    toM₀ (p x) = p₀ x
    toM₀ (n y) = n₀ (toN₀ y)

    toN₀ : N -> N₀
    toN₀ (m y) = m₀ (toM₀ y)

module FakingFix where
  -- We can look at encoding mutual data types from entirely distinct perspective.
  -- One of the standard approaches is to have kind-level products and use `Fix :: (k -> k) -> k`
  -- over them. There is no such `Fix` in Agda, but we can pretend it exists:

  postulate
    Fix : ∀ {α} {A : Set α} -> (A -> A) -> A

  -- Then we can encode `MN` as

  MN : (Set -> Set) × Set
  MN =
    Fix λ Rec ->
      let M A = proj₁ Rec A
          N   = proj₂ Rec
        in (λ A -> A ⊎ N) , M ⊤

  -- This all is very similar to what we've seen in the previous section: the local definitions
  -- of `M` and `N` differ and we construct a type-level tuple rather than a `Set`, but the
  -- pattern is the same.

  -- The global definitions of `M` and `N` are

  M : Set -> Set
  M = proj₁ MN

  N : Set
  N = proj₂ MN

  -- And now we can perform the same restricted Church-encoding trick again and use
  -- `((Set -> Set) -> Set -> Set) -> Set` instead of `(Set -> Set) × Set`.
  -- Note that the new type then is exactly the same as the one of `MN` from the previous section:

  -- MN : MNᵗ -> Set

  -- which being inlined becomes:

  -- MN : ((Set -> Set) -> Set -> Set) -> Set

  -- Hence we arrived at the same encoding taking a folklore technique as a starting point.
