module Compilation.Encode.Core where

open import Context
open import Type.Core
open import Compilation.Data

open import Function
open import Data.List.Base as List

{- Note [Compilation]
We compile data descriptions to System Fωμ in two steps:

1. Lambda-bind
     a) a tag to distinguish between the data types from the family
     b) a variable for each of the data types from the family
   then apply the tag to all of the data types after Scott-encoding them in order to be able to
   choose one particular data type from the family later. This way we get a valid System Fωμ type,
   but it's not a legal pattern functor yet, as it binds one tag and `n` variables responsible for
   recursion and we need to have only one variable responsible for recursion and one tag in order
   to be able to feed a type function to `μ` and actually tie the knot. Thus the next step is
2. Instantiate all the variables responsible for recursion using a single variable applied to
   distinct tags. This way we transform `1` (tag) + `n` (recursion) variables into
   `1` (recursion) + `1` (tag) variables, i.e. just two variables of right kinds, thus the result
   can be passed to `μ`.

We can now look at the `ProdTree`/`Tree` example.

After the first step (which is performed by the `encodeDataN` function, which calls `scottEncode`
internally) we get the following type (I'll save you from the De Bruijn reverse Turing test and
use the Agda notation instead, but note that this is still a System Fωμ type):

> prodTreeTreeReprN =
>   λ (tag : (Set -> Set -> Set) -> (Set -> Set) -> Set)
>       (prodTree : Set -> Set -> Set) (tree : Set -> Set) ->
>         ∀ (R : Set) ->                                     -- Binding the result variable.
>           tag                                              -- Choosing between the two data types.
>             (λ A B                                         -- The two types that `ProdTree` binds.
>                -> (tree (∀ Q -> (A -> B -> Q) -> Q) -> R)  -- Case over the `Prod` constructor.
>                -> R)
>             (λ A                                           -- The type that `Tree` binds.
>                -> (A -> R)                                 -- Case over the `Leaf` constructor.
>                -> (prodTree A A -> R)                      -- Case over the `Fork` constructor.
>                -> R)

Here we lambda-bind `prodTree` and `tree` directly, Scott-encode the definition of the data types
and use `tag` in order to choose between the two data types.

At the next step we instantiate `prodTree` and `tree` (`instantiations` computes the instantiations)
using a single `rec` (`packEncodedDataN` does this):

> prodTreeTreeRepr1 =
>   λ (rec : ((Set -> Set -> Set) -> (Set -> Set) -> Set) -> Set)
>       (tag : (Set -> Set -> Set) -> (Set -> Set) -> Set) ->
>         prodTreeTreeReptN
>           tag
>           (λ A B -> rec λ prodTree tree -> prodTree A B)
>           (λ A   -> rec λ prodTree tree -> tree A)

It only remains to take the fixed point of this pattern functor:

> prodTreeTree = λ tag -> μ prodTreeTreeRepr1 tag

And that's it, `prodTreeTree` is a valid System Fωμ type that encodes the `ProdTree`/`Tree` family.
-}

{- Note [Data description denotations]
Once we compile a data description to a System Fωμ type, we could already take the denotation of
the latter, but then we'd just get an Agda type that encodes the whole family of mutually recursive
data types, while what we really want is getting all the separate data types, not the whole family
at once.

Hence rather than take the denotation directly, we first instantiate the resulting System Fωμ type
using the tags that the data types from the family correspond to. I.e. we call `instantiations` once
again, get an environment of System Fωμ types and take denotations of those. The result then is an
environment of Agda types, each of which represents a data type from the original family of data
types. We only need to extract them from the environment. Unfortunately, Agda lacks top-level
matches, so we do it like this:

>  ProdTreeTree′ = Encoded.⟦ prodTreeTree ⟧ᵈ
>
>  ProdTree′ : Set -> Set -> Set
>  ProdTree′ with ProdTreeTree′
>  ... | ∅ ▷ PT′ ▷ T′ = PT′
>
>  Tree′ : Set -> Set
>  Tree′ with ProdTreeTree′
>  ... | ∅ ▷ PT′ ▷ T′ = T′
-}

-- | Get the kind of tags from the context of a data description.
--
-- > dataConToTagKind (ε ▻ (σ¹₁ ▻ … ▻ σ¹ₙ₁) ▻ … ▻ (σ¹ₘ ▻ … ▻ σᵐₙₘ)) τ =
-- >   (σ¹₁ ⇒ᵏ … ⇒ᵏ σ¹ₙ₁ ⇒ᵏ ⋆) ⇒ᵏ … ⇒ᵏ (σ¹₁ ⇒ᵏ … ⇒ᵏ σᵐₙₘ ⇒ᵏ ⋆) ⇒ᵏ τ
dataConToTagKind : Con Conᵏ -> Kind -> Kind
dataConToTagKind = conToKindBy $ λ Θ -> conToKind Θ ⋆

-- | Scott-encode a single data type. The type variable (denoted as `ρ`) that represents
-- the result is assumed to be in scope, because we Scott-encode a bunch of data types
-- at the same time and hence the resulting type variable has to be bound outside of all of them,
-- which is why we keep it implicit while encoding a single data type.
--
-- > scottEncode (ε ▻ α₁ ▻ … ▻ αₙ) [(β¹₁ ⇒ᶜ … ⇒ᶜ β¹ₙ₁ ⇒ᶜ endᶜ) , … , (βᵐ₁ ⇒ᶜ … ⇒ᶜ βᵐₙₘ ⇒ᶜ endᶜ)] =
-- >     λ α₁ … αₙ → (β¹₁ ⇒ … ⇒ β¹ₙ₁ ⇒ ρ) ⇒ … ⇒ (βᵐ₁ ⇒ … ⇒ βᵐₙₘ ⇒ ρ) ⇒ ρ
scottEncode : ∀ {Ξ} Θ -> List (Cons (Ξ ▻▻ Θ)) -> Ξ ▻ ⋆ ⊢ᵗ conToKind Θ ⋆
scottEncode Θ = Lamⁿ' Θ ∘ foldr (λ ξ γ -> consToType (renᶜ (keepⁿ Θ topᵒ) ξ) ρ ⇒ γ) ρ where
  ρ = renᵗ (extʳ Θ) $ Var vz

-- | Encode a `Data` description as an n-ary type function.
--
-- > encodeDataN (PackData [data¹ , … , dataᵐ]) =
-- >    λ tag δ¹ … δᵐ → tag (scott data¹) … (scott dataᵐ)
--
-- (`δᵢ` is the name of `dataᵢ` that is potentially used internally in any `dataⱼ`,
-- because the data types are allowed to be mutually recursive).
encodeDataN : ∀ {Ξ Θs} -> Data Ξ Θs -> Ξ ⊢ᵗ dataConToTagKind Θs ⋆ ⇒ᵏ dataConToTagKind Θs ⋆
encodeDataN {Ξ} {Θs} (PackData datas) =
  Lam_ ∘′ Lamⁿ Θs ∘′ π ⋆ $′
    applyᵗⁿ Θs
      (Var ∘ vsⁿ $ mapᶜ _ Θs ▻ ⋆)
      (mapˢ (λ {Θ} -> renᵗ (keepⁿ (mapᶜ _ Θs ▻ ⋆) topᵒ) ∘ scottEncode Θ) datas)

-- | Compute all instantiations of a thing of kind `dataConToTagKind Θs ⋆ ⇒ᵏ ⋆`, which is either
-- the first variable that a packed pattern functor binds (i.e. the one responsible for recursion)
-- or the final data type representing a family of mutually recursive data types.
-- "Instantiations" then are particular data types from a family of mutually recursive data types
-- (or represent them if we're are inside a pattern functor).
-- For example, the instantiations of `treeForest` are `tree` and `forest`, i.e. precisely those
-- data types that form the family.
--
-- > instantiations ψ
-- >     = ∅
-- >     ▷ (λ α¹₁ … α¹ₙ₁ → ψ λ β¹ … βᵐ → β¹ α¹₁ … α¹ₙ₁)
-- >     ▷ …
-- >     ▷ (λ αᵐ₁ … αᵐₙₘ → ψ λ β¹ … βᵐ → βᵐ αᵐ₁ … αᵐₙₘ)
instantiations : ∀ {Θs Ξ} -> Ξ ⊢ᵗ dataConToTagKind Θs ⋆ ⇒ᵏ ⋆ -> Seq (λ Θ -> Ξ ⊢ᵗ conToKind Θ ⋆) Θs
instantiations {ε}      ψ = ø
instantiations {Θs ▻ Θ} ψ
  = instantiations {Θs} (Lam_ $ shiftᵗ ψ ∙
      Lamⁿ (Θs ▻ Θ) (applyᵗⁿ Θs (Var (vsⁿ (mapᶜ _ (Θs ▻ Θ)))) (mapˢ shiftᵗ subVars)))
  ▶ Lamⁿ' Θ (shiftᵗⁿ Θ ψ ∙
      Lamⁿ (Θs ▻ Θ) (applyᵗⁿ Θ (Var vz) (mapˢ (shiftᵗⁿ (mapᶜ _ $ Θs ▻ Θ)) subVars')))

-- | Pack an encoded family of mutually recursive data types as an 1-ary pattern functor.
-- The encoded family is of this form (see `encodeDataN`):
--
-- > φ : ((σ¹₁ ⇒ᵏ … ⇒ᵏ σ¹ₙ₁ ⇒ᵏ ⋆) ⇒ᵏ … ⇒ᵏ (σᵐ₁ ⇒ᵏ … ⇒ᵏ σᵐₙₘ ⇒ᵏ ⋆) ⇒ᵏ ⋆)
-- >   ⇒ᵏ (σ¹₁ ⇒ᵏ … ⇒ᵏ σ¹ₙ₁ ⇒ᵏ ⋆) ⇒ᵏ … ⇒ᵏ (σᵐ₁ ⇒ᵏ … ⇒ᵏ σᵐₙₘ ⇒ᵏ ⋆) ⇒ᵏ ⋆
-- > φ = λ tag δ¹ … δᵐ → <body>
--
-- Where `tag` is a tag and `δʲ` is a variable that stands for a data type from the family.
--
-- The definition of `packEncodedDataN` then is
--
-- > packEncodedDataN _ φ =
-- >     λ rec tag → φ tag
-- >         (λ α¹₁ … α¹ₙ₁ → rec λ ψ¹ … ψᵐ → ψ¹ α¹₁ … α¹ₙ₁)
-- >         …
-- >         (λ αᵐ₁ … αᵐₙₘ → rec λ ψ¹ … ψᵐ → ψᵐ αᵐ₁ … αᵐₙₘ)
--
-- where `αʲᵢ` is a parameter of a data type and `λ ψ¹ … ψᵐ → ψʲ αʲ₁ … αʲᵢ` is the tag of
-- the data type. That is, we put parameters of data types into their corresponding tags.
--
-- So we instantiate each data type argument of `φ` as `rec` applied to an appropriate tag. This
-- way we represent all of the data types using just a single `rec` applied to different tags.
packEncodedDataN
  : ∀ {Ξ} Θs
  -> Ξ ⊢ᵗ dataConToTagKind Θs ⋆ ⇒ᵏ dataConToTagKind Θs ⋆
  -> Ξ ⊢ᵗ (dataConToTagKind Θs ⋆ ⇒ᵏ ⋆) ⇒ᵏ dataConToTagKind Θs ⋆ ⇒ᵏ ⋆
packEncodedDataN Θs φ =
  Lam_ ∘′ Lam_ ∘′ applyᵗⁿ Θs (shiftᵗⁿ (ε ▻ _ ▻ _) φ ∙ Var vz) ∘′ instantiations $ Var (vs vz)

-- | Encode a `Data` as a 1-ary pattern functor.
encodeData1
  : ∀ {Ξ Θs} -> Data Ξ Θs -> Ξ ⊢ᵗ (dataConToTagKind Θs ⋆ ⇒ᵏ ⋆) ⇒ᵏ dataConToTagKind Θs ⋆ ⇒ᵏ ⋆
encodeData1 {Θs = Θs} = packEncodedDataN Θs ∘ encodeDataN

-- | Compile a `Data` to System Fωμ.
compileData : ∀ {Ξ Θs} -> Data Ξ Θs -> Ξ ⊢ᵗ dataConToTagKind Θs ⋆ ⇒ᵏ ⋆
compileData d = Lam μ (shiftᵗ $ encodeData1 d) (Var vz)

compileDatas : ∀ {Ξ Θs} -> Data Ξ Θs -> Seq (λ Θ -> Ξ ⊢ᵗ conToKind Θ ⋆) Θs
compileDatas = instantiations ∘ compileData

-- | Return the denotations of all the data types from a family of mutually recursive data types
-- encoded as a `Data`.
⟦_⟧ᵈ : ∀ {Θs} -> Data ε Θs -> Seq (λ Θ -> ⟦ conToKind Θ ⋆ ⟧ᵏ) Θs
⟦_⟧ᵈ = mapˢ ⟦_⟧ᵗ ∘ compileDatas

module Unused where
  constructorTypes : ∀ {Θs Ξ} -> Data Ξ Θs -> Con (Star (Ξ ▻▻ mapᶜ (λ Θᵢ -> conToKind Θᵢ ⋆) Θs))
  constructorTypes {Θs} {Ξ} (PackData constructors) =
    joinᶜ ∘′ eraseˢ $′ mapElˢ consesToCon constructors where
      consesToCon
        : ∀ {Θ}
        -> Θ ∈ Θs
        -> List (Cons (Ξ ▻▻ mapᶜ (λ Θᵢ -> conToKind Θᵢ ⋆) Θs ▻▻ Θ))
        -> Con (Star (Ξ ▻▻ mapᶜ (λ Θᵢ -> conToKind Θᵢ ⋆) Θs))
      consesToCon {Θ} v = listToCon ∘ List.map (λ ξ -> πⁿ' Θ $ consToType ξ ρ) where
        ρ = applyᵗⁿ Θ (Var ∘ renᵛ (skipⁿ Θ extˡ) $ mapᵛ v) subVars'

  constructorFullTypes : ∀ {Θs Ξ} -> Data Ξ Θs -> Con (Star Ξ)
  constructorFullTypes δ = mapᶜ (instᵗⁿ $ compileDatas δ) $ constructorTypes δ
