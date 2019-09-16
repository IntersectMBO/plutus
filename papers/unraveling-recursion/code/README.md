# Contents

This formalization consists of two parts:

1. type-level compilation of mutually recursive IR data types into System F-omega-mu
2. term-level compilation of mutually recursive IR functions into System F-omega-mu

Most notably, we do not have term-level compilation of IR data types into System F-omega-mu.
I.e. we compile type-level representations of data types, but do not compile constructors.
Compilation of constructors is future work (see below on why this is the case).

# The type level

We have intrinsically typed syntax for types and terms. Types are

```agda
mutual
  -- | Types of kind `⋆`.
  Star : Conᵏ -> Set
  Star Θ = Θ ⊢ᵗ ⋆

  -- | A type is defined in a context and has a kind.
  data _⊢ᵗ_ Θ : Kind -> Set where
    Var  : ∀ {σ} -> σ ∈ Θ -> Θ ⊢ᵗ σ                              -- Variable.
    Lam_ : ∀ {σ τ} -> Θ ▻ σ ⊢ᵗ τ -> Θ ⊢ᵗ σ ⇒ᵏ τ                  -- Lambda abstraction.
    _∙_  : ∀ {σ τ} -> Θ ⊢ᵗ σ ⇒ᵏ τ -> Θ ⊢ᵗ σ -> Θ ⊢ᵗ τ            -- Application.
    _⇒_  : Star Θ -> Star Θ -> Star Θ                            -- Arrow.
    π    : ∀ σ -> Star (Θ ▻ σ) -> Star Θ                         -- Universal quantifier.
    μ    : ∀ {κ} -> Θ ⊢ᵗ (κ ⇒ᵏ ⋆) ⇒ᵏ κ ⇒ᵏ ⋆ -> Θ ⊢ᵗ κ -> Star Θ  -- Indexed fixed-point combinator.
```

which is a standard representation of System F-omega extended with an indexed fixed-point combinator
that allows to define recursive types.

Terms are discussed below.

# Compilation of data types

Type-level compilation of data types is done fully and commented. Relevant modules are

1. [`Compilation.Data`](src/Compilation/Data.agda) -- The definition of IR data types.
2. [`Compilation.Encode.Core`](src/Compilation/Encode/Core.agda) -- Compilation of IR data types into System F-omega-mu.
3. [`Compilation.Encode.Examples`](src/Compilation/Encode/Examples.agda) -- Examples of IR data types and their encodings.

Since System F-omega-mu is impredicative, we enable `{-# OPTIONS --type-in-type #-}` in some of the files. Since the indexed fixed-point combinator allows to define non-strictly-positive data types (including negative ones), we enable `{-# NO_POSITIVITY_CHECK #-}` for the denotation of this combinator in Agda (called `IFix`). `Example.agda` also enables `{-# TERMINATING #-}` for *conversions* between original and encoded data types, because Agda is unable to see that conversions terminate (they do).

The reason why we do not have compilation of constructors is not that it's hard to get what is required at the term level. The hard part is to compile constructors in such a way that they have exactly the same types that we compile data types to. I.e. we have the entire data type compilation pipeline at the type level if we attempt to compile constructors. Here is how a function that compiles constructors would look like:

```agda
constructors : ∀ {Θs Ξ Γ} -> (δ : Data Ξ Θs) -> Seq (Γ ⊢_) (constructorFullTypes δ)
constructors = {!!}
```

The problem is that the normalized type of the goal is this:

<details>
  <summary> Goal </summary>
  <p>

```agda
Goal: (δ : Data .Ξ .Θs) →
      Seq (_⊢_ .Γ)
      (foldlᶜ
       (λ Ξ x →
          Ξ ▻
          instᵗⁿ
          (instantiations
           (Lam
            μ
            (Lam
             (Lam
              renᵗ (keep (keep (λ {_} x₁ → vs x₁)))
              (applyᵗⁿ .Θs
               ((Lam
                 renᵗ (keep (λ {_} x₁ → vs (vs x₁)))
                 (Lamⁿ .Θs
                  (π ⋆
                   (applyᵗⁿ .Θs
                    (Var
                     (vs
                      vsⁿ (foldlᶜ (λ Ξ₁ x₁ → Ξ₁ ▻ foldrᶜ (λ x₂ → _⇒ᵏ_ x₂) ⋆ x₁) ε .Θs)))
                    (foldlˢ
                     (Seq
                      (λ σ →
                         .Ξ ▻ foldrᶜ (λ x₁ → _⇒ᵏ_ (foldrᶜ (λ x₂ → _⇒ᵏ_ x₂) ⋆ x₁)) ⋆ .Θs ▻▻
                         foldlᶜ (λ Ξ₁ x₁ → Ξ₁ ▻ foldrᶜ (λ x₂ → _⇒ᵏ_ x₂) ⋆ x₁) ε .Θs
                         ▻ ⋆
                         ⊢ᵗ foldrᶜ (λ x₁ → _⇒ᵏ_ x₁) ⋆ σ))
                     (λ {.Ξ} {.σ} ρ x₁ →
                        ρ ▶
                        renᵗ
                        (λ {z} →
                           keep
                           (keepⁿ (foldlᶜ (λ Ξ₁ x₂ → Ξ₁ ▻ foldrᶜ (λ x₃ → _⇒ᵏ_ x₃) ⋆ x₂) ε .Θs)
                            (λ {_} x₂ → vs x₂)))
                        (Lamⁿ' .σ
                         (foldr
                          (λ ξ →
                             _⇒_
                             (consToType (renᶜ (keepⁿ .σ (λ {_} x₂ → vs x₂)) ξ)
                              (Var (skipⁿ .σ (λ {.σ₁} x₂ → x₂) vz))))
                          (Var (skipⁿ .σ (λ {.σ₁} x₂ → x₂) vz)) x₁)))
                     ø (Data.constructors δ))))))
                ∙ Var vz)
               (instantiations (Var (vs vz))))))
            (Var vz)))
          x)
       ε
       (foldlᶜ (λ Γ Δ → Γ ▻▻ Δ) ε
        (foldlˢ
         (λ v →
            Con
            (Con
             (.Ξ ▻▻ foldlᶜ (λ Ξ x → Ξ ▻ foldrᶜ (λ x₁ → _⇒ᵏ_ x₁) ⋆ x) ε .Θs ⊢ᵗ
              ⋆)))
         (λ {.Ξ} {.σ} → _▻_) ε
         (mapElˢ
          (λ {Θ} v x →
             listToCon
             (map
              (λ ξ →
                 πⁿ' Θ
                 (consToType ξ
                  (applyᵗⁿ Θ (Var (skipⁿ Θ (λ {.σ₁} → extˡ) (mapᵛ v))) subVars')))
              x))
          (Data.constructors δ)))))
```
</p></details>

# Compilation of functions

System F-omega-mu terms are

```agda
data _⊢_ : ∀ {Θ} -> Con (Star Θ) -> Star Θ -> Set where
  var  : ∀ {Θ Γ} {α : Star Θ}   -> α ∈ Γ -> Γ ⊢ α
  Λ_   : ∀ {Θ Γ σ} {α : Star (Θ ▻ σ)} -> shiftᶜ Γ ⊢ α -> Γ ⊢ π σ α
  -- A normalizing at the type level type instantiation.
  _[_] : ∀ {Θ Γ σ} {β : Star (Θ ▻ σ)} -> Γ ⊢ π σ β -> (α : Θ ⊢ᵗ σ) -> Γ ⊢ β [ α ]ᵗ
  -- A non-normalizing at the type level type instantiation.
  _<_> : ∀ {Θ Γ σ} {β : Star (Θ ▻ σ)} -> Γ ⊢ π σ β -> (α : Θ ⊢ᵗ σ) -> Γ ⊢ β < α >ᵗ
  -- A shorthand for `_< Var vz >` with more convenient computation at the type level.
  _<>  : ∀ {Θ σ Γ} {β : Star (Θ ▻ σ ▻ σ)} -> Γ ⊢ π σ β -> Γ ⊢ unshiftᵗ β
  ƛ_   : ∀ {Θ Γ} {α β : Star Θ} -> Γ ▻ α ⊢ β -> Γ ⊢ α ⇒ β
  _·_  : ∀ {Θ Γ} {α β : Star Θ} -> Γ ⊢ α ⇒ β -> Γ ⊢ α -> Γ ⊢ β
  iwrap  : ∀ {Θ Γ κ ψ} {α : Θ ⊢ᵗ κ} -> Γ ⊢ unfold ψ α -> Γ ⊢ μ ψ α
  unwrap : ∀ {Θ Γ κ ψ} {α : Θ ⊢ᵗ κ} -> Γ ⊢ μ ψ α -> Γ ⊢ unfold ψ α
```

Here all constructors are either standard ones (`var`, `Λ_`, `_[_]`, `ƛ_`, `_·_`) or come together with the indexed fixed-point combinator (`iwrap`, `unwrap`) except these two:

1. `_<_>` -- this constructor is similar to `_[_]` in that it allows to perform type instantiation, however at the type level type instantiation does not result in full normalization like with `_[_]`. Instead, `_<_>` performs non-normalizing substitution at the type-level.
2. `_<>` is an even more restricted type instantiation operator. It is equivalent to `_< Var vz >`.
At the type level it takes the predecessor of the index of each type-level variable except for the outermost one which it doesn't touch.

So in total we get three type instantiation operators. Such a zoo is needed, because

1. We generate F-omega-mu types and terms in a type-driven way in Agda itself. I.e. we generate terms with open target types at the meta level and this is a rather non-trivial thing to do, because normalization at the type level in the target language gets stuck when it encounters a metavariable (i.e. a variable bound in Agda rather than in System F-omega-mu). So in the end we need to deal with weird meta-theoretical type-level constructs while defining terms in the target language

2. While performing translation from IR to System F-omega-mu we want to preserve the non-normalizedness of types. `_[_]` is a big hammer that normalizes everything (it uses [McBride-style NbE](https://github.com/pigworker/SSGEP-DataData/blob/master/STLC.lagda#L615) under the hood), so term-level type instantiation requires substitution at the type-level, which can result in reduction of completely unrelated to the substitution redexes. This immediately causes problems for compilation: a type and its normalized version are not definitionally the same, so we need some way to convince the type checker that the normalized version does correspond to the original one somehow.

So we just extend the term-level language with constructs that perform *less* normalization at the type level. This allows to transform IR terms to F-omega-mu terms and keep types *definitionally* the same. Less normalization at the type level in cases where it's not needed = much less trouble to deal with. For terms with closed types we still use `_[_]`, because the aforementioned problems arise only when we need to deal with terms that contain open types.

Even if we're willing to compile IR terms to System F-omega-mu terms not extended with those two additional type instantiation operators, it's still easier to compile IR terms to extended System F-omega-mu terms and then compile the latter to non-extended terms.

Term-level compilation is not done fully. Things that are not implemented:

1. no compilation of data types at the term level (due to the lack of compilation of constructors). I.e. we only compile mutually recursive functions and single let-bound types
2. we have the following `postulate`:

```agda
postulate
  shift-⊢ : ∀ {Θ Γ β} {α : Star Θ} -> Γ ⊢ α -> shiftᶜ {τ = β} Γ ⊢ shiftᵗ α
```

This theorem says that any term that is defined in context `Γ` and has type `α` can be converted to a term that

1. is defined in the same context `Γ`, but with all variable indices increased by one
2. has the same type `α`, but with all variable indices increased by one as well

This is a pretty sensible thing to say, but it's a huge amount of work to prove this, because it requires proving that renaming goes fine through type-level normalization. So this is future work.

It is also the case that term-level compilation assumes that we compile to a lazy version of System F-omega-mu.

Finally, we use `{-# OPTIONS --rewriting #-}` in order to avoid death by a thousand paper cuts, where "paper cut" = explicitly rewriting the current context by some trivial lemma. We enable implicit rewriting like this (only in `Term.Core`):

```agda
{-# BUILTIN REWRITE _≡_ #-}
```

All theorems used for rewriting are proved. No fancy features are used (like the combination of irrelevance and rewriting).
