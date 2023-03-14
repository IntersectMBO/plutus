\begin{code}
module Algorithmic where
\end{code}

## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong;trans;sym;cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Function using (_∘_)

open import Utils hiding (TermCon)
open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;_∋⋆_;Z;S;Φ)
open _⊢⋆_

open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;weakenNf;renNf;embNf)
open _⊢Nf⋆_
open _⊢Ne⋆_

import Type.RenamingSubstitution as ⋆
open import Type.BetaNBE using (nf)
open import Type.BetaNBE.RenamingSubstitution 
                         using (subNf;SubNf;renNf-subNf;subNf-cong;subNf-comp) 
                         renaming (_[_]Nf to _[_])
open import Type.BetaNBE.Stability using (stability)

open import Builtin using (Builtin;signature)
open Builtin.Builtin
open import Builtin.Signature using (Sig;sig;nat2Ctx⋆;fin2∈⋆)

open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con using (TermCon)
open import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *) using (TyCon)
open TyCon

open Builtin.Signature.FromSig Ctx⋆ (_⊢Nf⋆ *) nat2Ctx⋆ (λ x → ne (` (fin2∈⋆ x))) con _⇒_ Π using (sig2type)
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgements, types, and terms.
\begin{code}
infix  4 _∋_
infix  4 _⊢_
infixl 5 _,_
\end{code}

## Contexts and erasure

We need to mutually define contexts and their
erasure to type contexts.
\begin{code}
--data Ctx : Set
--∥_∥ : Ctx → Ctx⋆
\end{code}

A context is either empty, or extends a context by
a type variable of a given kind, or extends a context
by a variable of a given type.
\begin{code}
data Ctx : Ctx⋆ → Set where
  ∅    : Ctx ∅
  _,⋆_ : Ctx Φ → (J : Kind) → Ctx (Φ ,⋆ J)
  _,_  : (Γ : Ctx Φ) → Φ ⊢Nf⋆ * → Ctx Φ
\end{code}
Let `Γ` range over contexts.  In the last rule,
the type is indexed by the erasure of the previous
context to a type context and a kind.

The erasure of a context is a type context.
\begin{code}
--∥ ∅ ∥       =  ∅
--∥ Γ ,⋆ J ∥  =  ∥ Γ ∥ ,⋆ J
--∥ Γ , A ∥   =  ∥ Γ ∥
\end{code}

## Variables

A variable is indexed by its context and type.
\begin{code}
data _∋_ : (Γ : Ctx Φ) → Φ ⊢Nf⋆ * → Set where

  Z : ∀ {Γ} {A : Φ ⊢Nf⋆ *}
      ----------
    → Γ , A ∋ A

  S : ∀ {Γ} {A : Φ ⊢Nf⋆ *} {B : Φ ⊢Nf⋆ *}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A

  T : ∀ {Γ K}{A : Φ ⊢Nf⋆ *}
    → Γ ∋ A
      -------------------
    → Γ ,⋆ K ∋ weakenNf A
\end{code}


\begin{code}
btype : Builtin → Φ ⊢Nf⋆ *
btype b = subNf (λ()) (sig2type (signature b))

btype-∅ : ∀ {A : ∅ ⊢Nf⋆ *} → A ≡ subNf {∅} {∅} (λ()) {*} A
btype-∅ {A} = begin
             A
            ≡⟨ sym (stability A) ⟩
             nf (embNf A)
           ≡⟨ cong nf (sym (⋆.sub-∅ (embNf A)  (embNf ∘  λ()))) ⟩
             nf (⋆.sub (embNf ∘ λ()) (embNf A))
           ≡⟨ refl ⟩
             subNf (λ ()) A
           ∎

btype-sig2type : ∀ (b : Builtin) → btype {∅} b ≡ sig2type (signature b)
btype-sig2type b = sym btype-∅

btype-ren : ∀{Φ Ψ} b (ρ : ⋆.Ren Φ Ψ) → btype b ≡ renNf ρ (btype b)
btype-ren b ρ = begin
             btype b
             ≡⟨ refl ⟩
             subNf (λ()) (sig2type (signature b))
             ≡⟨ subNf-cong {f = λ()} {renNf ρ ∘ λ ()} (λ ()) (sig2type (signature b)) ⟩
             subNf (renNf ρ ∘ λ ()) (sig2type (signature b))
             ≡⟨ renNf-subNf (λ()) ρ (sig2type (signature b)) ⟩
             renNf ρ (btype b)
           ∎

btype-sub : ∀{Φ Ψ} b (ρ : SubNf Φ Ψ) → btype b ≡ subNf ρ (btype b)
btype-sub b ρ = begin 
           btype b
          ≡⟨ refl ⟩
           subNf (λ()) (sig2type (signature b))
          ≡⟨ subNf-cong {f = λ()} {subNf ρ ∘ λ ()} (λ ()) (sig2type (signature b)) ⟩
            subNf (subNf ρ ∘ (λ ())) (sig2type (signature b))
          ≡⟨ subNf-comp (λ()) ρ (sig2type (signature b)) ⟩
           subNf ρ (subNf (λ()) (sig2type (signature b)))
          ≡⟨ refl ⟩
           subNf ρ (btype b)
          ∎

postulate sub-Π : ∀{n}{A : (nat2Ctx⋆ n) ⊢Nf⋆ *}{B} →  (Π B) [ A ] ≡ Π (B [ weakenNf A ])
\end{code}
          
Let `x`, `y` range over variables.

## Terms

A term is indexed over by its context and type.  A term is a variable,
an abstraction, an application, a type abstraction, or a type
application.

\begin{code}
infixl 7 _·⋆_/_

data _⊢_ (Γ : Ctx Φ) : Φ ⊢Nf⋆ * → Set where

  ` : ∀ {A : Φ ⊢Nf⋆ *}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ : ∀ {A B : Φ ⊢Nf⋆ *}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {A B : Φ ⊢Nf⋆ *}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  Λ : ∀ {K}
    → {B : Φ ,⋆ K ⊢Nf⋆ *}
    → Γ ,⋆ K ⊢ B
      -------------------
    → Γ ⊢ Π B

  _·⋆_/_ : ∀ {K C}
    → {B : Φ ,⋆ K ⊢Nf⋆ *}
    → Γ ⊢ Π B
    → (A : Φ ⊢Nf⋆ K)
    → C ≡ B [ A ]
      --------------
    → Γ ⊢ C

  wrap : ∀{K}
   → (A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)
   → (B : Φ ⊢Nf⋆ K)
   → Γ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)
     -------------------------------------------------------------
   → Γ ⊢ μ A B

  unwrap : ∀{K C}
    → {A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : Φ ⊢Nf⋆ K}
    → Γ ⊢ μ A B
    → C ≡ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)
      -------------------------------------------------------------
    → Γ ⊢ C

  con : ∀{tcn}
    → TermCon {Φ} (con tcn)
      ---------------------
    → Γ ⊢ con tcn

  builtin_/_ : ∀{C}
    → (b :  Builtin)
    → C ≡ btype b
      --------------
    → Γ ⊢ C

  error :
      (A : Φ ⊢Nf⋆ *)
      --------------
    → Γ ⊢ A
\end{code}

Utility functions

\begin{code}
conv∋ : ∀ {Γ Γ'}{A A' : Φ ⊢Nf⋆ *}
 → Γ ≡ Γ'
 → A ≡ A'
 → Γ ∋ A
 → Γ' ∋ A'
conv∋ refl refl x = x

conv⊢ : ∀ {Γ Γ'}{A A' : Φ ⊢Nf⋆ *}
 → Γ ≡ Γ'
 → A ≡ A'
 → Γ ⊢ A
 → Γ' ⊢ A'
conv⊢ refl refl t = t

Ctx2type : (Γ : Ctx Φ) → Φ ⊢Nf⋆ * → ∅ ⊢Nf⋆ *
Ctx2type ∅        C = C
Ctx2type (Γ ,⋆ J) C = Ctx2type Γ (Π C)
Ctx2type (Γ , x)  C = Ctx2type Γ (x ⇒ C)
\end{code}
 