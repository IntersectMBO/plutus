\begin{code}
module Algorithmic where
\end{code}

## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;trans;cong;cong₂;subst)

open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.Product using (_×_)
open import Data.Vec as Vec using (Vec;[];_∷_;lookup) 
open import Data.List.Properties using (foldr-++)

open import Utils renaming (_×_ to _U×_; List to UList; map to umap)
open import Utils.List using (List;_++_;foldr;IList;[];_∷_;Bwd;_:<_;bwd-foldr;lemma-bwd-foldr;_<><_;lemma<>1)
open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;_∋⋆_;Z;S;Φ)
open _⊢⋆_

open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;weakenNf;renNf;embNf)
open _⊢Nf⋆_
open _⊢Ne⋆_

import Type.RenamingSubstitution as ⋆
open import Type.BetaNBE using (nf)
open import Type.BetaNBE.RenamingSubstitution using (subNf∅) renaming (_[_]Nf to _[_])

open import Builtin using (Builtin)

open import Builtin.Constant.Type using (TyCon)
open TyCon
open import Builtin.Constant.AtomicType using (⟦_⟧at)

open import Builtin.Signature using (_⊢♯)
open _⊢♯

open import Algorithmic.Signature using (btype;⊢♯2TyNe♯)
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
          
## Semantic of constant terms

We define a predicate ♯Kinded for kinds that ultimately end in ♯.

\begin{code}
data ♯Kinded : Kind → Set where
   ♯ : ♯Kinded ♯
   K♯ : ∀{K J} → ♯Kinded J → ♯Kinded (K ⇒ J)
\end{code}

There is no type of a ♯Kinded kind which takes more than two type arguments. 

\begin{code}
lemma♯Kinded : ∀ {K K₁ K₂ J} → ♯Kinded J → ∅ ⊢Ne⋆ (K₂ ⇒ (K₁ ⇒ (K ⇒ J))) → ⊥
lemma♯Kinded k (f · _) = lemma♯Kinded (K♯ k) f
\end{code}

Closed types can be mapped into the signature universe and viceversa.

\begin{code}
ty2sty : ∅ ⊢Nf⋆ ♯ → 0 ⊢♯
ty2sty (ne (((f · _) · _) · _)) with lemma♯Kinded ♯ f 
... | ()
ty2sty (ne ((^ pair · x) · y)) = pair (ty2sty x) (ty2sty y)
ty2sty (ne (^ list · x)) = list (ty2sty x)
ty2sty (ne (^ (atomic x))) = atomic x

sty2ty : 0 ⊢♯ → ∅ ⊢Nf⋆ ♯
sty2ty t = ne (⊢♯2TyNe♯ t)
\end{code}

Now we have functions `ty2sty` and `sty2ty`. We prove that they are inverses, and therefore
define an isomorphism.

\begin{code}
ty≅sty₁ : ∀ (A : ∅ ⊢Nf⋆ ♯) → A ≡ sty2ty (ty2sty A)
ty≅sty₁ (ne (((f · _) · _) · _)) with  lemma♯Kinded ♯ f
... | ()
ty≅sty₁ (ne ((^ pair · x) · y))  = cong ne (cong₂ _·_ (cong (^ pair ·_) (ty≅sty₁ x)) (ty≅sty₁ y))
ty≅sty₁ (ne (^ list · x))        = cong ne (cong (^ list ·_) (ty≅sty₁ x)) 
ty≅sty₁ (ne (^ (atomic x)))      = refl

ty≅sty₂ : ∀ (A : 0 ⊢♯) →  A ≡ ty2sty (sty2ty A)
ty≅sty₂ (atomic x) = refl
ty≅sty₂ (list A) = cong list (ty≅sty₂ A)
ty≅sty₂ (pair A B) = cong₂ pair (ty≅sty₂ A) (ty≅sty₂ B)
\end{code}

The semantics of closed types of kind ♯ is given by the following 
interpretation function

\begin{code}
⟦_⟧ : (ty : ∅ ⊢Nf⋆ ♯) → Set
⟦ ne (((f · _) · _) · _) ⟧ with lemma♯Kinded ♯ f 
... | ()
⟦ ne ((^ pair · x) · y) ⟧ = ⟦ x ⟧ U× ⟦ y ⟧
⟦ ne (^ list · x) ⟧ = UList ⟦ x ⟧
⟦ ne (^ (atomic x)) ⟧ = ⟦ x ⟧at
\end{code}

All these types need to be able to be interfaced with Haskell, as this 
interpretation function is used everywhere of type or a type tag needs to be 
interpreted. It is precisely because they need to be interfaced with Haskell
that we use the version of product and list from the Utils module.

## Terms

A term is indexed over by its context and type.  A term is a variable,
an abstraction, an application, a type abstraction, a type
application, a wrapping or unwrapping of a recursive type, a constructor, 
a case expression, a constant, a builtin function, or an error.

Constants of a builtin type A are given directly by its meaning ⟦ A ⟧, where
A is restricted to kind ♯.

The type of cases if a function consuming every type in a list.
We construct it with the following function: 
\begin{code}
mkCaseType : ∀{Φ} (A : Φ ⊢Nf⋆ *) → List (Φ ⊢Nf⋆ *) → Φ ⊢Nf⋆ *
mkCaseType A = foldr _⇒_ A
\end{code}

We declare two auxiliary datatypes, which are mutually recursive with the type of terms,
for constructor arguments and cases.

\begin{code}
ConstrArgs : (Γ : Ctx Φ) → List (Φ ⊢Nf⋆ *) → Set
data Cases (Γ : Ctx Φ) (B : Φ ⊢Nf⋆ *) : ∀{n} → Vec (List (Φ ⊢Nf⋆ *)) n → Set 
\end{code}

The actual type of terms

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

  constr : ∀{n}
      → (i : Fin n)                   -- The tag

      → (A : Vec (List (Φ ⊢Nf⋆ *)) n) -- The sum of products. We make it a Vector
                                      -- of lists, so that the tag is statically correct.
      
      → ∀ {ts} → ts ≡ lookup A i      -- The reason to define it like this, rather than
      → ConstrArgs Γ ts               -- simply ConstrArgs Γ (lookup A e) 
                                      -- is so that it is easier to construct terms (avoids using subst)
                                      -- as often the result of a function will not match definitionally
                                      -- with (lookup A e) but only propositionally.
        --------------------------------------
      → Γ ⊢ SOP A

  case : ∀{n}{tss : Vec _ n}{A : Φ ⊢Nf⋆ *}
      → (t : Γ ⊢ SOP tss)
      → (cases : Cases Γ A tss)
        --------------------------
      → Γ ⊢ A  

  con : ∀{A : ∅ ⊢Nf⋆ ♯}{B}
    → ⟦ A ⟧ 
    → B ≡ subNf∅ A
      ---------------------
    → Γ ⊢ con B

  builtin_/_ : ∀{C}
    → (b :  Builtin)
    → C ≡ btype b
      --------------
    → Γ ⊢ C

  error :
      (A : Φ ⊢Nf⋆ *)
      --------------
    → Γ ⊢ A

ConstrArgs Γ = IList (Γ ⊢_)

-- Cases is indexed by a vector 
-- so it can't be an IList
data Cases Γ B where 
   []  : Cases Γ B []
   _∷_ : ∀{n}{AS}{ASS : Vec _ n}(
         c : Γ ⊢ (mkCaseType B AS)) 
       → (cs : Cases Γ B ASS)
         --------------------- 
       → Cases Γ B (AS ∷ ASS) 
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

lookupCase : ∀{n Φ}{Γ : Ctx Φ}{B}{TSS : Vec _ n} → (i : Fin n) → Cases Γ B TSS → Γ ⊢ mkCaseType B (Vec.lookup TSS i)
lookupCase Fin.zero (c ∷ cs) = c
lookupCase (Fin.suc i) (c ∷ cs) = lookupCase i cs

bwdMkCaseType : ∀{Φ} → Bwd (Φ ⊢Nf⋆ *) → (A : Φ ⊢Nf⋆ *) → Φ ⊢Nf⋆ *
bwdMkCaseType bs A = bwd-foldr _⇒_ A bs

lemma-bwdfwdfunction' : ∀{Φ} {B : Φ ⊢Nf⋆ *} TS → mkCaseType B TS ≡ bwdMkCaseType ([] <>< TS) B
lemma-bwdfwdfunction' {B = B} TS = trans (cong (mkCaseType B) (sym (lemma<>1 [] TS))) (lemma-bwd-foldr _⇒_ B ([] <>< TS))         

constr-cong :  ∀{Γ : Ctx Φ}{n}{i : Fin n}{A : Vec (List (Φ ⊢Nf⋆ *)) n}{ts} 
            → (p : ts ≡ lookup A i)
            → {cs : ConstrArgs Γ ts}
            → {cs' : ConstrArgs Γ (lookup A i)}
            → (q : cs' ≡ subst (IList (Γ ⊢_)) p cs)
            → constr i A refl cs' ≡ constr i A p cs
constr-cong refl refl = refl
\end{code}