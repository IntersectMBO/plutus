---
title: Algorithmic.ReductionEC.Determinism
layout: page
---
```
module Algorithmic.ReductionEC.Determinism where
```
## Imports

```
open import Data.Nat using (suc)
open import Data.Fin using (Fin)
open import Data.Empty using (⊥;⊥-elim)
open import Data.Vec as Vec using (lookup)
open import Data.Product using (Σ;_×_;∃) renaming (_,_ to _,,_)
open import Data.List.Properties using (∷-injective)
open import Relation.Nullary using (¬_;yes;no)
open import Relation.Binary.PropositionalEquality 
                    using (_≡_;refl;sym;trans;cong;cong₂;subst-subst;subst-injective)  
                    renaming (subst to substEq)
open import Relation.Binary.HeterogeneousEquality 
        using (_≅_;refl;≅-to-≡) 

open import Utils hiding (_×_;List)
open import Utils.List
open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;_∋⋆_;Z)
open _⊢⋆_
import Type.RenamingSubstitution as T
open import Algorithmic using (Ctx;_⊢_;conv⊢;ConstrArgs;constr-cong)
open Ctx
open _⊢_
open import Algorithmic.RenamingSubstitution using (_[_];_[_]⋆)
open import Algorithmic.Properties using (lem-·⋆;lem-unwrap)
open import Algorithmic.Signature using (SigTy;convSigTy;uniqueSigTy;_[_]SigTy)
open import Type.BetaNBE using (nf)
open import Type.BetaNBE.RenamingSubstitution using (_[_]Nf)
open import Type.BetaNormal using (_⊢Nf⋆_;embNf;weakenNf)
open _⊢Nf⋆_
open import Algorithmic.ReductionEC
open import Builtin using (Builtin;signature)
open import Builtin.Signature using (Sig;args♯;fv)
open Sig
```

```
lemΛE'' : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}
  → ∀{L : ∅ ,⋆ K ⊢ B}{X}{L' : ∅ ⊢ X}
  → (E : EC (Π B) X)
  → Λ L ≅ E [ L' ]ᴱ
  → ∃ λ (p : X ≡ Π B)
  → substEq (EC (Π B)) p E ≡ EC.[] × Λ L ≡ substEq (∅ ⊢_) p L'
lemΛE'' [] refl = refl ,, refl ,, refl

conv∔≣ : ∀{tt tt' tn tm tn' tm'}
  → (tn'  ∔ tm'  ≣ tt') 
  → tt ≡ tt' → tn ≡ tn' → tm ≡ tm'
  → tn ∔ tm ≣ tt
conv∔≣ p refl refl refl = p

conv∔≣t : ∀{b b' tn tm tn' tm'}
  → b ≡ b'
  → (tn'  ∔ tm'  ≣ fv (signature b')) 
  → tn ≡ tn' → tm ≡ tm'
  → tn ∔ tm ≣ fv (signature b)
conv∔≣t refl pt = conv∔≣ pt refl  

conv∔≣a : ∀{b b' an am an' am'}
  → b ≡ b'
  → (an'  ∔ am'  ≣ args♯ (signature b')) 
  → an ≡ an' → am ≡ am'
  → an ∔ am ≣ args♯ (signature b)
conv∔≣a refl pa = conv∔≣ pa refl  

uniqueVal : ∀{A}(M : ∅ ⊢ A)(v v' : Value M) → v ≡ v'

uniqueVal-List : ∀{As : Bwd (∅ ⊢Nf⋆ *)}{cs : IBwd (∅ ⊢_) As} → (vs vs' : VList cs) → vs ≡ vs'
uniqueVal-List [] [] = refl
uniqueVal-List (vs :< x) (vs' :< x') = cong₂ _:<_ (uniqueVal-List vs vs') (uniqueVal _ x x')


uniqueBApp : ∀{A b}
  → ∀{tn tm}{pt : tn ∔ tm ≣ fv (signature b)}
  → ∀{an am}{pa : an ∔ am ≣ args♯ (signature b)}
  → {σA : SigTy pt pa A}
  → (M : ∅ ⊢ A)(v v' : BApp b σA M) → v ≡ v'
uniqueBApp .(builtin _ / refl) base base = refl
uniqueBApp (M · M') (step v x) (step v' x') with uniqueBApp M v v' | uniqueVal M' x x'
... | refl | refl  = refl
uniqueBApp (M ·⋆ A / refl) (step⋆ {σB = σA} v refl) (step⋆ {σB = σA'} v' refl) with uniqueSigTy σA σA' 
... | refl with uniqueBApp M v v'  
... | refl = refl

uniqueBApp' : ∀{A b b'}
  → (M : ∅ ⊢ A)
  → ∀{tn tm}{pt : tn ∔ tm ≣ fv (signature b)} 
  → ∀{an am}{pa : an ∔ am ≣ args♯ (signature b)}
  → {σA : SigTy pt pa A}
  → ∀{tn' tm'}{pt' : tn' ∔ tm' ≣ fv (signature b')} 
  → ∀{an' am'}{pa' : an' ∔ am' ≣ args♯ (signature b')}
  → {σA' : SigTy pt' pa' A}
  → (v : BApp b σA M)(v' : BApp b' σA' M)
  → ∃ λ (be : b ≡ b') → ∃ λ (tne : tn ≡ tn') → ∃ λ (tme : tm ≡ tm')  → ∃ λ (ane : an ≡ an') →  ∃ λ (ame : am ≡ am') 
  → (pt ≡ conv∔≣t be pt' tne tme) × (pa ≡ conv∔≣a be pa' ane ame)
uniqueBApp' (M · _) (step v _) (step v' _) with uniqueBApp' M v v'
... | refl ,, refl ,, refl ,, refl ,, refl ,, refl ,, refl  = refl ,, refl ,, refl ,, refl ,, refl ,, refl ,, refl
uniqueBApp' (M ·⋆ A / x) (step⋆ v .x) (step⋆ v' .x) with uniqueBApp' M v v' 
... | refl ,, refl ,, refl ,, refl ,, refl ,, refl ,, refl = refl ,, refl ,, refl ,, refl ,, refl ,, refl ,, refl
uniqueBApp' (builtin b / x) base base = refl ,, refl ,, refl ,, refl ,, refl ,, refl ,, refl

uniqueVal .(ƛ M) (V-ƛ M) (V-ƛ .M) = refl
uniqueVal .(Λ M) (V-Λ M) (V-Λ .M) = refl
uniqueVal .(wrap _ _ _) (V-wrap v) (V-wrap v') = cong V-wrap (uniqueVal _ v v')
uniqueVal .(con x refl) (V-con x) (V-con .x) = refl
uniqueVal M (V-I⇒ b {σB = s} x) (V-I⇒ b' {σB = s'} x') with uniqueBApp' M x x'
... | refl ,, refl ,, refl ,, refl ,, refl ,, refl ,, refl with uniqueSigTy s s'
... | refl = cong (V-I⇒ b) (uniqueBApp M x x')
uniqueVal M (V-IΠ b {σA = s} x) (V-IΠ b' {σA = s'} x') with uniqueBApp' M x x'
... | refl ,, refl ,, refl ,, refl ,, refl ,, refl ,, refl with uniqueSigTy s s'
... | refl = cong (V-IΠ b) (uniqueBApp M x x')
uniqueVal _ (V-constr e Tss refl refl {ts} vs refl) (V-constr .e .Tss .refl refl {ts'} vs₁ q) 
        with inj-IBwd2IList {ts = ts'}{ts} (lemma<>1 [] (lookup Tss e)) q 
uniqueVal _ (V-constr e Tss .refl refl {ts} vs refl) (V-constr _ _ .refl refl {.ts} vs₁ refl) | refl =
     cong (λ vs → V-constr e Tss refl refl vs refl) (uniqueVal-List vs vs₁)
```

```
lemV· : ∀{A B}{M : ∅ ⊢ A ⇒ B}{M'} → ¬ (Value M) → ¬ (Value (M · M'))
lemV· ¬VM (V-I⇒ b (step q VM')) = ⊥-elim (¬VM (V-I⇒ b q))

lemV'· : ∀{A B}{M : ∅ ⊢ A ⇒ B}{M'} → ¬ (Value M') → ¬ (Value (M · M'))
lemV'· ¬VM' (V-I⇒ b (step q VM')) = ⊥-elim (¬VM' VM')

lemVunwrap :  ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}{C}{q : C ≡ _}{M}
  → ¬ (Value (unwrap {A = A}{B} M q))
lemVunwrap (V-I⇒ b ())
lemVunwrap (V-IΠ b ())

lemV·⋆ : ∀{K}{A : ∅ ⊢Nf⋆ K}{B}{M : ∅ ⊢ Π B}{C}{p : C ≡ B [ A ]Nf}
  → ¬ (Value M) → ¬ (Value (M ·⋆ A / p))
lemV·⋆ ¬VM (V-I⇒ b (step⋆ q r)) = ¬VM (V-IΠ b q)
lemV·⋆ ¬VM (V-IΠ b (step⋆ q r)) = ¬VM (V-IΠ b q)


lemBAppβ : ∀{A B}{b}
  → ∀{tn tm}{pt : tn ∔ tm ≣ fv (signature b)}
  → ∀{an am}{pa : an ∔ am ≣ args♯ (signature b)}
  → {σB : SigTy pt pa B}
  → {M : ∅ , A ⊢ B} → ∀{M'}
  → ¬ (BApp b σB (ƛ M · M'))
lemBAppβ (step () x)


lemBAppβ⋆ : ∀{A : ∅ ⊢Nf⋆ K}{B}{b}
  → ∀{tn tm}{pt : tn ∔ tm ≣ fv (signature b)}
  → ∀{an am}{pa : an ∔ am ≣ args♯ (signature b)}
  → ∀{C}{σC : SigTy pt pa C}
  → ∀{M : ∅ ,⋆ K ⊢ B}{q : C ≡ B [ A ]Nf} → ¬ (BApp b σC (Λ M ·⋆ A / q))
lemBAppβ⋆ (step⋆ () refl)


lemVβ : ∀{A B}{M : ∅ , A ⊢ B}{M'} → ¬ (Value (ƛ M · M'))
lemVβ (V-I⇒ b q) = lemBAppβ q
lemVβ (V-IΠ b q) = lemBAppβ q

lemVβ⋆ : ∀{K}{A : ∅ ⊢Nf⋆ K}{B}{M : ∅ ,⋆ K ⊢ B}{C}{p : C ≡ B [ A ]Nf}
  → ¬ (Value (Λ M ·⋆ A / p))
lemVβ⋆ (V-I⇒ b q) = lemBAppβ⋆ q
lemVβ⋆ (V-IΠ b q) = lemBAppβ⋆ q

VE-constr-lemma : ∀ {Vs} {H} {Ts}
                    {tvs : IBwd (_⊢_ ∅) Vs}
                    {M : ∅ ⊢ H}
                    (ts : Algorithmic.ConstrArgs ∅ Ts)
                    {ZS}
                    (p : ZS ≡ (Vs <>< (H ∷ Ts)))
                    {zs : IBwd (∅ ⊢_) ZS} 
                    (q : substEq (IBwd (∅ ⊢_)) p zs ≡ (tvs <><I (M ∷ ts)))
                    (vs : VList zs)
                   → VList (tvs <><I (M ∷ ts))
VE-constr-lemma ts refl refl vs = vs

lemVE : ∀{A B} M (E : EC A B) → Value (E [ M ]ᴱ) → Value M
lemVE M [] V = V
lemVE M (EC₁ l· x) (V-I⇒ b (step x₁ x₂)) = lemVE M EC₁ (V-I⇒ b x₁)
lemVE M (x ·r EC₁) (V-I⇒ b (step x₁ v)) = lemVE M EC₁ v
lemVE M (EC₁ ·⋆ A / x) (V-I⇒ b (step⋆ x₁ .x)) = lemVE _ EC₁ (V-I b x₁)
lemVE M (EC₁ ·⋆ A / x) (V-IΠ b (step⋆ x₁ .x)) = lemVE _ EC₁ (V-I b x₁)
lemVE M (wrap EC₁) (V-wrap V) = lemVE _ EC₁ V
lemVE M (unwrap EC₁ / x) (V-I⇒ b ())
lemVE M (unwrap EC₁ / x) (V-IΠ b ())
lemVE M (constr {Vs = Vs}{H}{Ts} i A refl {tidx} {tvs} vs ts E) (V-constr _ _ _ refl {zs} vs' x) = 
       lemVE M E (proj-IIBwd (E [ M ]ᴱ) tvs ts
                             (VE-constr-lemma ts (lemma<>2 Vs (H ∷ Ts)) 
                                         (trans (cong (substEq (IBwd (_⊢_ ∅)) (lemma<>2 Vs (H ∷ Ts))) 
                                        (trans (IBwd<>IList (lemma<>1 [] (Vs <>> (H ∷ Ts))) x) 
                                          ((≡-subst-removable (IBwd (_⊢_ ∅)) _ refl  ([] <><I (tvs <>>I ((E [ M ]ᴱ) ∷ ts))))))) 
                                         (lemma<>I2 tvs ((E [ M ]ᴱ) ∷ ts))) vs'))
lemVE M (EC.case cs E) (V-I⇒ b ())
lemVE M (EC.case cs E) (V-IΠ b ())

lemBE : ∀{A B b} M (E : EC A B)
  → ∀{tn tm}{pt : tn ∔ tm ≣ fv (signature b)}
  → ∀{an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
  → {σ : SigTy pt pa A}
  → BApp b σ (E [ M ]ᴱ) → Value M
lemBE {b = b} M [] {σ = s} bt = V-I b bt
lemBE M (E l· x) (step bt y) = lemBE _ E bt
lemBE M (x ·r E) (step bt y) = lemVE _ E y
lemBE M (E ·⋆ A / refl) (step⋆ bt refl) = lemBE _ E bt

-- these adhoc lemmas about subst are needed as do the uniqueness bits of
-- lemma51! with pattern matching lambdas and can't use "with"

subst-l· : ∀{A B C C'}(E : EC (A ⇒ B) C)(M' : ∅ ⊢ A)(p : C ≡ C')
  → substEq (EC B) p (E l· M') ≡ substEq (EC (A ⇒ B)) p E l· M'
subst-l· E B refl = refl

subst-·r : ∀{A B C C'}(E : EC A C)(M : ∅ ⊢ A ⇒ B)(VM : Value M)(p : C ≡ C')
  → substEq (EC B) p (VM ·r E) ≡ VM ·r substEq (EC A) p E
subst-·r E M VM refl = refl

proj· : ∀{A A' B}{t : ∅ ⊢ A ⇒ B}{t' : ∅ ⊢ A' ⇒ B}{u : ∅ ⊢ A}{u' : ∅ ⊢ A'}
  → t _⊢_.· u ≡ t' · u'
  → ∃ λ (p : A ≡ A')
      → substEq (λ A → ∅ ⊢ A ⇒ B) p t ≡ t'
      × substEq (∅ ⊢_) p u ≡ u'
proj· refl = refl ,, refl ,, refl

subst-case : ∀ {B} {A} {B'} {n}
               {Tss = Tss : Vec.Vec (List (∅ ⊢Nf⋆ *)) n}
               (cs : Algorithmic.Cases ∅ A Tss) (E : EC (SOP Tss) B)
               (X : B ≡ B') →
             substEq (EC A) X (case cs E) ≡ case cs (substEq (EC (SOP Tss)) X E)
subst-case cs E refl = refl

valred : ∀{A}{L N : ∅ ⊢ A} → Value L → L —→⋆ N → ⊥
valred (V-I⇒ b (step () x₂)) (β-ƛ x)
valred (V-I⇒ b (step⋆ () .p)) (β-Λ p)
valred (V-IΠ b (step⋆ () .p)) (β-Λ p)
valred (V-I⇒ b ()) (β-wrap x p)
valred (V-IΠ b ()) (β-wrap x p)
valred (V-I⇒ b₁ (step bt₁ x₁)) (β-builtin b t bt u vu)  with uniqueBApp' t bt₁ bt
... | ()

valerr : ∀{A}{L : ∅ ⊢ A} → Error L → Value L → ⊥
valerr E-error (V-I⇒ b ())
valerr E-error (V-IΠ b ())

-- should replace this with something more general if something similar shows
-- up again
substƛVal : ∀{A A' B}{M : ∅ , A ⊢ B} (p : A ≡ A')
  → Value (substEq (λ A → ∅ ⊢ (A ⇒ B)) p (ƛ M))
substƛVal refl = V-ƛ _


BUILTIN-eq : ∀{A b b'}(M : ∅ ⊢ A)
  → ∀{tn}{pt : tn ∔ _ ≣ fv (signature b)} 
  → ∀{an}{pa : an ∔ _ ≣ args♯ (signature b)}
  → {σA : SigTy pt pa A}
  → ∀{tn'}{pt' : tn' ∔ _ ≣ fv (signature b')} 
  → ∀{an'}{pa' : an' ∔ _ ≣ args♯ (signature b')}
  → {σA' : SigTy pt' pa' A}
  → (bv : BApp b σA M)
  → (bv' : BApp b' σA' M)
  → BUILTIN' b bv ≡ BUILTIN' b' bv'
BUILTIN-eq M {σA = σA} {σA' = σA'} bv bv'
  with uniqueBApp' M bv bv'
... | refl ,, refl ,, refl ,, refl ,, refl ,, refl ,, refl
  with uniqueSigTy σA σA' 
... | refl  with uniqueBApp M bv bv' 
... | refl = refl 

determinism⋆ : ∀{A}{L N N' : ∅ ⊢ A} → L —→⋆ N → L —→⋆ N' → N ≡ N'
determinism⋆ (β-ƛ _) (β-ƛ _) = refl
determinism⋆ (β-Λ refl) (β-Λ refl) = refl
determinism⋆ (β-wrap _ refl) (β-wrap _ refl) = refl
determinism⋆ (β-builtin b t bt u vu) (β-builtin b' .t bt' .u vu') =
  BUILTIN-eq _  (step bt vu) (step bt' vu')
determinism⋆ (β-case e Tss refl {ts} vs refl cases) (β-case e' Tss' refl {ts'} vs' q cases') 
   with inj-IBwd2IList {ts = ts'}{ts} (lemma<>1 [] (lookup Tss e)) q 
... | refl = refl 

data Redex {A : ∅ ⊢Nf⋆ *} : ∅ ⊢ A → Set where
  β   : {L N : ∅ ⊢ A} → L —→⋆ N → Redex L
  err : Redex (error A)

valredex : ∀{A}{L : ∅ ⊢ A} → Value L → Redex L → ⊥
valredex V (β r) = valred V r
valredex V err   = valerr E-error V

data RProgress {A : ∅ ⊢Nf⋆ *} (M : ∅ ⊢ A) : Set where
  step :
      (Value M → ⊥)
    → ∀{B}(E : EC A B){L : ∅ ⊢ B}
    → Redex L
    → M ≡ E [ L ]ᴱ
    → (∀{B'}
      → (E' : EC A B')
      → {L' : ∅ ⊢ B'}
      → M ≡ E' [ L' ]ᴱ
      → Redex L'
      → ∃ λ (p : B ≡ B')
      → substEq (EC A) p E ≡ E' × substEq (∅ ⊢_) p L ≡ L')
      ----------------------------------------------------
    → RProgress M
  done :
      Value M
      -----------
    → RProgress M

data FocusedRProgress : ∀{tot}(itot : IList (∅ ⊢_) tot) → Set 
     where 
     done  : ∀{bs}{ibs : IBwd (∅ ⊢_) bs}{tot}{itot : IList (∅ ⊢_) tot}
              {idx : tot ≣ bs <>> []}
             (x : (itot ≣I ibs <>> []) idx)
             (vs : VList ibs)
        → FocusedRProgress itot
     step  :  ∀{tot}{itot : IList (∅ ⊢_) tot}
           → ∀{bs}{ibs : IBwd (∅ ⊢_) bs}(vs : VList ibs) --evaluated
           → ∀{A : ∅ ⊢Nf⋆ *} {M : ∅ ⊢ A}
           ----
          → (Value M → ⊥)
          → ∀{B}(E : EC A B){L : ∅ ⊢ B}
          → Redex L
          → M ≡ E [ L ]ᴱ
          → (∀{B'}
            → (E' : EC A B')
            → {L' : ∅ ⊢ B'}
            → M ≡ E' [ L' ]ᴱ
            → Redex L'
            → ∃ λ (p : B ≡ B')
            → substEq (EC A) p E ≡ E' × substEq (∅ ⊢_) p L ≡ L')
          ----
           → ∀ {ls : List (∅ ⊢Nf⋆ *)}(cs : ConstrArgs ∅ ls) 
           → {idx : tot ≣ bs <>> (A ∷ ls)}
           → (x : (itot ≣I ibs <>> (M ∷ cs)) idx)
           → FocusedRProgress itot


-- these lemmas are needed for the uniqueness cases of lemma51!
-- it might be cleaner to define every uniqueness case directly as a lemma

-- a beta⋆ reduction happened
U·⋆1 : ∀{A : ∅ ⊢Nf⋆ K}{B}{L : ∅ ,⋆ K ⊢ B}{X}
 {B' : ∅ ⊢Nf⋆ *}
 → (p : X ≡ B [ A ]Nf)
 → (E' : EC X  B'){L' : ∅ ⊢ B'}
 → Λ L _⊢_.·⋆ A / p ≡ (E' [ L' ]ᴱ)
 → Redex L' →
 ∃ (λ (q : X ≡ B') → substEq (EC _) q [] ≡ E' × substEq (∅ ⊢_) q (Λ L ·⋆ A / p) ≡ L')
U·⋆1 eq [] refl q = refl ,, refl ,, refl
U·⋆1 eq (E' ·⋆ A / r) p q with lem-·⋆ r eq p
U·⋆1 {L = L} eq (E' ·⋆ A / r) {L'} p q | refl ,, Y ,, refl ,, refl
  with lemΛE'' E' Y
U·⋆1 {_} {A} {L = L} eq (_·⋆_/_ {_} E' A r) {.(Λ L)} p (β ()) | refl ,, Y ,, refl ,, refl | refl ,, X ,, refl
U·⋆1 p (constr i _ refl vs ts E') () y


-- M is not a value, it has made a step
U·⋆2 : ∀{K}{C}{A : ∅ ⊢Nf⋆ K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{M : ∅ ⊢ Π B}{E : EC (Π B) C}{L : ∅ ⊢ C}{X}
 {B' : ∅ ⊢Nf⋆ *}
 → ¬ (Value M)
 → (p : X ≡ B [ A ]Nf) 
 → (E' : EC X B')
 → {L' : ∅ ⊢ B'} → M _⊢_.·⋆ A / p ≡ (E' [ L' ]ᴱ) 
 → Redex L' 
 → (U : {B' : ∅ ⊢Nf⋆ *} (E' : EC (Π B) B') {L' : ∅ ⊢ B'} 
      → M ≡ (E' [ L' ]ᴱ) 
      → Redex L' 
      → ∃ (λ (q : C ≡ B') → substEq (EC _) q E ≡ E' × substEq (_⊢_ ∅) q L ≡ L'))
 → ∃ (λ (p₁ : C ≡ B') →
     substEq (EC X) p₁ (E EC.·⋆ A / p) ≡ E'
   × substEq (_⊢_ ∅) p₁ L ≡ L')
U·⋆2 ¬VM eq [] refl (β (β-Λ .eq)) U = ⊥-elim (¬VM (V-Λ _))
U·⋆2 ¬VM eq (E ·⋆ A / .eq) refl q U with U E refl q
... | refl ,, refl ,, refl = refl ,, refl ,, refl

-- body of wrap made a step, it's not a value
Uwrap : ∀{A C}{B : ∅ ⊢Nf⋆ K}{M : ∅ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)}{L : ∅ ⊢ C}{E}{B' : ∅ ⊢Nf⋆ *}
 → (E' : EC (μ A B) B') {L' : ∅ ⊢ B'} →
 _⊢_.wrap A B M ≡ E' [ L' ]ᴱ →
 Redex L' →
 (U : {B' : ∅ ⊢Nf⋆ *}
      (E' : EC _ B')
      {L' : ∅ ⊢ B'} →
      M ≡ (E' [ L' ]ᴱ) →
      Redex L' →
      ∃ (λ p → substEq (EC _) p E ≡ E' × substEq (_⊢_ ∅) p L ≡ L'))
 →
 ∃
 (λ (p₁ : C ≡ B') →
    substEq (EC (μ A B)) p₁ (wrap E) ≡ E' × substEq (_⊢_ ∅) p₁ L ≡ L')
Uwrap (E l· x) () q U
Uwrap (x ·r E) () q U
Uwrap (E ·⋆ A / x) () q U
Uwrap (wrap E) refl q U with U E refl q
... | refl ,, refl ,, refl = refl ,, refl ,, refl
Uwrap (unwrap E / x) () q U
Uwrap [] refl (β ()) U


-- the body of the unwrap, M, is not a value and made a step
Uunwrap1 : ∀{A C}{B : ∅ ⊢Nf⋆ K}{M : ∅ ⊢ μ A B}{L : ∅ ⊢ C}{E}{B' : ∅ ⊢Nf⋆ *}{X}
  → ¬ (Value M)
  → (p : X ≡ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) →
  (E' : EC X B')
  {L' : ∅ ⊢ B'} →
  _⊢_.unwrap M p ≡ (E' [ L' ]ᴱ) →
  Redex L' →
  (U : {B' : ∅ ⊢Nf⋆ *} (E' : EC (μ A B) B') {L' : ∅ ⊢ B'} →
    M ≡ (E' [ L' ]ᴱ) →
    Redex L' →
    ∃ (λ q → substEq (EC (μ A B)) q E ≡ E' × substEq (_⊢_ ∅) q L ≡ L'))
  →
  ∃ (λ (q : C ≡ B') →
    substEq (EC X) q (EC.unwrap E / p) ≡ E' × substEq (_⊢_ ∅) q L ≡ L')
Uunwrap1 ¬VM eq [] refl (β (β-wrap x .eq)) U = ⊥-elim (¬VM (V-wrap x))
Uunwrap1 ¬VM refl (unwrap E / refl) refl q U with U E refl q
... | refl ,, refl ,, refl = refl ,, refl ,, refl

-- beta step
Uunwrap2 : ∀{A}{B : ∅ ⊢Nf⋆ K}{M : ∅ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)}{B' : ∅ ⊢Nf⋆ *}{X}
  → Value M
  → (p : X ≡ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) →
  (E' : EC X B')
  {L' : ∅ ⊢ B'} →
  _⊢_.unwrap (wrap A B M) p ≡ (E' [ L' ]ᴱ) →
  Redex L' →
  ∃ (λ (q : X ≡ B')
    → substEq (EC X) q [] ≡ E' × substEq (∅ ⊢_) q (unwrap (wrap A B M) p) ≡ L')
Uunwrap2 VM eq [] refl q = refl ,, refl ,, refl 
Uunwrap2 VM eq (unwrap E / x) p q with lem-unwrap p
... | refl ,, refl ,, refl ,, X4 = ⊥-elim (valredex (lemVE _ E (substEq Value (≅-to-≡ X4) (V-wrap VM))) q)

Ucase2 : ∀ {n} {Tss : Vec.Vec (List (∅ ⊢Nf⋆ *)) n}
           {M  : (∅ ⊢ SOP Tss)} {A}
           {cs : Algorithmic.Cases ∅ A Tss} 
           (VM : Value M)
           {B'} {n'}{Tss' : Vec.Vec (List (∅ ⊢Nf⋆ *)) n'} {L' : ∅ ⊢ B'}
       → (cs' : Algorithmic.Cases ∅ A Tss') 
       → (E' : EC (SOP Tss') B') 
       → _⊢_.case M cs ≡ _⊢_.case (E' [ L' ]ᴱ) cs' 
       → Redex L' 
       → Σ (A ≡ B') (λ p → Σ (substEq (EC A) p [] ≡ case cs' E') (λ x → substEq (_⊢_ ∅) p (case M cs) ≡ L'))
Ucase2 VM cs' E' refl r = ⊥-elim (valredex (lemVE _ E' VM) r)

constr-helper : ∀ {Bs : Bwd (∅ ⊢Nf⋆ *)}
                  {bs} (ibs : IBwd (_⊢_ ∅) bs)
                  {A} (w : ∅ ⊢ A) 
                  {ls} (ils : ConstrArgs ∅ ls)
                  {ts : IBwd (_⊢_ ∅) Bs} 
          → (vs : IIBwd Value ts)
          → (p : Bs ≡ bs <>< (A ∷ ls)) 
          → (q : substEq (IBwd (_⊢_ ∅)) p ts ≡ ibs <><I (w ∷ ils))
          → Value w
constr-helper ibs w ils vs refl refl = proj-IIBwd w ibs ils vs

subst-helper : ∀{a p} {A : Set a}(P : A → Set p) 
                  {a x y : A} (a≡x : a ≡ x) (a≡y : a ≡ y) {p : P x}{q : P y} 
                → substEq P (sym a≡x) p ≡ substEq P (sym a≡y) q 
                 → Σ (x ≡ y) λ eq → substEq P eq p ≡ q
subst-helper P refl refl refl = refl ,, refl 

Uconstr : ∀ {n} {Tss : Vec.Vec (List (∅ ⊢Nf⋆ *)) n} →
          -- First
          ∀ {i : Fin n} {tot : ConstrArgs ∅ (lookup Tss i)} 
            {B}  {bs} {H} {ls} 
            {ibs : IBwd (_⊢_ ∅) bs}
          → (vs : IIBwd Value ibs) 
          → (cs : IList (_⊢_ ∅) ls)
          → (idx : lookup Tss i ≣ bs <>> (H ∷ ls)) 
          → (E : EC H B) (L : ∅ ⊢ B) 
          → Redex L
          → tot ≡ substEq (IList (_⊢_ ∅)) (sym (lem-≣-<>> idx)) (ibs <>>I ((E [ L ]ᴱ) ∷ cs)) 
          -- Second
       → ∀  {i' : Fin n}
            {B'} {Vs} {H'} {Ts} 
            {tvs : IBwd (_⊢_ ∅) Vs}
          → (vs' : IIBwd Value tvs) 
          → (cs' : ConstrArgs ∅ Ts)
          → (idx' :  lookup Tss i' ≣ Vs <>> (H' ∷ Ts))    
          → (E' : EC H' B') (L' : ∅ ⊢ B')
        → _≡_ {_}{∅ ⊢ SOP Tss} (constr i Tss refl tot) (constr i' Tss refl (substEq (IList (_⊢_ ∅)) ((sym (lem-≣-<>> idx'))) (tvs <>>I ((E' [ L' ]ᴱ) ∷ cs'))))
        → Redex L'
        → (∀ {B''} (E'' : EC H B'') {L' = L'' : ∅ ⊢ B''} →
            (E [ L ]ᴱ) ≡ (E'' [ L'' ]ᴱ) 
             →   Redex L'' 
             →  Σ (B ≡ B'') (λ p → substEq (EC H) p E ≡ E'' × substEq (_⊢_ ∅) p L ≡ L''))
        → Σ (B ≡ B') (λ p → substEq (EC (SOP Tss)) p (constr i Tss refl {idx} {_} vs cs E) ≡  (constr i' Tss refl {idx'} vs' cs' E') × (substEq _ p L ≡ L'))
Uconstr {tot = tot} vs cs idx E L r p vs' cs' idx' E' L' refl r' U with subst-helper (IList (∅ ⊢_)) (lem-≣-<>> idx') (lem-≣-<>> idx) p
... | x ,, y with equalbyPredicateI tot Value (lem-≣-<>> idx) (lem-≣-<>> idx') p refl vs vs' (λ V → valredex (lemVE _ E V) r) (λ V' → valredex (lemVE _ E' V') r') 
... | refl ,, refl ,, refl ,, refl with uniqueVal-List vs vs' | unique-≣-<>> idx idx'
Uconstr {ibs = ibs} vs cs idx E L r p .vs cs' idx' E' L' refl r' U 
  | refl ,, y | refl ,, refl ,, refl ,, refl | refl | refl with ∷-injectiveI refl (<>>I-cancelˡ ibs ((E' [ L' ]ᴱ) ∷ cs') ((E [ L ]ᴱ) ∷ cs) y)
... | pel ,, refl with U E' (sym pel) r' 
... | refl ,, refl ,, refl = refl ,, refl ,, refl

----------
-- Lemma inspired by Lemma 5.1 (Chapter 5) of Semantics Engineering with PLT Redex
-- by M. Felleisen, R.B. Findler, and M. Flatt
rlemma51! : {A : ∅ ⊢Nf⋆ *} → (M : ∅ ⊢ A) → RProgress M

rlemma51-List :  ∀{tot}{itot : IList (∅ ⊢_) tot}{bs}{ibs : IBwd (∅ ⊢_) bs}
                  {ls}{idx : tot ≣ bs <>> ls} 
               → (cs : IList (∅ ⊢_) ls)
               → (iidx : (itot ≣I ibs <>> cs) idx)
               → VList ibs
               → FocusedRProgress itot
rlemma51-List [] x Vs = done x Vs
rlemma51-List (c ∷ cs) x Vs with rlemma51! c 
... | step  ¬VM E p q U = step Vs ¬VM E p q U cs x
... | done V = rlemma51-List cs (bubble x) (Vs :< V)

rlemma51! (ƛ M) = done (V-ƛ M)
rlemma51! (M · N) with rlemma51! M
... | step ¬VM E p q U = step
  (lemV· ¬VM)
  (E l· N)
  p
  (cong (_· N) q) 
        λ { [] refl (β (β-ƛ VN)) → ⊥-elim (¬VM (V-ƛ _))
          ; [] refl (β (β-builtin b .M bt .N vu)) → ⊥-elim (¬VM (V-I⇒ b bt))
          ; (E' l· N') refl r → let X ,, Y ,, Y' = U E' refl r in X ,,  trans ( subst-l· E N X)  (cong (_l· N) Y)  ,, Y'
          ; (VM ·r E') refl rx → ⊥-elim (¬VM VM)}
... | done VM with rlemma51! N
... | step ¬VN E p q U = step
  (lemV'· ¬VN)
  (VM ·r E)
  p
  (cong (M ·_) q) 
        λ { [] refl (β (β-ƛ VN)) → ⊥-elim (¬VN VN)
          ; [] refl (β (β-builtin b .M bt .N VN)) → ⊥-elim (¬VN VN)
          ; (E' l· N') refl q → ⊥-elim (valredex (lemVE _ _ VM) q)
          ; (VM' ·r E') refl q → let X ,, X'' ,, X''' = U E' refl q in
                X
                ,,
                trans (subst-·r E M VM X)
                      (trans (cong (VM ·r_) X'') (cong (_·r E') (uniqueVal M VM VM')))
                ,,
                X'''}
rlemma51! (.(ƛ M) · N) | done (V-ƛ M) | done VN = step
  lemVβ
  []
  (β (β-ƛ VN))
  refl
  λ { [] refl (β (β-ƛ x)) → refl ,, refl ,, refl
    ; (E' l· N') p q → let X ,, Y ,, Y' = proj· p in
      ⊥-elim (valredex (lemVE _ E' (substEq Value Y (substƛVal X))) q)
    ; (VM' ·r E') refl q → ⊥-elim (valredex (lemVE _ E' VN) q)}
rlemma51! (M · N) | done (V-I⇒ b {am = 0} x) | done VN = step
  (λ V → valred V (β-builtin b M x N VN))
  []
  (β (β-builtin b M x N VN))
  refl
  λ { [] refl (β (β-builtin b .M bt .N vu)) → refl ,, refl ,, refl
    ; (E' l· N') refl q → ⊥-elim (valredex (lemBE _ E' x) q)
--    ; (E' l·v VN') refl q → ⊥-elim (valredex (lemBE _ E' x) q)
    ; (VM' ·r E') refl q → ⊥-elim (valredex (lemVE _ E' VN) q)}
rlemma51! (M · N) | done (V-I⇒ b {am = suc _} x) | done VN =
  done (V-I b (step x VN))
rlemma51! (Λ M) = done (V-Λ M)
rlemma51! (M ·⋆ A / refl) with rlemma51! M
... | step ¬VM E p q U = step (λ V → lemV·⋆ (λ V → ¬VM V) V) (E ·⋆ A / refl) p (cong (_·⋆ A / refl) q) (λ E p q → U·⋆2 ¬VM refl E p q U)
... | done (V-Λ M) = step lemVβ⋆ [] (β (β-Λ refl)) refl (U·⋆1 refl)
... | done (V-IΠ b {σA = σ} bt) = done (V-I b (step⋆ bt refl {σ [ A ]SigTy}))
rlemma51! (wrap A B M) with rlemma51! M
... | step ¬VM E p q U = step
  (λ {(V-wrap VM) → ¬VM VM})
  (wrap E)
  p
  (cong (wrap A B) q)
  λ E p' q' → Uwrap E p' q' U
... | done VM = done (V-wrap VM)
rlemma51! (unwrap M x) with rlemma51! M
... | step ¬VM E p q U = step
  (λ V → lemVunwrap V)
  (unwrap E / x)
  p
  (cong (λ M → unwrap M x) q)
  λ E p' q' → Uunwrap1 ¬VM x E p' q' U
... | done (V-wrap VM) = step
  (λ V → valred V (β-wrap VM x))
  []
  (β (β-wrap VM x))
  refl
  λ E p' q' → Uunwrap2 VM x E p' q'
rlemma51! (con c refl) = done (V-con c)
rlemma51! (constr i Tss refl tot) with rlemma51-List tot start [] 
... | done {bs}{ibs}{idx = idx} x vs = done 
          (V-constr i 
                    Tss 
                    refl 
                    (sym (lemma<>2' _ _ (sym (lem-≣-<>> idx))))
                    vs 
                    (trans (≡-subst-removable (IList (_⊢_ ∅)) _ _ (ibs <>>I [])) 
                           (sym (lem-≣I-<>>1' x))))
... | step {bs = bs}{ibs} vs ¬VM E {L} r refl U {ls} cs {idx} x = step 
          (λ {(V-constr .i .Tss .refl refl {ts} vs' x') → 
                ¬VM (constr-helper ibs 
                                   (E [ L ]ᴱ) 
                                   cs 
                                   (substEq VList (IBwd<>IList (lemma<>1 [] (lookup Tss i)) {ts} x') vs')
                                  (trans (cong ([] <><_) (lem-≣-<>> idx)) (lemma<>2 bs (_ ∷ ls))) 
                                  (trans (trans (trans
                                     (trans (trans 
                                         (subst-subst (lemma<>2' ([] <>< lookup Tss i) (lookup Tss i) (lemma<>1 [] (lookup Tss i))) 
                                              {(trans (cong ([] <><_) (lem-≣-<>> idx)) (lemma<>2 bs (_ ∷ ls)))}) 
                                         (≡-subst-removable (IBwd (∅ ⊢_)) _ _ ([] <><I tot))) 
                                         (sym (subst-subst (cong (_<><_ []) (lem-≣-<>> idx)) {lemma<>2 bs (_ ∷ ls) }  ))) 
                                         (cong (substEq (IBwd (_⊢_ ∅)) (lemma<>2 bs (_ ∷ ls))) (sym (lem-<><I-subst(lem-≣-<>> idx))))) 
                                         (cong (substEq (IBwd (_⊢_ ∅)) (lemma<>2 bs (_ ∷ ls))) (cong ([] <><I_) (lem-≣I-<>>1 x)))) 
                                         (lemma<>I2 ibs ((E [ L ]ᴱ) ∷ cs))))  }) 
          (constr i Tss refl { idx } vs cs E) 
          r 
          (constr-cong (trans (sym (lem-≣-<>> idx)) refl) (trans (lem-≣I-<>>1' x) (≡-subst-removable (IList (_⊢_ ∅)) _ _ (ibs <>>I ((E [ _ ]ᴱ) ∷ cs)))))
          λ { [] refl (β ())
            ; (constr i' .Tss refl {idx'} {tvs} vs' cs' E') {L'} p' r' →
                  Uconstr vs cs idx E L r (lem-≣I-<>>1' x) 
                                  vs' cs' idx' E' L' (trans p' 
                                                            (sym (constr-cong (trans (sym (lem-≣-<>> idx')) refl) 
                                                            (≡-subst-removable (IList (_⊢_ ∅)) (sym (lem-≣-<>> idx')) (trans (sym (lem-≣-<>> idx')) refl) _)))) 
                                  r' U 
            }
rlemma51! (case M cs) with rlemma51! M  
... | step ¬VM E p q U = step (λ V → ¬VM (lemVE _ (EC.case cs []) V)) 
                              (EC.case cs E) 
                              p 
                              (cong₂ case q refl) 
                              λ { [] refl (β (β-case e _ q vs x .cs)) → ⊥-elim (¬VM (V-constr e _ refl q vs x))
                                ; (case x E') refl q' → let X ,, Y ,, Y' = U E' refl q' 
                                                        in X ,, (trans (subst-case cs E X) (cong (case cs) Y)) ,, Y'}
... | done VM@(V-constr e Tss refl refl vs x) = 
      step (λ V → valred V (β-case e Tss refl vs x cs)) 
          [] 
          (β (β-case e Tss refl vs x cs)) 
          refl 
          λ { [] refl r → refl ,, refl ,, refl
            ; (EC.case cs' E') p r → Ucase2 VM cs' E' p r} 
rlemma51! (builtin b / refl) = done (ival b)
rlemma51! (error _) = step
  (valerr E-error)
  []
  err
  refl
  λ { [] p q → refl ,, refl ,, p}


unique-EC : ∀{A B}(E E' : EC A B)(L : ∅ ⊢ B) → Redex L
  → E [ L ]ᴱ ≡ E' [ L ]ᴱ → E ≡ E'
unique-EC  E E' L p q with rlemma51! (E [ L ]ᴱ)
... | done VEL = ⊥-elim (valredex (lemVE L E VEL) p)
... | step ¬VEL E'' r r' U with U E' q p
... | refl ,, refl ,, refl with U E refl p
... | refl ,, refl ,, refl = refl

unique-EC' : ∀{A B}(E : EC A B)(L : ∅ ⊢ B) → Redex L
  → E [ L ]ᴱ ≡ error _ → ∃ λ (p : B ≡ A) → E ≡ substEq (λ A → EC A B) p [] × L ≡ error _
unique-EC' E L p q with rlemma51! (E [ L ]ᴱ)
... | done VEL = ⊥-elim (valredex (lemVE L E VEL) p)
... | step ¬VEL E'' r r' U with U [] q err
... | refl ,, refl ,, refl with U E refl p
... | refl ,, refl ,, refl = refl ,, refl ,, refl

notVAL : ∀{A}{L N : ∅ ⊢ A} → Value L → L —→ N → ⊥
notVAL V (ruleEC E p refl r) = valred (lemVE _ E V) p
notVAL V (ruleErr E refl)    =
  valerr E-error (lemVE _ E V)

determinism : ∀{A}{L N N' : ∅ ⊢ A} → L —→ N → L —→ N' → N ≡ N'
determinism {L = L} p q with rlemma51! L
determinism {L = .(E [ _ ]ᴱ)} (ruleEC E p refl p') q | done VL =
  ⊥-elim (valred (lemVE _ E VL) p)
determinism {L = L} (ruleErr E refl)      q | done VL =
  ⊥-elim (valerr E-error (lemVE _ E VL))
determinism {L = L} (ruleEC E' p p' p'') q | step ¬VL E r r' U
  with U E' p' (β p)
determinism {L = L} (ruleEC E p p' p'') (ruleEC E' q q' q'') | step ¬VL E (β r) r' U | refl ,, refl ,, refl with U E' q' (β q)
... | refl ,, refl ,, refl =
  trans p'' (trans (cong (E [_]ᴱ) (determinism⋆ p q)) (sym q''))
determinism {L = L} (ruleEC E p p' p'') (ruleErr E' q) | step ¬VL E (β r) r' U | refl ,, refl ,, refl with U E' q err
determinism {L = L} (ruleEC .(substEq (EC _) refl E) p p' p'') (ruleErr .E q) | step ¬VL E (β ()) r' U | refl ,, refl ,, refl | refl ,, refl ,, refl
determinism {L = L} (ruleErr E' p) q | step ¬VL E (β x) r' U
  with U E' p err
determinism {L = L} (ruleErr .E p) q | step ¬VL E (β ()) r' U | refl ,, refl ,, refl
determinism {L = L} (ruleErr E' p) (ruleEC E'' q q' q'') | step ¬VL E err r' U with U E'' q' (β q)
determinism {L = L} (ruleErr E' p) (ruleEC .E () q' q'') | step ¬VL E err r' U | refl ,, refl ,, refl
determinism {L = L} (ruleErr E' p) (ruleErr E'' q) | step ¬VL E err r' U with U E' p err | U E'' q err
... | refl ,, refl ,, refl | refl ,, refl ,, refl = refl
-- -}
```  
    
