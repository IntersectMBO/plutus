```
module Algorithmic.ReductionEC.Determinism where
```
## Imports

```
open import Data.Nat using (suc)
open import Data.Empty using (⊥;⊥-elim)
open import Data.List as List using (List; _∷_; [])
open import Data.Product using (_×_;∃) renaming (_,_ to _,,_)
open import Relation.Nullary using (¬_;yes;no)
open import Relation.Binary.PropositionalEquality 
                    using (_≡_;refl;sym;trans;cong)  
                    renaming (subst to substEq)
open import Relation.Binary.HeterogeneousEquality 
        using (_≅_;refl;≅-to-≡) 

open import Utils hiding (TermCon)
open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;_∋⋆_;Z)
open _⊢⋆_
import Type.RenamingSubstitution as T
open import Algorithmic using (Ctx;_⊢_;conv⊢)
open Ctx
open _⊢_
open import Algorithmic.RenamingSubstitution using (_[_];_[_]⋆)
open import Algorithmic.Properties using (lem-·⋆;lem-unwrap)
open import Algorithmic.Signature using (SigTy;convSigTy;uniqueSigTy)
open import Type.BetaNBE using (nf)
open import Type.BetaNBE.RenamingSubstitution using (_[_]Nf)
open import Type.BetaNormal using (_⊢Nf⋆_;embNf;weakenNf)
open _⊢Nf⋆_
open import Algorithmic.ReductionEC
open import Builtin using (Builtin;signature)
open import Builtin.Signature using (Sig;args♯)
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
  → (tn'  ∔ tm'  ≣ fv♯ (signature b')) 
  → tn ≡ tn' → tm ≡ tm'
  → tn ∔ tm ≣ fv♯ (signature b)
conv∔≣t refl pt = conv∔≣ pt refl  

conv∔≣a : ∀{b b' an am an' am'}
  → b ≡ b'
  → (an'  ∔ am'  ≣ args♯ (signature b')) 
  → an ≡ an' → am ≡ am'
  → an ∔ am ≣ args♯ (signature b)
conv∔≣a refl pa = conv∔≣ pa refl  


uniqueVal : ∀{A}(M : ∅ ⊢ A)(v v' : Value M) → v ≡ v'

uniqueBApp : ∀{A b}
  → ∀{tn tm}{pt : tn ∔ tm ≣ fv♯ (signature b)}
  → ∀{an am}{pa : an ∔ am ≣ args♯ (signature b)}
  → {σA : SigTy pt pa A}
  → (M : ∅ ⊢ A)(v v' : BApp b σA M) → v ≡ v'
uniqueBApp .(builtin _ / refl) base base = refl
uniqueBApp (M · M') (step v x) (step v' x') with uniqueBApp M v v' | uniqueVal M' x x'
... | refl | refl  = refl
uniqueBApp (M ·⋆ A / refl) (step⋆ {σB = σA} v refl refl) (step⋆ {σB = σA'} v' refl σq') with uniqueSigTy σA σA' 
... | refl with uniqueBApp M v v' | σq' 
... | refl | refl = refl

uniqueBApp' : ∀{A b b'}
  → (M : ∅ ⊢ A)
  → ∀{tn tm}{pt : tn ∔ tm ≣ fv♯ (signature b)} 
  → ∀{an am}{pa : an ∔ am ≣ args♯ (signature b)}
  → {σA : SigTy pt pa A}
  → ∀{tn' tm'}{pt' : tn' ∔ tm' ≣ fv♯ (signature b')} 
  → ∀{an' am'}{pa' : an' ∔ am' ≣ args♯ (signature b')}
  → {σA' : SigTy pt' pa' A}
  → (v : BApp b σA M)(v' : BApp b' σA' M)
  → ∃ λ (be : b ≡ b') → ∃ λ (tne : tn ≡ tn') → ∃ λ (tme : tm ≡ tm')  → ∃ λ (ane : an ≡ an') →  ∃ λ (ame : am ≡ am') 
  → (pt ≡ conv∔≣t be pt' tne tme) × (pa ≡ conv∔≣a be pa' ane ame)
uniqueBApp' (M · _) (step v _) (step v' _) with uniqueBApp' M v v'
... | refl ,, refl ,, refl ,, refl ,, refl ,, refl ,, refl  = refl ,, refl ,, refl ,, refl ,, refl ,, refl ,, refl
uniqueBApp' (M ·⋆ A / x) (step⋆ v .x _) (step⋆ v' .x _) with uniqueBApp' M v v' 
... | refl ,, refl ,, refl ,, refl ,, refl ,, refl ,, refl = refl ,, refl ,, refl ,, refl ,, refl ,, refl ,, refl
uniqueBApp' (builtin b / x) base base = refl ,, refl ,, refl ,, refl ,, refl ,, refl ,, refl

uniqueVal .(ƛ M) (V-ƛ M) (V-ƛ .M) = refl
uniqueVal .(Λ M) (V-Λ M) (V-Λ .M) = refl
uniqueVal .(wrap _ _ _) (V-wrap v) (V-wrap v') = cong V-wrap (uniqueVal _ v v')
uniqueVal .(con cn) (V-con cn) (V-con .cn) = refl
uniqueVal M (V-I⇒ b {σB = s} x) (V-I⇒ b' {σB = s'} x') with uniqueBApp' M x x'
... | refl ,, refl ,, refl ,, refl ,, refl ,, refl ,, refl with uniqueSigTy s s'
... | refl = cong (V-I⇒ b) (uniqueBApp M x x')
uniqueVal M (V-IΠ b {σA = s} x) (V-IΠ b' {σA = s'} x') with uniqueBApp' M x x'
... | refl ,, refl ,, refl ,, refl ,, refl ,, refl ,, refl with uniqueSigTy s s'
... | refl = cong (V-IΠ b) (uniqueBApp M x x')
```

```
lemV· : ∀{A B}{M : ∅ ⊢ A ⇒ B}{M'} → ¬ (Value M) → ¬ (Value (M · M'))
lemV· ¬VM (V-I⇒ b (step q VM')) = ⊥-elim (¬VM (V-I⇒ b q))
--lemV· ¬VM (V-IΠ b (step q VM')) = ⊥-elim (¬VM (V-I⇒ b q))

lemV'· : ∀{A B}{M : ∅ ⊢ A ⇒ B}{M'} → ¬ (Value M') → ¬ (Value (M · M'))
lemV'· ¬VM' (V-I⇒ b (step q VM')) = ⊥-elim (¬VM' VM')
--lemV'· ¬VM' (V-IΠ b (step q VM')) = ⊥-elim (¬VM' VM')

lemVunwrap :  ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}{C}{q : C ≡ _}{M}
  → ¬ (Value (unwrap {A = A}{B} M q))
lemVunwrap (V-I⇒ b ())
lemVunwrap (V-IΠ b ())

lemV·⋆ : ∀{K}{A : ∅ ⊢Nf⋆ K}{B}{M : ∅ ⊢ Π B}{C}{p : C ≡ B [ A ]Nf}
  → ¬ (Value M) → ¬ (Value (M ·⋆ A / p))
lemV·⋆ ¬VM (V-I⇒ b (step⋆ q r _)) = ¬VM (V-IΠ b q)
lemV·⋆ ¬VM (V-IΠ b (step⋆ q r _)) = ¬VM (V-IΠ b q)


lemBAppβ : ∀{A B}{b}
  → ∀{tn tm}{pt : tn ∔ tm ≣ fv♯ (signature b)}
  → ∀{an am}{pa : an ∔ am ≣ args♯ (signature b)}
  → {σB : SigTy pt pa B}
  → {M : ∅ , A ⊢ B} → ∀{M'}
  → ¬ (BApp b σB (ƛ M · M'))
lemBAppβ (step () x)


lemBAppβ⋆ : ∀{A : ∅ ⊢Nf⋆ K}{B}{b}
  → ∀{tn tm}{pt : tn ∔ tm ≣ fv♯ (signature b)}
  → ∀{an am}{pa : an ∔ am ≣ args♯ (signature b)}
  → ∀{C}{σC : SigTy pt pa C}
  → ∀{M : ∅ ,⋆ K ⊢ B}{q : C ≡ B [ A ]Nf} → ¬ (BApp b σC (Λ M ·⋆ A / q))
lemBAppβ⋆ (step⋆ () refl refl)


lemVβ : ∀{A B}{M : ∅ , A ⊢ B}{M'} → ¬ (Value (ƛ M · M'))
lemVβ (V-I⇒ b q) = lemBAppβ q
lemVβ (V-IΠ b q) = lemBAppβ q

lemVβ⋆ : ∀{K}{A : ∅ ⊢Nf⋆ K}{B}{M : ∅ ,⋆ K ⊢ B}{C}{p : C ≡ B [ A ]Nf}
  → ¬ (Value (Λ M ·⋆ A / p))
lemVβ⋆ (V-I⇒ b q) = lemBAppβ⋆ q
lemVβ⋆ (V-IΠ b q) = lemBAppβ⋆ q

lemVE : ∀{A B} M (E : EC A B) → Value (E [ M ]ᴱ) → Value M
lemVE M [] V = V
lemVE M (EC₁ l· x) (V-I⇒ b (step x₁ x₂)) = lemVE M EC₁ ((V-I⇒ b x₁))
lemVE M (x ·r EC₁) (V-I⇒ b (step x₁ v)) = lemVE M EC₁ v
lemVE M (EC₁ ·⋆ A / x) (V-I⇒ b (step⋆ x₁ .x σq)) = lemVE _ EC₁ (V-I b x₁)
lemVE M (EC₁ ·⋆ A / x) (V-IΠ b (step⋆ x₁ .x σq)) = lemVE _ EC₁ (V-I b x₁)
lemVE M (wrap EC₁) (V-wrap V) = lemVE _ EC₁ V
lemVE M (unwrap EC₁ / x) (V-I⇒ b ())
lemVE M (unwrap EC₁ / x) (V-IΠ b ())

lemBE : ∀{A B b} M (E : EC A B)
  → ∀{tn tm}{pt : tn ∔ tm ≣ fv♯ (signature b)}
  → ∀{an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
  → {σ : SigTy pt pa A}
  → BApp b σ (E [ M ]ᴱ) → Value M
lemBE {b = b} M [] {σ = s} bt = V-I b bt
lemBE M (E l· x) (step bt y) = lemBE _ E bt
lemBE M (x ·r E) (step bt y) = lemVE _ E y
lemBE M (E ·⋆ A / refl) (step⋆ bt refl refl) = lemBE _ E bt


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

valred : ∀{A}{L N : ∅ ⊢ A} → Value L → L —→⋆ N → ⊥
valred (V-I⇒ b (step () x₂)) (β-ƛ x)
valred (V-I⇒ b (step⋆ () .p σq)) (β-Λ p)
valred (V-IΠ b (step⋆ () .p σq)) (β-Λ p)
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
  → ∀{tn}{pt : tn ∔ _ ≣ fv♯ (signature b)} 
  → ∀{an}{pa : an ∔ _ ≣ args♯ (signature b)}
  → {σA : SigTy pt pa A}
  → ∀{tn'}{pt' : tn' ∔ _ ≣ fv♯ (signature b')} 
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

-- M is not a value, it has made a step
U·⋆2 : ∀{K}{C}{A : ∅ ⊢Nf⋆ K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{M : ∅ ⊢ Π B}{E : EC (Π B) C}{L : ∅ ⊢ C}{X}
 {B' : ∅ ⊢Nf⋆ *}
 → ¬ (Value M)
 → (p : X ≡ B [ A ]Nf) →
 (E' : EC X B')
 {L' : ∅ ⊢ B'} →
 M _⊢_.·⋆ A / p ≡ (E' [ L' ]ᴱ) →
 Redex L' →
 (U : {B' : ∅ ⊢Nf⋆ *} (E' : EC (Π B) B') {L' : ∅ ⊢ B'} →
      M ≡ (E' [ L' ]ᴱ) →
      Redex L' →
      ∃ (λ (q : C ≡ B') → substEq (EC _) q E ≡ E' × substEq (_⊢_ ∅) q L ≡ L'))
 →
 ∃
 (λ (p₁ : C ≡ B') →
   substEq
   (EC X)
   p₁ (E EC.·⋆ A / p)
   ≡ E'
   × substEq (_⊢_ ∅) p₁ L ≡ L')
U·⋆2 ¬VM eq [] refl (β (β-Λ .eq)) U = ⊥-elim (¬VM (V-Λ _))
U·⋆2 ¬VM eq (E ·⋆ A / .eq) refl q U with U E refl q
... | refl ,, refl ,, refl = refl ,, refl ,, refl

U·⋆3 : ∀{K}{A : ∅ ⊢Nf⋆ K}{B}{M : ∅ ⊢ Π B}{B' : ∅ ⊢Nf⋆ *}{X}
      → (p : X ≡ B [ A ]Nf) →
      (E' : EC X B')
      {L' : ∅ ⊢ B'} →
      Value M →
      M _⊢_.·⋆ A / p ≡ (E' [ L' ]ᴱ) →
      Redex L' →
      ∃ λ (q : X ≡ B') → substEq (EC X) q [] ≡ E'
         × substEq (∅ ⊢_) q (M _⊢_.·⋆ A / p) ≡ L'
U·⋆3 eq (E ·⋆ A / .eq) V refl q = ⊥-elim (valredex (lemVE _ E V) q)
U·⋆3 refl [] V refl q = refl ,, refl ,, refl


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
Uunwrap2 VM eq (unwrap E / x) p q with lem-unwrap p
... | refl ,, refl ,, refl ,, X4 =
  ⊥-elim (valredex (lemVE
                     _
                     E
                     (substEq Value (≅-to-≡ X4)
                     (V-wrap VM))) q)
Uunwrap2 VM refl [] refl q = refl ,, refl ,, refl


rlemma51! : {A : ∅ ⊢Nf⋆ *} → (M : ∅ ⊢ A) → RProgress M
rlemma51! (ƛ M) = done (V-ƛ M)
rlemma51! (M · N) with rlemma51! M
... | step ¬VM E p q U = step
  (lemV· ¬VM)
  (E l· N)
  p
  (cong (_· N) q)
  λ { [] refl (β (β-ƛ VN)) → ⊥-elim (¬VM (V-ƛ _))
    ; [] refl (β (β-builtin b .M bt .N vu)) → ⊥-elim (¬VM (V-I⇒ b bt))
    ; (E' l· N') refl r → let X ,, Y ,, Y' = U E' refl r in
      X ,,  trans ( subst-l· E N X)  (cong (_l· N) Y)  ,, Y'
    ; (VM ·r E') refl r → ⊥-elim (¬VM VM)
    }
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
    ; (VM' ·r E') refl q → ⊥-elim (valredex (lemVE _ E' VN) q)}
rlemma51! (M · N) | done (V-I⇒ b {am = suc _} x) | done VN =
  done (V-I b (step x VN))
rlemma51! (Λ M) = done (V-Λ M)
rlemma51! (M ·⋆ A / x) with rlemma51! M
... | step ¬VM E p q U = step (λ V → lemV·⋆ (λ V → ¬VM V) V) (E ·⋆ A / x) p (cong (_·⋆ A / x) q) (λ E p q → U·⋆2 ¬VM x E p q U)
... | done (V-Λ M) = step lemVβ⋆ [] (β (β-Λ x)) refl (U·⋆1 x)
... | done (V-IΠ b bt) = done (V-I b (step⋆ bt x refl))
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
rlemma51! (con c) = done (V-con c)
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