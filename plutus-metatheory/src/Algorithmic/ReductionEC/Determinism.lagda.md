```
module Algorithmic.ReductionEC.Determinism where
```
## Imports

```
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
open import Algorithmic using (Ctx;_⊢_;Arity;Term;Type;conv⊢) renaming (arity to sigarity)
open Ctx
open _⊢_
open import Algorithmic.RenamingSubstitution using (_[_];_[_]⋆)
open import Algorithmic.Properties using (lem-·⋆;lem-unwrap)
open import Type.BetaNBE using (nf)
open import Type.BetaNBE.RenamingSubstitution using (_[_]Nf)
open import Type.BetaNormal using (_⊢Nf⋆_;embNf;weakenNf)
open _⊢Nf⋆_
open import Algorithmic.ReductionEC
open import Builtin using (Builtin;signature)

arity : (b : Builtin) -> Arity
arity b = sigarity (signature b)
```

```
lemΛE'' : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}
  → ∀{L : ∅ ,⋆ K ⊢ B}{X}{L' : ∅ ⊢ X}
  → (E : EC (Π B) X)
  → Λ L ≅ E [ L' ]ᴱ
  → ∃ λ (p : X ≡ Π B)
  → substEq (EC (Π B)) p E ≡ EC.[] × Λ L ≡ substEq (∅ ⊢_) p L'
lemΛE'' [] refl = refl ,, refl ,, refl

subst<>>∈ : ∀{b b' as as' az az'}
  → az' <>> as' ∈ arity b'
  → b ≡ b' → az ≡ az' → as ≡ as'
  → az <>> as ∈ arity b
subst<>>∈ p refl refl refl = p

uniqueVal : ∀{A}(M : ∅ ⊢ A)(v v' : Value M) → v ≡ v'

uniqueBApp : ∀{A b as az}
  → (p : az <>> as ∈ arity b)(M : ∅ ⊢ A)(v v' : BApp b p M) → v ≡ v'
uniqueBApp .(start (arity b)) (builtin b / refl) (base refl) (base refl) = refl
uniqueBApp .(bubble p) (M ·⋆ A / refl) (step⋆ p v refl) (step⋆ .p v' refl)
  with uniqueBApp p M v v'
... | refl = refl
uniqueBApp .(bubble p) (M · M') (step p v w) (step .p v' w')
  with uniqueBApp p M v v' | uniqueVal M' w w'
... | refl | refl = refl

uniqueBApp' : ∀{A b b' as as' az az'}(M : ∅ ⊢ A)(p : az <>> as ∈ arity b)(p' : az' <>> as' ∈ arity b')(v : BApp b p M)(v' : BApp b' p' M)
  → ∃ λ (r : b ≡ b') → ∃ λ (r' : az ≡ az') → ∃ λ (r'' : as ≡ as')
  → p ≡ subst<>>∈ p' r r' r''
uniqueBApp' (builtin b / refl) .(start (arity b)) .(start (arity b)) (base refl) (base  refl) =
  refl ,, refl ,, refl ,, refl
uniqueBApp' (M · M') .(bubble p) .(bubble p₁) (step p q x) (step p₁ q' x₁)
  with uniqueBApp' M p p₁ q q'
... | refl ,, refl ,, refl ,, refl = refl ,, refl ,, refl ,, refl
uniqueBApp' (M ·⋆ A / refl) .(bubble p) .(bubble p₁) (step⋆ p q refl) (step⋆ p₁ q' refl)
  with uniqueBApp' M p p₁ q q'
... | refl ,, refl ,, refl ,, refl = refl ,, refl ,, refl ,, refl

uniqueVal .(ƛ M) (V-ƛ M) (V-ƛ .M) = refl
uniqueVal .(Λ M) (V-Λ M) (V-Λ .M) = refl
uniqueVal .(wrap _ _ _) (V-wrap v) (V-wrap v') with uniqueVal _ v v'
... | refl = refl
uniqueVal .(con cn) (V-con cn) (V-con .cn) = refl
uniqueVal M (V-I⇒ b x y) (V-I⇒ b' x' y') with uniqueBApp' M x x' y y'
... | refl ,, refl ,, refl ,, refl = cong (V-I⇒ b x) (uniqueBApp x M y y')
uniqueVal M (V-IΠ b x y) (V-IΠ b' x' y')  with uniqueBApp' M x x' y y'
... | refl ,, refl ,, refl ,, refl = cong (V-IΠ b x) (uniqueBApp x M y y')
```

```
lemV· : ∀{A B}{M : ∅ ⊢ A ⇒ B}{M'} → ¬ (Value M) → ¬ (Value (M · M'))
lemV· ¬VM (V-I⇒ b .(bubble p) (step p q VM')) = ⊥-elim (¬VM (V-I⇒ b p q))
lemV· ¬VM (V-IΠ b .(bubble p) (step p q VM')) = ⊥-elim (¬VM (V-I⇒ b p q))

lemV'· : ∀{A B}{M : ∅ ⊢ A ⇒ B}{M'} → ¬ (Value M') → ¬ (Value (M · M'))
lemV'· ¬VM' (V-I⇒ b .(bubble p) (step p q VM')) = ⊥-elim (¬VM' VM')
lemV'· ¬VM' (V-IΠ b .(bubble p) (step p q VM')) = ⊥-elim (¬VM' VM')

lemVunwrap :  ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}{C}{q : C ≡ _}{M}
  → ¬ (Value (unwrap {A = A}{B} M q))
lemVunwrap (V-I⇒ b p ())
lemVunwrap (V-IΠ b p ())

lemV·⋆ : ∀{K}{A : ∅ ⊢Nf⋆ K}{B}{M : ∅ ⊢ Π B}{C}{p : C ≡ B [ A ]Nf}
  → ¬ (Value M) → ¬ (Value (M ·⋆ A / p))
lemV·⋆ ¬VM (V-I⇒ b .(bubble p) (step⋆ p q r)) = ¬VM (V-IΠ b p q)
lemV·⋆ ¬VM (V-IΠ b .(bubble p) (step⋆ p q r)) = ¬VM (V-IΠ b p q)

lemBAppβ : ∀{A B}{b}{az as}{p : az <>> as ∈ arity b}{M : ∅ , A ⊢ B}{M'}
  → ¬ (BApp b p (ƛ M · M'))
lemBAppβ (step p () x)

lemBAppβ⋆ : ∀{K}{A : ∅ ⊢Nf⋆ K}{B}{b}{az as}{p : az <>> as ∈ arity b}{M : ∅ ,⋆ K ⊢ B}{C}{q : C ≡ B [ A ]Nf} → ¬ (BApp b p (Λ M ·⋆ A / q))
lemBAppβ⋆ (step⋆ p () refl)

lemVβ : ∀{A B}{M : ∅ , A ⊢ B}{M'} → ¬ (Value (ƛ M · M'))
lemVβ (V-I⇒ b p q) = lemBAppβ q
lemVβ (V-IΠ b p q) = lemBAppβ q

lemVβ⋆ : ∀{K}{A : ∅ ⊢Nf⋆ K}{B}{M : ∅ ,⋆ K ⊢ B}{C}{p : C ≡ B [ A ]Nf}
  → ¬ (Value (Λ M ·⋆ A / p))
lemVβ⋆ (V-I⇒ b p q) = lemBAppβ⋆ q
lemVβ⋆ (V-IΠ b p q) = lemBAppβ⋆ q


postulate lemVE : ∀{A B} M (E : EC A B) → Value (E [ M ]ᴱ) → Value M

{-
This currently triggers an agda bug:
Panic: Pattern match failure in do expression at
src/full/Agda/TypeChecking/Rules/LHS/Unify.hs:1313:7-14
when checking that the pattern V-I⇒ b p q has type
Value ((x ·r E) [ M ]ᴱ)

lemVE : ∀{A B} M (E : EC A B) → Value (E [ M ]ᴱ) → Value M
lemVE M []             V = V
lemVE M (x ·r E) (V-I⇒ b p q) = ?
lemVE M (x ·r E) (V-IΠ b p q) = ?
lemVE M (E l· x) (V-I⇒ b .(bubble p) (step p x₁ x₂)) = lemVE _ E (V-I⇒ b p x₁)
lemVE M (E l· x) (V-IΠ b .(bubble p) (step p x₁ x₂)) = lemVE _ E (V-I⇒ b p x₁)
lemVE M (E ·⋆ A / x)   V = {!!}
lemVE M (wrap E)       V = {!!}
lemVE M (unwrap E / x) V = {!!}
{-
lemVE M [] V = V
lemVE M (E l· M') (V-I⇒ b .(bubble p) (step p x x₁)) =
  lemVE _ E (V-I⇒ b p x)
lemVE M (E l· M') (V-IΠ b .(bubble p) (step p x x₁)) =
  lemVE _ E (V-I⇒ b p x)
lemVE M (VM' ·r E) (V-I⇒ b .(bubble p) (step p x x₁)) =
  lemVE _ E x₁
lemVE M (VM' ·r E) (V-IΠ b .(bubble p) (step p x x₁)) =
  lemVE _ E x₁
lemVE M (E ·⋆ A / refl) (V-I⇒ b .(bubble p) q (step⋆ p x)) =
  lemVE _ E (V-IΠ b p refl x)
lemVE M (E ·⋆ A / refl) (V-IΠ b .(bubble p) q (step⋆ p x)) =
  lemVE _ E (V-IΠ b p refl x)
lemVE M (wrap E) (V-wrap V) = lemVE _ E V
lemVE M (unwrap E) (V-I⇒ b p q ())
lemVE M (unwrap E) (V-IΠ b p q ())
-}
-}

lemBE : ∀{A B} M (E : EC A B){as a az b}{p : az <>> (a ∷ as) ∈ arity b}
  → BApp b p (E [ M ]ᴱ) → Value M
lemBE M [] {a = Term} q with bappTermLem _ M _ q
... | _ ,, _ ,, refl = V-I⇒ _ _ q
lemBE M [] {a = Type} q with bappTypeLem _ M _ q
... | _ ,, _ ,, refl = V-IΠ _ _ q
lemBE M (E l· x) (step p q x₁) = lemBE _ E q
lemBE M (x ·r E) (step p q x₁) = lemVE _ E x₁
lemBE M (E ·⋆ A / r) (step⋆ p q refl) = lemBE _ E q
lemBE M (wrap E) ()
lemBE M (unwrap E / r) ()


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
valred (V-I⇒ b .(bubble p) (step p () x₁)) (β-ƛ VN)
valred (V-IΠ b .(bubble p) (step p () x₁)) (β-ƛ VN)
valred (V-I⇒ b .(bubble p₁) (step⋆ p₁ () .p)) (β-Λ p)
valred (V-IΠ b .(bubble p₁) (step⋆ p₁ () .p)) (β-Λ p)
valred (V-I⇒ b p₁ ()) (β-wrap VN p)
valred (V-IΠ b p₁ ()) (β-wrap VN p)
valred (V-I⇒ b₁ .(bubble p₁) (step p₁ x x₁)) (β-sbuiltin b t p bt u vu)
  with uniqueBApp' t p₁ p x bt
... | refl ,, refl ,, () ,, refl
valred (V-IΠ b₁ .(bubble p₁) (step p₁ x x₁)) (β-sbuiltin b t p bt u vu)
  with uniqueBApp' t p₁ p x bt
... | refl ,, refl ,, () ,, refl
valred (V-I⇒ b₁ .(bubble p₁) (step⋆ p₁ x q)) (β-sbuiltin⋆ b t p bt A q)
  with uniqueBApp' t p₁ p x bt
... | refl ,, refl ,, () ,, refl
valred (V-IΠ b₁ .(bubble p₁) (step⋆ p₁ x q)) (β-sbuiltin⋆ b t p bt A r)
  with uniqueBApp' t p₁ p x bt
... | refl ,, refl ,, () ,, refl

{-
bapperr : ∀{A}{L : ∅ ⊢ A}{b az as}{p : az <>> as ∈ arity b}
  → Error L → BApp b p L → ⊥
bapperr () base
bapperr () (step p bs x)
bapperr () (step⋆ p bs)
-}

valerr : ∀{A}{L : ∅ ⊢ A} → Error L → Value L → ⊥
valerr E-error (V-I⇒ b p ())
valerr E-error (V-IΠ b p ())

{-
errred : ∀{A}{L N : ∅ ⊢ A} → Error L → L —→⋆ N → ⊥
errred E-error ()
-}
-- should replace this with something more general if something similar shows
-- up again
substƛVal : ∀{A A' B}{M : ∅ , A ⊢ B} (p : A ≡ A')
  → Value (substEq (λ A → ∅ ⊢ (A ⇒ B)) p (ƛ M))
substƛVal refl = V-ƛ _

BUILTIN-eq : ∀{A b b' az az'}(M : ∅ ⊢ A)(p : az <>> _ ∈ arity b)(p' : az' <>> _ ∈ arity b')(bv : BApp b p M)(bv' : BApp b' p' M)
  → BUILTIN' b p bv ≡ BUILTIN' b' p' bv'
BUILTIN-eq M p p' bv bv'
  with uniqueBApp' M p p' bv bv'
... | refl ,, refl ,, refl ,, refl
  with uniqueBApp p M bv bv'
... | refl = refl

determinism⋆ : ∀{A}{L N N' : ∅ ⊢ A} → L —→⋆ N → L —→⋆ N' → N ≡ N'
determinism⋆ (β-ƛ _) (β-ƛ _) = refl
determinism⋆ (β-Λ refl) (β-Λ refl) = refl
determinism⋆ (β-wrap _ refl) (β-wrap _ refl) = refl
determinism⋆ (β-sbuiltin b t p bt u vu) (β-sbuiltin b' .t p' bt' .u vu') =
  BUILTIN-eq _ (bubble p) (bubble p') (step p bt vu) (step p' bt' vu')
determinism⋆ (β-sbuiltin⋆ b t p bt A refl) (β-sbuiltin⋆ b' .t p' bt' .A refl) =
  BUILTIN-eq _ (bubble p) (bubble p') (step⋆ p bt refl) (step⋆ p' bt' refl)

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
U·⋆2 ¬VM eq [] refl (β (β-sbuiltin⋆ b _ p bt _ .eq)) U =
  ⊥-elim (¬VM (V-IΠ b p bt))
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
    ; [] refl (β (β-sbuiltin b .M p bt .N vu)) → ⊥-elim (¬VM (V-I⇒ b p bt))
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
    ; [] refl (β (β-sbuiltin b .M p bt .N VN)) → ⊥-elim (¬VN VN)
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
rlemma51! (M · N) | done (V-I⇒ b {as' = []}       p x) | done VN = step
  (λ V → valred V (β-sbuiltin b M p x N VN))
  []
  (β (β-sbuiltin b M p x N VN))
  refl
  λ { [] refl (β (β-sbuiltin b .M p bt .N vu)) → refl ,, refl ,, refl
    ; (E' l· N') refl q → ⊥-elim (valredex (lemBE _ E' x) q)
    ; (VM' ·r E') refl q → ⊥-elim (valredex (lemVE _ E' VN) q)}
rlemma51! (M · N) | done (V-I⇒ b {as' = a' ∷ as'} p x) | done VN =
  done (V-I b (bubble p) (step p x VN))
rlemma51! (Λ M) = done (V-Λ M)
rlemma51! (M ·⋆ A / x) with rlemma51! M
... | done (V-Λ M) = step
  lemVβ⋆
  []
  (β (β-Λ x))
  refl
  (U·⋆1 x)
rlemma51! (M ·⋆ A / x) | done (V-IΠ b {as' = []} p q) = step
  (λ V → valred V (β-sbuiltin⋆ b M p q A x))
  []
  (β (β-sbuiltin⋆ b M p q A x))
  refl
  λ E p' q' → U·⋆3 x E (V-IΠ b _ q) p' q'
rlemma51! (M ·⋆ A / x) | done (V-IΠ b {as' = x₁ ∷ as'} p q) =
  done (V-I b (bubble p) (step⋆ p q x))
... | step ¬VM E p q U = step
  (λ V → lemV·⋆ (λ V → ¬VM V) V)
  (E ·⋆ A / x)
  p
  (cong (_·⋆ A / x) q)
  λ E p q → U·⋆2 ¬VM x E p q U
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
{-
notErr : ∀{A B}{L L′ : ∅ ⊢ A}{E : EC B A} → L —→⋆ L′ → E [ L′ ]ᴱ ≡ error _ → ⊥
notErr {L = L}{L′}{E} x y with rlemma51! (E [ L′ ]ᴱ)
... | step x₁ E₁ x₂ x₃ x₄ = {!!}
-- what do we know? E [ L′ ]ᴱ == error B, so E == [] and L′ == error B
-- we also have that E [ L′ ] ᴱ == E₁ [ L₁ ]ᴱ and L₁ is a redex...
... | done x₁ = ⊥-elim (notVAL x₁ (ruleErr [] y))
-}
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