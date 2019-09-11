```
module Algorithmic.Equality where
```

```
open import Function hiding (_∋_)
open import Data.Product renaming (_,_ to _,,_)

open import Type
open import Type.BetaNormal
open import Type.BetaNormal.Equality
open import Algorithmic
open import Type.BetaNBE
open import Type.BetaNBE.RenamingSubstitution renaming (_[_]Nf to _[_])
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf 

```

```
data VarEq : ∀{Φ}{A A' : Φ ⊢Nf⋆ *}{Γ Γ'}
  → Γ ≡Ctx Γ' → A ≡Nf A'  → Γ ∋ A → Γ' ∋ A' → Set
  where
    ZEq : ∀ {Φ}{Γ Γ' : Ctx Φ}
      → {A B : Φ ⊢Nf⋆ *}(p : A ≡Nf B)
      → {A' B' : Φ ⊢Nf⋆ *}(p' : A' ≡Nf B')
      → (p'' : A ≡Nf A') -- this is derivable from the other three
      → (q : Γ ≡Ctx Γ')
      → (r : B ≡Nf B') 
      → VarEq (q , p'') r (Z p) (Z p')
    SEq : ∀ {Φ}{Γ Γ' : Ctx Φ}{A B : Φ ⊢Nf⋆ *}{A' B' : Φ ⊢Nf⋆ *}
      → {x : Γ ∋ B}{x' : Γ' ∋ B'}
      → (p : Γ ≡Ctx Γ')
      → (q : A ≡Nf A')
      → (r : B ≡Nf B')
      → VarEq p r x x'
      → VarEq (p , q) r (S x) (S x')
    TEq : ∀ {Φ}{Γ Γ' : Ctx Φ}{K}
      → {A : Φ ⊢Nf⋆ *}{B : Φ ,⋆ K ⊢Nf⋆ *}
      → {A' : Φ ⊢Nf⋆ *}{B' : Φ ,⋆ K ⊢Nf⋆ *}
      → (p : weakenNf A ≡Nf B)
      → (p' : weakenNf A' ≡Nf B')
      → (q : Γ ≡Ctx Γ')
      → (r : A ≡Nf A')
      → (s : B ≡Nf B')
      → {x : Γ ∋ A}{x' : Γ' ∋ A'}
      → VarEq q  r x x'
      → VarEq (q ,⋆ K) s (T x p) (T x' p')

-- all we can change here is the context I think
open import Data.List hiding ([_])
open import Data.Unit
TelEq : ∀{Φ}{Γ Γ' : Ctx Φ} → Γ ≡Ctx Γ' → 
  ∀ {Δ} As
  (σ : ∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J)
  → (ts : Tel Γ Δ σ As)
  → (ts' : Tel Γ' Δ σ As)
  → Set
     
data Eq : ∀{Φ}{A A' : Φ ⊢Nf⋆ *}{Γ Γ'} → Γ ≡Ctx Γ'
  → A ≡Nf A' → Γ ⊢ A → Γ' ⊢ A' → Set where
  
  varEq : ∀{Φ}{A A' : Φ ⊢Nf⋆ *}{Γ Γ'}(p : Γ ≡Ctx Γ')(q : A ≡Nf A')
    → {x : Γ ∋ A}{x'  : Γ' ∋ A'}
    → VarEq p q x x' → Eq p q (` x) (` x')
  ƛEq : ∀{Φ Γ Γ'}(p : Γ ≡Ctx Γ'){A B A' B' : Φ ⊢Nf⋆ *}
    → (q : A ≡Nf A')
    → (r : B ≡Nf B')
    → {t : Γ , A ⊢ B}
    → {t' : Γ' , A' ⊢ B'}
    → ∀{x x'}
    → Eq (p , q) r t t'
    → Eq p (⇒≡Nf q r) (ƛ x t) (ƛ x' t')

  ·Eq : ∀{Φ Γ Γ'}(p : Γ ≡Ctx Γ'){A B A' B' : Φ ⊢Nf⋆ *}
    → (q : A ≡Nf A')
    → (r : B ≡Nf B')
    → {t : Γ ⊢ A ⇒ B}
    → {t' : Γ' ⊢ A' ⇒ B'}
    → Eq p (⇒≡Nf q r) t t'
    → {u : Γ ⊢ A}
    → {u' : Γ' ⊢ A'}
    → Eq p q u u'
    → Eq p r (t · u) (t' · u')

  ΛEq : ∀{Φ Γ Γ'}(p : Γ ≡Ctx Γ'){K}{A A' : Φ ,⋆ K ⊢Nf⋆ *}
    → (q : A ≡Nf A')
    → {t : Γ ,⋆ K ⊢ A}
    → {t' : Γ' ,⋆ K ⊢ A'}
    → Eq (p ,⋆ K) q t t'
    → ∀{x x'}
    → Eq p (Π≡Nf q) (Λ x t) (Λ x' t')
    
  ·⋆Eq : ∀{Φ Γ Γ'}(p : Γ ≡Ctx Γ'){K}{A A' : Φ ,⋆ K ⊢Nf⋆ *}
    → (q : A ≡Nf A')
    → {B B' : Φ ⊢Nf⋆ K}
    → (r : B ≡Nf B')
    → ∀{x x'}
    → {L : Γ ⊢ Π x A}
    → {L' : Γ' ⊢ Π x' A'}
    → Eq p (Π≡Nf q) L L'
    → {C C' : Φ ⊢Nf⋆ *}
    → (s : (A [ B ]) ≡Nf C)
    → (s' : (A' [ B' ]) ≡Nf C')
    → (s'' : C ≡Nf C') -- derivable
    → Eq p s'' (·⋆ L B s) (·⋆ L' B' s')

  wrap1Eq : ∀{Φ Γ Γ'}(p : Γ ≡Ctx Γ'){K}
    → {pat pat' : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg arg' : Φ ⊢Nf⋆ K}
    → (q : pat ≡Nf pat')
    → (q' : arg ≡Nf arg')
    → {term : Γ ⊢ nf (embNf pat · (μ1 · embNf pat) · embNf arg)}
    → {term' : Γ' ⊢ nf (embNf pat' · (μ1 · embNf pat') · embNf arg')}
    → (r : nf (embNf pat · (μ1 · embNf pat) · embNf arg)
           ≡Nf
           nf (embNf pat' · (μ1 · embNf pat') · embNf arg'))
    → Eq p r term term'
    → Eq p
         (ne≡Nf (·≡Ne (·≡Ne μ≡Ne q) q'))
         (wrap1 pat arg term)
         (wrap1 pat' arg' term')

  unwrap1Eq : ∀{Φ Γ Γ'}(p : Γ ≡Ctx Γ'){K}
    → {pat pat' : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg arg' : Φ ⊢Nf⋆ K}
    → (q : pat ≡Nf pat')
    → (q' : arg ≡Nf arg')
    → {term : Γ ⊢ ne (μ1 · pat · arg)}
    → {term' : Γ' ⊢ ne (μ1 · pat' · arg')}
    → Eq p (ne≡Nf (·≡Ne (·≡Ne μ≡Ne q) q')) term term'
    → {B : Φ ⊢Nf⋆ *}
    → (r : nf (embNf pat · (μ1 · embNf pat) · embNf arg) ≡Nf B)
    → {B' : Φ ⊢Nf⋆ *}
    → (r' : nf (embNf pat' · (μ1 · embNf pat') · embNf arg') ≡Nf B')
    → (r'' : B ≡Nf B')
      → Eq p r'' (unwrap1 term r) (unwrap1 term' r')

  conEq : ∀{Φ Γ Γ'}(p : Γ ≡Ctx Γ'){tcn}
    → (t : TermCon {Φ} (con tcn))
    → (q : con {Φ} tcn ≡Nf con tcn) -- could be reflNf
    → Eq p q (con {Γ = Γ} t) (con {Γ = Γ'} t)


  builtinEq : ∀{Φ Γ Γ'}(p : Γ ≡Ctx Γ'){bn} →
    let Δ ,, As ,, C = SIG bn in 
      (σ : ∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J)
    → {ts : Tel Γ Δ σ As}
    → {ts' : Tel Γ' Δ σ As}
    → TelEq p As σ ts ts'
    → {B B' : Φ ⊢Nf⋆ *}
    → (q : substNf σ C ≡Nf B)
    → (q' : substNf σ C ≡Nf B')
    → (r : B ≡Nf B')
    → Eq p r (builtin bn σ ts q) (builtin bn σ ts' q')

  errorEq : ∀{Φ}{A A' : Φ ⊢Nf⋆ *}{Γ Γ'}(p : Γ ≡Ctx Γ')(q : A ≡Nf A')
    → Eq p q (error A) (error A')


TelEq p []       σ _ _ = ⊤
TelEq p (A ∷ As) σ (t ,, ts) (t' ,, ts') =
  Eq p reflNf t t' × TelEq p As σ ts ts'

```

```
cohVar : ∀{Φ}{A A' : Φ ⊢Nf⋆ *}{Γ Γ'}(p : Γ ≡Ctx Γ')(q : A ≡Nf A')(x : Γ ∋ A)
    → VarEq p q x (conv∋ p q x)
cohVar (p , p') q (Z r)   = ZEq r (transNf (symNf p') (transNf r q)) p' p q
cohVar (p , p') q (S x)   = SEq p p' q (cohVar p q x)
cohVar (p ,⋆ K) q (T x r) = TEq r (transNf r q) p reflNf q (cohVar p reflNf x)

cohTel : ∀ {Φ Ψ}{Γ Γ' : Ctx Φ}
  → (p : Γ ≡Ctx Γ')
  → (σ : ∀{J} → Ψ ∋⋆ J → Φ ⊢Nf⋆ J)
  → (As : List (Ψ ⊢Nf⋆ *))
  → (tel : Tel Γ Ψ σ As)
  → TelEq p As σ tel (convTel p σ As tel)

coh : ∀{Φ}{A A' : Φ ⊢Nf⋆ *}{Γ Γ'}(p : Γ ≡Ctx Γ')(q : A ≡Nf A')(t : Γ ⊢ A)
  → Eq p q t (conv⊢ p q t)
coh p q (` x)               = varEq p q (cohVar p q x)
coh p (⇒≡Nf q q')   (ƛ x t) = ƛEq p q q' (coh (p , q) q' t)
coh p q (t · u)             =
 ·Eq p reflNf q (coh p (⇒≡Nf reflNf q) t) (coh p reflNf u)
coh p (Π≡Nf q)      (Λ x t) = ΛEq p q (coh (p ,⋆ _) q t)
coh p q (·⋆ t A r)          =
  ·⋆Eq p reflNf reflNf (coh p (Π≡Nf reflNf) t) r (transNf r q) q
coh p (ne≡Nf (·≡Ne (·≡Ne μ≡Ne q) q')) (wrap1 pat arg t) =
  wrap1Eq p q q' _ (coh p _ t)
coh p q (unwrap1 t r) = unwrap1Eq p reflNf reflNf (coh p _ t) r (transNf r q) q
coh p con≡Nf (con c) = conEq p c con≡Nf
coh p q (builtin bn σ tel r) =
  builtinEq p σ (cohTel p σ _ tel) r (transNf r q) q
coh p q (error A) = errorEq p q

cohTel p σ []       _          = tt
cohTel p σ (A ∷ As) (t ,, tel) = coh p reflNf t ,, cohTel p σ As tel
```
