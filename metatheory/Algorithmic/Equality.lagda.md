```
module Algorithmic.Equality where
```

```
open import Type
open import Type.BetaNormal
open import Type.BetaNormal.Equality
open import Algorithmic
open import Type.BetaNBE
open import Type.BetaNBE.RenamingSubstitution renaming (_[_]Nf to _[_])
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
```

```
cohVar : ∀{Φ}{A A' : Φ ⊢Nf⋆ *}{Γ Γ'}(p : Γ ≡Ctx Γ')(q : A ≡Nf A')(x : Γ ∋ A)
    → VarEq p q x (conv∋ p q x)
cohVar (p , p') q (Z r)   = ZEq r (transNf (symNf p') (transNf r q)) p' p q
cohVar (p , p') q (S x)   = SEq p p' q (cohVar p q x)
cohVar (p ,⋆ K) q (T x r) = TEq r (transNf r q) p reflNf q (cohVar p reflNf x)


```
