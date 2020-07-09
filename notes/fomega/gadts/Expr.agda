{-# OPTIONS --type-in-type #-}

open import Function
open import Data.Nat.Base
open import Data.Bool.Base
open import Data.Product

{-# NO_POSITIVITY_CHECK #-}
record IFix {I : Set} (F : (I -> Set) -> I -> Set) (i : I) : Set where
  constructor wrap
  field unwrap : F (IFix F) i
open IFix

data Expr : Set -> Set where
  Lit  : ℕ -> Expr ℕ
  Inc  : Expr ℕ -> Expr ℕ
  IsZ  : Expr ℕ -> Expr Bool
  Pair : ∀ {A B} -> Expr A -> Expr B -> Expr (A × B)
  Fst  : ∀ {A B} -> Expr (A × B) -> Expr A
  Snd  : ∀ {A B} -> Expr (A × B) -> Expr B

-- As usually the pattern vector of a Scott-encoded data type encodes pattern-matching.
ExprF′ : (Set -> Set) -> Set -> Set
ExprF′
  = λ Rec I
  -> (R : Set -> Set)
  -> (ℕ -> R ℕ)
  -> (Rec ℕ -> R ℕ)
  -> (Rec ℕ -> R Bool)
  -> (∀ {A B} -> Rec A -> Rec B -> R (A × B))
  -> (∀ {A B} -> Rec (A × B) -> R A)
  -> (∀ {A B} -> Rec (A × B) -> R B)
  -> R I

Expr′ : Set -> Set
Expr′ = IFix ExprF′

expr-to-expr′ : ∀ {A} -> Expr A -> Expr′ A
expr-to-expr′ (Lit x)    = wrap λ R lit inc isZ pair fst snd -> lit x
expr-to-expr′ (Inc x)    = wrap λ R lit inc isZ pair fst snd -> inc (expr-to-expr′ x)
expr-to-expr′ (IsZ x)    = wrap λ R lit inc isZ pair fst snd -> isZ (expr-to-expr′ x)
expr-to-expr′ (Pair x y) = wrap λ R lit inc isZ pair fst snd -> pair (expr-to-expr′ x) (expr-to-expr′ y)
expr-to-expr′ (Fst p)    = wrap λ R lit inc isZ pair fst snd -> fst (expr-to-expr′ p)
expr-to-expr′ (Snd p)    = wrap λ R lit inc isZ pair fst snd -> snd (expr-to-expr′ p)

{-# TERMINATING #-}
expr′-to-expr : ∀ {A} -> Expr′ A -> Expr A
expr′-to-expr e =
  unwrap
    e
    Expr
    Lit
    (Inc ∘ expr′-to-expr)
    (IsZ ∘ expr′-to-expr)
    (λ x y -> Pair (expr′-to-expr x) (expr′-to-expr y))
    (Fst ∘ expr′-to-expr)
    (Snd ∘ expr′-to-expr)

isZero : ℕ -> Bool
isZero zero    = true
isZero (suc _) = false

{-# TERMINATING #-}
evalExpr′ : ∀ {A} -> Expr′ A -> A
evalExpr′ e =
  unwrap
    e
    id
    id
    (suc ∘ evalExpr′)
    (isZero ∘ evalExpr′)
    (λ x y -> (evalExpr′ x , evalExpr′ y))
    (proj₁ ∘ evalExpr′)
    (proj₂ ∘ evalExpr′)
