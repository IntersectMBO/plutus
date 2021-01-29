module Lambda where

{-# FOREIGN AGDA2HS 
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE EmptyDataDeriving #-}
#-}


-- import the Ulf's Agdaized version of the Haskell prelude
open import Haskell.Prelude hiding (e)
open import Relation.Binary.PropositionalEquality

-- The syntax of STLC + nats and addition

data Tm (a : Set) : Set where
  Lam : Tm (Maybe a) → Tm a
  App : Tm a → Tm a → Tm a
  Var : a → Tm a
  Val : Nat → Tm a
  Add : Tm a → Tm a → Tm a

{-# COMPILE AGDA2HS Tm deriving Show #-}

ext : (a → b) → Maybe a → Maybe b
ext = fmap

{-# COMPILE AGDA2HS ext #-}

ren : (a → b) → Tm a → Tm b
ren ρ (Lam t)   = Lam (ren (ext ρ) t)
ren ρ (App t u) = App (ren ρ t) (ren ρ u)
ren ρ (Var x)   = Var (ρ x)
ren ρ (Val n)   = Val n
ren ρ (Add t u) = Add (ren ρ t) (ren ρ u)

{-# COMPILE AGDA2HS ren #-}

exts : (a → Tm b) → Maybe a → Tm (Maybe b)
exts σ Nothing  = Var Nothing
exts σ (Just x) = ren Just (σ x)

{-# COMPILE AGDA2HS exts #-}

sub : (a → Tm b) → Tm a → Tm b
sub σ (Lam t)   = Lam (sub (exts σ) t)
sub σ (App t u) = App (sub σ t) (sub σ u)
sub σ (Var x)   = σ x
sub σ (Val n)   = Val n
sub σ (Add t u) = Add (sub σ t) (sub σ u)

{-# COMPILE AGDA2HS sub #-}

-- correctness of renaming and substitution
-- easy to prove in Agda

-- Tm is a functor
-- ren = fmap
postulate ren-id   : (t : Tm a)
                   → ren id t ≡ t
postulate ren-comp : (t : Tm a)(ρ : b → c)(ρ' : a → b)
                   → ren (ρ ∘ ρ') t ≡ ren ρ (ren ρ' t)

-- Tm is a monad
-- Var = return
-- sub = (=<<)

postulate sub-id   : (t : Tm a)
                   → sub Var t ≡ t
postulate sub-comp : (t : Tm a)(σ : b → Tm c)(σ' : a → Tm b)
                   → sub (sub σ ∘ σ') t ≡ sub σ (sub σ' t)

-- back to the program...

sub1 : Tm (Maybe a) → Tm a → Tm a
sub1 t u = sub (λ where (Just x) → Var x; Nothing → u) t

{-# COMPILE AGDA2HS sub1 #-}

data Empty : Set where

{-# COMPILE AGDA2HS Empty deriving Show #-}

-- small step reduction
-- quite minimal and loosely specified
-- note no variable case

step : Tm Empty → Maybe (Tm Empty)
step (Lam t)               = Nothing
step (App (Lam t) u)       = Just (sub1 t u)
step (App t u)             = fmap (λ t → App t u) (step t)
step (Val n)               = Nothing
step (Add (Val m) (Val n)) = Just (Val (m + n))
step (Add (Val m) u)       = fmap (Add (Val m)) (step u)
step (Add t u)             = fmap (λ t → Add t u) (step t)

{-# COMPILE AGDA2HS step #-}

data Gas : Set where
  Z : Gas
  S : Gas → Gas

{-# COMPILE AGDA2HS Gas #-}

-- iterate small step reduction for a given number of steps 

stepper : Gas → Tm Empty → Maybe (Tm Empty)
stepper Z     t = Nothing -- out of gas
stepper (S n) t = maybe (Just t) (stepper n) (step t)

{-# COMPILE AGDA2HS stepper #-}

-- (\x -> 2 + x) 2
ex : Tm Empty
ex = App (Lam (Add (Val 2) (Var Nothing))) (Val 2)

{-# COMPILE AGDA2HS ex #-}
