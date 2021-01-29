{-# LANGUAGE EmptyDataDecls    #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE LambdaCase        #-}

module Lambda where

import           Numeric.Natural (Natural)

data Tm a = Lam (Tm (Maybe a))
          | App (Tm a) (Tm a)
          | Var a
          | Val Natural
          | Add (Tm a) (Tm a)
              deriving Show

ext :: (a -> b) -> Maybe a -> Maybe b
ext = fmap

ren :: (a -> b) -> Tm a -> Tm b
ren ρ (Lam t)   = Lam (ren (ext ρ) t)
ren ρ (App t u) = App (ren ρ t) (ren ρ u)
ren ρ (Var x)   = Var (ρ x)
ren ρ (Val n)   = Val n
ren ρ (Add t u) = Add (ren ρ t) (ren ρ u)

exts :: (a -> Tm b) -> Maybe a -> Tm (Maybe b)
exts σ Nothing  = Var Nothing
exts σ (Just x) = ren Just (σ x)

sub :: (a -> Tm b) -> Tm a -> Tm b
sub σ (Lam t)   = Lam (sub (exts σ) t)
sub σ (App t u) = App (sub σ t) (sub σ u)
sub σ (Var x)   = σ x
sub σ (Val n)   = Val n
sub σ (Add t u) = Add (sub σ t) (sub σ u)

sub1 :: Tm (Maybe a) -> Tm a -> Tm a
sub1 t u
  = sub
      (\case
           Just x  -> Var x
           Nothing -> u)
      t

data Empty deriving Show

step :: Tm Empty -> Maybe (Tm Empty)
step (Lam t)               = Nothing
step (App (Lam t) u)       = Just (sub1 t u)
step (App t u)             = fmap (\ t -> App t u) (step t)
step (Val n)               = Nothing
step (Add (Val m) (Val n)) = Just (Val (m + n))
step (Add (Val m) u)       = fmap (Add (Val m)) (step u)
step (Add t u)             = fmap (\ t -> Add t u) (step t)
step (Var x)               = error "step: impossible"

data Gas = Z
         | S Gas

stepper :: Gas -> Tm Empty -> Maybe (Tm Empty)
stepper Z t     = Nothing
stepper (S n) t = maybe (Just t) (stepper n) (step t)

ex :: Tm Empty
ex = App (Lam (Add (Val 2) (Var Nothing))) (Val 2)

