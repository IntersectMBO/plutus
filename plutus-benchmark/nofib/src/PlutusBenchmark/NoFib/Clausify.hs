{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module PlutusBenchmark.NoFib.Clausify where

import PlutusBenchmark.Common (Term, compiledCodeToTerm)

import PlutusTx qualified as Tx
import PlutusTx.List qualified as List
import PlutusTx.Plugin ()
import PlutusTx.Prelude as Plutus
import Prelude qualified as Haskell

type Var = Integer

type LRVars = ([Var], [Var]) -- % Lists of variables in lhs and rhs of formula

data Formula =
  Sym Var |   -- % Was Char, but that doesn't work well with PLC
  Not Formula |
  Dis Formula Formula |
  Con Formula Formula |
  Imp Formula Formula |
  Eqv Formula Formula
      deriving stock (Haskell.Show)
Tx.makeLift ''Formula

-- separate positive and negative literals, eliminating duplicates
clause :: Formula -> LRVars
clause p = clause' p ([] , [])
           where
           clause' (Dis p q)       x   = clause' p (clause' q x)
           clause' (Sym s)       (c,a) = (insert s c , a)
           clause' (Not (Sym s)) (c,a) = (c , insert s a)
{-# INLINABLE clause #-}

-- the main pipeline from propositional formulae to a list of clauses
clauses :: Formula -> [LRVars]
clauses = unicl . split . disin . negin . elim
{-# INLINABLE clauses #-}

conjunct :: Formula -> Bool
conjunct (Con _ _) = True
conjunct _         = False
{-# INLINABLE conjunct #-}

-- shift disjunction within conjunction
disin :: Formula -> Formula
disin (Dis p (Con q r)) = Con (disin (Dis p q)) (disin (Dis p r))
disin (Dis (Con p q) r) = Con (disin (Dis p r)) (disin (Dis q r))
disin (Dis p q) =
  if conjunct dp || conjunct dq then disin (Dis dp dq)
  else (Dis dp dq)
  where
  dp = disin p
  dq = disin q
disin (Con p q) = Con (disin p) (disin q)
disin p = p
{-# INLINABLE disin #-}

-- split conjunctive proposition into a list of conjuncts
split :: Formula -> [Formula]
split p = split' p []
          where
          split' (Con p q) a = split' p (split' q a)
          split' p a         = p : a
{-# INLINABLE split #-}

-- eliminate connectives other than not, disjunction and conjunction
elim :: Formula -> Formula
elim (Sym s)    = Sym s
elim (Not p)    = Not (elim p)
elim (Dis p q)  = Dis (elim p) (elim q)
elim (Con p q)  = Con (elim p) (elim q)
elim (Imp p q)  = Dis (Not (elim p)) (elim q)
elim (Eqv f f') = Con (elim (Imp f f')) (elim (Imp f' f))
{-# INLINABLE elim #-}

-- insertion of an item into an ordered list
-- Note: this is a corrected version from Colin (94/05/03 WDP)
insert :: (Ord t) => t -> [t] -> [t]
insert x [] = [x]
insert x p@(y:ys) =
  if x < y then x : p
  else if x > y then y : insert x ys
  else p
{-# INLINABLE insert #-}

-- shift negation to innermost positions
negin :: Formula -> Formula
negin (Not (Not p))   = negin p
negin (Not (Con p q)) = Dis (negin (Not p)) (negin (Not q))
negin (Not (Dis p q)) = Con (negin (Not p)) (negin (Not q))
negin (Dis p q)       = Dis (negin p) (negin q)
negin (Con p q)       = Con (negin p) (negin q)
negin p               = p
{-# INLINABLE negin #-}

-- does any symbol appear in both consequent and antecedent of clause
tautclause :: LRVars -> Bool
tautclause (c,a) = [x | x <- c, x `List.elem` a] /= []
{-# INLINABLE tautclause #-}

-- form unique clausal axioms excluding tautologies
unicl :: [Formula] -> [LRVars]
unicl a = List.foldr unicl' [] a
          where
          unicl' p x = if tautclause cp then x else insert cp x
                       where
                       cp = clause p :: LRVars
{-# INLINABLE unicl #-}

while :: (t -> Bool) -> (t -> t) -> t -> t
while p f x = if p x then while p f (f x) else x
{-# INLINABLE while #-}

formula1 :: Formula  -- % (a = a) = (a = a) = (a = a)
formula1 = Eqv (Eqv (Sym 1) (Sym 1))
               (Eqv (Eqv (Sym 1) (Sym 1))
                    (Eqv (Sym 1) (Sym 1)))
{-# INLINABLE formula1 #-}

-- % One execution takes about 0.35s and 300 MB
formula2 :: Formula  -- (a = a = a) = (a = a = a)
formula2 = Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
               (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
{-# INLINABLE formula2 #-}

-- % One execution takes about 1.5s and 660 MB
formula3 :: Formula  -- (a = a = a) = (a = a) = (a = a)
formula3 = Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
               (Eqv (Eqv (Sym 1) (Sym 1))
                    (Eqv (Sym 1) (Sym 1)))
{-# INLINABLE formula3 #-}

-- % One execution takes about 2s and 1 GB
formula4 :: Formula  -- (a = b = c) = (d = e) = (f = g)
formula4 = Eqv (Eqv (Sym 1) (Eqv (Sym 2) (Sym 3)))
               (Eqv (Eqv (Sym 4) (Sym 5))
                    (Eqv (Sym 6) (Sym 7)))
{-# INLINABLE formula4 #-}

-- % One execution takes about 11s and 5 GB
formula5 :: Formula  -- (a = a = a) = (a = a = a) = (a = a)
formula5 = Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
               (Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
                    (Eqv (Sym 1) (Sym 1)))
{-# INLINABLE formula5 #-}

-- % Overflow
formula6 :: Formula  -- (a = a = a) = (a = a = a) = (a = a = a)
formula6 = Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
               (Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
                    (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1))))
{-# INLINABLE formula6 #-}

-- % Overflow
formula7 :: Formula -- (a = b = c) = (d = e = f) = (g = h = i)
formula7 = Eqv (Eqv (Sym 1) (Eqv (Sym 2) (Sym 3)))
               (Eqv (Eqv (Sym 4) (Eqv (Sym 5) (Sym 6)))
                    (Eqv (Sym 7) (Eqv (Sym 8) (Sym 9))))
{-# INLINABLE formula7 #-}

data StaticFormula = F1 | F2 | F3 | F4 | F5 | F6 | F7
Tx.makeLift ''StaticFormula

getFormula :: StaticFormula -> Formula
getFormula =
    \case
     F1 -> formula1
     F2 -> formula2
     F3 -> formula3
     F4 -> formula4
     F5 -> formula5
     F6 -> formula6
     F7 -> formula7
{-# INLINABLE getFormula #-}

-- % Haskell entry point for testing
runClausify :: StaticFormula -> [LRVars]
runClausify = clauses . getFormula
{-# INLINABLE runClausify #-}

mkClausifyCode :: StaticFormula -> Tx.CompiledCode [LRVars]
mkClausifyCode formula =
  $$(Tx.compile [|| runClausify ||])
  `Tx.unsafeApplyCode`
  Tx.liftCodeDef formula

mkClausifyTerm :: StaticFormula -> Term
mkClausifyTerm formula = compiledCodeToTerm $ mkClausifyCode formula
