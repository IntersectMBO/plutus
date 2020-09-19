{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -fwarn-missing-signatures     #-}
{-# OPTIONS_GHC -fno-warn-unused-imports      #-}

{-# OPTIONS_GHC -fexpose-all-unfoldings       #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr              #-}
{-# OPTIONS_GHC -fno-strictness               #-}
{-# OPTIONS_GHC -fno-worker-wrapper           #-}


module Plutus.Benchmark.Clausify where

import           Control.Monad
import           System.Environment

import qualified Language.PlutusCore.Pretty as PLC
import qualified Language.PlutusTx          as Tx
import           Language.PlutusTx.Prelude  as TxPrelude hiding (replicate)

-- import Data.Ix
-- import System.Environment
-- import Control.Monad (forM_)

type Var = Integer

type LRVars = ([Var], [Var]) -- Lists of variables in lhs and rhs of formula
    
data Formula =
  Sym Var |   -- Was Char, but that doesn't work well with PLC
  Not Formula |
  Dis Formula Formula |
  Con Formula Formula |
  Imp Formula Formula |
  Eqv Formula Formula
      deriving (Show)
               
-- separate positive and negative literals, eliminating duplicates
{-# INLINABLE clause #-}
clause :: Formula -> LRVars
clause p = clause' p ([] , [])
           where
           clause' (Dis p q)       x   = clause' p (clause' q x)
           clause' (Sym s)       (c,a) = (insert s c , a)
           clause' (Not (Sym s)) (c,a) = (c , insert s a)

{-
-- the main pipeline from propositional formulae to printed clauses
{-# INLINABLE clauses #-}
clauses :: Formula -> ([Char], [Char])
clauses :: [Char] -> [Char]
clauses = concat . map disp . unicl . split . disin . negin . elim . parse
-}

-- the main pipeline from propositional formulae to a list of clauses
{-# INLINABLE clauses #-}
clauses :: Formula -> [LRVars]
clauses = unicl . split . disin . negin . elim 

{-# INLINABLE conjunct #-}
conjunct :: Formula -> Bool
conjunct (Con p q) = True
conjunct p = False

-- shift disjunction within conjunction
{-# INLINABLE disin #-}
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

-- split conjunctive proposition into a list of conjuncts
{-# INLINABLE split #-}
split :: Formula -> [Formula]
split p = split' p []
          where
          split' (Con p q) a = split' p (split' q a)
          split' p a = p : a


-- eliminate connectives other than not, disjunction and conjunction
{-# INLINABLE elim #-}
elim :: Formula -> Formula
elim (Sym s) = Sym s
elim (Not p) = Not (elim p)
elim (Dis p q) = Dis (elim p) (elim q)
elim (Con p q) = Con (elim p) (elim q)
elim (Imp p q) = Dis (Not (elim p)) (elim q)
elim (Eqv f f') = Con (elim (Imp f f')) (elim (Imp f' f))


-- insertion of an item into an ordered list
-- Note: this is a corrected version from Colin (94/05/03 WDP)
{-# INLINABLE insert #-}
insert :: (Ord t) => t -> [t] -> [t]
insert x [] = [x]
insert x p@(y:ys) =
  if x < y then x : p
  else if x > y then y : insert x ys
  else p

-- shift negation to innermost positions
{-# INLINABLE negin #-}
negin :: Formula -> Formula
negin (Not (Not p)) = negin p
negin (Not (Con p q)) = Dis (negin (Not p)) (negin (Not q))
negin (Not (Dis p q)) = Con (negin (Not p)) (negin (Not q))
negin (Dis p q) = Dis (negin p) (negin q)
negin (Con p q) = Con (negin p) (negin q)
negin p = p

-- does any symbol appear in both consequent and antecedent of clause
{-# INLINABLE tautclause #-}
tautclause :: LRVars -> Bool
tautclause (c,a) = [x | x <- c, x `elem` a] /= []

-- form unique clausal axioms excluding tautologies
{-# INLINABLE unicl #-}
unicl :: [Formula] -> [LRVars]
unicl a = foldr unicl' [] a
          where
          unicl' p x = if tautclause cp then x else insert cp x
                       where
                       cp = clause p :: LRVars

{-# INLINABLE while #-}
while :: (t -> Bool) -> (t -> t) -> t -> t
while p f x = if p x then while p f (f x) else x

              
{-# INLINABLE replicate #-}
replicate :: Integer -> a -> [a]
replicate n a = if n == 0 then []
                else a:(replicate (n-1) a)

{-# INLINABLE formula1 #-}  -- Overflow
formula1 :: Formula  -- (a = a = a) = (a = a = a) = (a = a = a) 
formula1 = Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
               (Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
                    (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1))))

{-# INLINABLE formula2 #-} -- Overflow
formula2 :: Formula -- (a = b = c) = (d = e = f) = (g = h = i) 
formula2 = Eqv (Eqv (Sym 1) (Eqv (Sym 2) (Sym 3)))
               (Eqv (Eqv (Sym 4) (Eqv (Sym 5) (Sym 6)))
                    (Eqv (Sym 7) (Eqv (Sym 8) (Sym 9))))

{-# INLINABLE formula3 #-}
formula3 :: Formula  -- (a = a = a) = (a = a = a)
formula3 = Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
               (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
                                                  
{-# INLINABLE formula4 #-} -- One execution takes about 0.35s and 300 MB
formula4 :: Formula  -- (a = a) = (a = a) = (a = a) 
formula4 = Eqv (Eqv (Sym 1) (Sym 1))
               (Eqv (Eqv (Sym 1) (Sym 1))
                    (Eqv (Sym 1) (Sym 1)))

{-# INLINABLE formula5 #-}  -- One execution takes about 1.5s and 660 MB 
formula5 :: Formula  -- (a = a = a) = (a = a) = (a = a) 
formula5 = Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
               (Eqv (Eqv (Sym 1) (Sym 1))
                    (Eqv (Sym 1) (Sym 1)))

{-# INLINABLE formula5a #-}  -- One execution takes about 2s and 1 GB 
formula5a :: Formula  -- (a = b = c) = (d = e) = (f = g) 
formula5a = Eqv (Eqv (Sym 1) (Eqv (Sym 2) (Sym 3)))
               (Eqv (Eqv (Sym 4) (Sym 5))
                    (Eqv (Sym 6) (Sym 7)))

{-# INLINABLE formula6 #-}  -- One execution takes about 11s and 5 GB 
formula6 :: Formula  -- (a = a = a) = (a = a = a) = (a = a) 
formula6 = Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
               (Eqv (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
                    (Eqv (Sym 1) (Sym 1)))


count :: Integer
count = 1
               
main :: IO ()
main = do
  let code = Tx.getPlc $ $$(Tx.compile [|| map clauses (replicate count formula5a)  ||])
  print . PLC.prettyPlcClassicDebug $ code

{- Original main
{-# INLINABLE res #-}
res :: Integer -> [Char]
res n = concat (map clauses xs)
    where xs = take (fromIntegral n) (repeat "(a = a = a) = (a = a = a) = (a = a = a)")
          {-# NOINLINE xs #-}
main :: IO ()
main = forM_ [1..1] $ const $ do
  (n:_) <- getArgs
  putStr (res (read n))
-}



-- Parsing: currently hopeless in PLC due to limited support for Char 
{-


data StackFrame = Ast Formula | Lex Char

{-# INLINABLE opri #-}
opri :: Char -> Integer
opri '(' = 0
opri '=' = 1
opri '>' = 2
opri '|' = 3
opri '&' = 4
opri '~' = 5

-- parsing a propositional formula
{-# INLINABLE parse #-}
parse :: [Char] -> Formula
parse t = f where [Ast f] = parse' t []

{-# INLINABLE parse' #-}
parse' :: [Char] -> [StackFrame] -> [StackFrame]
parse' [] s = redstar s
parse' (' ':t) s = parse' t s
parse' ('(':t) s = parse' t (Lex '(' : s)
parse' (')':t) s = parse' t (x:s')
                   where
                   (x : Lex '(' : s') = redstar s
parse' (c:t) s = if inRange ('a','z') c then parse' t (Ast (Sym c) : s)
                 else if spri s > opri c then parse' (c:t) (red s)
                 else parse' t (Lex c : s)

-- reduction of the parse stack
{-# INLINABLE red #-}
red :: [StackFrame] -> [StackFrame]
red (Ast p : Lex '=' : Ast q : s) = Ast (Eqv q p) : s
red (Ast p : Lex '>' : Ast q : s) = Ast (Imp q p) : s
red (Ast p : Lex '|' : Ast q : s) = Ast (Dis q p) : s
red (Ast p : Lex '&' : Ast q : s) = Ast (Con q p) : s
red (Ast p : Lex '~' : s) = Ast (Not p) : s

-- iterative reduction of the parse stack
{-# INLINABLE redstar #-}
redstar :: [StackFrame] -> [StackFrame]
redstar = while ((/=) 0 . spri) red

-- old: partain:
--redstar = while ((/=) (0::Int) . spri) red


{-# INLINABLE spaces #-}
spaces :: [Char]
spaces = repeat ' '

-- priority of the parse stack
{-# INLINABLE spri #-}
spri :: [StackFrame] -> Integer
spri (Ast x : Lex c : s) = opri c
spri s = 0

{-# INLINABLE interleave #-}
interleave :: [a] -> [a] -> [a]
interleave (x:xs) ys = x : interleave ys xs
interleave []     _  = []

-- format pair of lists of propositional symbols as clausal axiom
{-# INLINABLE disp #-}
disp :: ([Char], [Char]) -> [Char]
disp (l,r) = interleave l spaces ++ "<=" ++ interleave spaces r ++ "\n"

-}
