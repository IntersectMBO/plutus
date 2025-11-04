{-% nofib/spectral/constraints converted to Plutus.
    Renamed to avoid conflict with existing package. %-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
{-# OPTIONS_GHC -fno-warn-orphans             #-}
{-# OPTIONS_GHC -fno-warn-unused-matches      #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

module PlutusBenchmark.NoFib.Queens where

{- Andrew Tolmach and Thomas Nordin's contraint solver. See Proceedings of WAAAPL '99 -}

import Control.DeepSeq (NFData)
import Control.Monad (forM_)
import Data.Char (isSpace)
import GHC.Generics
import Prelude qualified as Haskell
import System.Environment

import PlutusBenchmark.Common (Term, compiledCodeToTerm)

import PlutusCore.Pretty qualified as PLC
import PlutusTx qualified as Tx
import PlutusTx.List as List hiding (sortBy)
import PlutusTx.Plugin ()
import PlutusTx.Prelude as TxPrelude hiding (abs)

-----------------------------
-- The main program
-----------------------------

{-% This program computes the number of mutually non-attacking arrangements
    of n queens on an n x n chessboard.  It's quite sophisticated: there's a
    generic constraint solver that takes an algorithm as a parameter.  There are
    five different algorithms, and the original behaviour was to try each of
    these on a board if size NxN, where N is a parameter supplied by the user.
    The Haskell version can run all five algorithms one after the other hundreds
    of times on an 8x8 board in a few seconds.

    Compiling into Plutus, I tried to run all five algorithms one after the other
    (in a single run of the program) on a 5x5 board on the CEK machine on an 8 GB
    machine.  The program was just able to complete in about 23s, but with some
    swapping.

    The resource consumption isn't so bad for the individual algorithms.  Here
    are figures for the time and memory usage for one run of the Plutus version
    of each algorithm on a 5x5 board on the same machine:

    bt:    2.9s, 1.2 GB
    bm:    2.5s, 830 MB
    bjbt:  2.7s, 933 MB
    bjbt': 3.0s, 1.1 GB
    fc:    7.5s, 3.2 GB

%-}

data Algorithm = Bt
               | Bm
               | Bjbt1
               | Bjbt2
               | Fc
               deriving stock (Haskell.Show, Haskell.Read)

Tx.makeLift ''Algorithm

-- The different algorithms implemented in this file. The program iterates the
-- solver over this list of algortihms.

allAlgorithms :: [Labeler]
allAlgorithms = [bt, bm, bjbt, bjbt', fc]

lookupAlgorithm :: Algorithm -> Labeler
lookupAlgorithm Bt    = bt
lookupAlgorithm Bm    = bm
lookupAlgorithm Bjbt1 = bjbt
lookupAlgorithm Bjbt2 = bjbt'  -- bjbt' problematic on command line
lookupAlgorithm Fc    = fc
{-# INLINABLE lookupAlgorithm #-}

nqueens :: Integer -> Labeler -> [State]
nqueens n algorithm = (search algorithm (queens n))
{-# INLINABLE nqueens #-}

-- % Haskell entry point for testing
runQueens :: Integer -> Algorithm -> [State]
runQueens n alg = nqueens n (lookupAlgorithm alg)
{-# INLINABLE runQueens #-}

-- % Compile a Plutus Core term which runs nqueens on given arguments
mkQueensCode :: Integer -> Algorithm -> Tx.CompiledCode [State]
mkQueensCode sz alg =
              $$(Tx.compile [|| runQueens ||])
              `Tx.unsafeApplyCode` Tx.liftCodeDef sz
              `Tx.unsafeApplyCode` Tx.liftCodeDef alg

mkQueensTerm :: Integer -> Algorithm -> Term
mkQueensTerm sz alg = compiledCodeToTerm $ mkQueensCode sz alg

main2 :: Haskell.IO ()  -- Haskell version
main2 = do
  args <- getArgs
  case args of
    [] -> Haskell.putStrLn "Integer parameter expected"
    arg:_ -> do
              let n = Haskell.read arg :: Integer
                  try algorithm = Haskell.print (nqueens n algorithm)
              forM_ [1..240::Integer] $ const $ do
                Haskell.sequence_ (map try allAlgorithms)

-- % Only for textual output of PLC scripts
unindent :: PLC.Doc ann -> [Haskell.String]
unindent d = map (dropWhile isSpace) $ (Haskell.lines . Haskell.show $ d)


-----------------------------------------------------------
-- % Various standard things reimplemented for Plutus
-----------------------------------------------------------

-- % Replacement for `iterate`, which generates an infinite list
iterateN :: Integer -> (a -> a) -> a -> [a]
iterateN k f x =
    if k == 0 then []
    else x : iterateN (k-1) f (f x)
{-# INLINABLE iterateN #-}

-- % Replacement for [a..b]
interval :: Integer -> Integer -> [Integer]
interval a b =
    if a > b then []
    else a : (interval (a+1) b)
{-# INLINABLE interval #-}

abs :: Integer -> Integer
abs n = if n<0 then 0-n else n
{-# INLINABLE abs #-}

-- % Things needed for `union`

deleteBy :: (a -> a -> Bool) -> a -> [a] -> [a]
deleteBy _  _ []     = []
deleteBy eq x (y:ys) = if x `eq` y then ys else y : deleteBy eq x ys
{-# INLINABLE deleteBy #-}

unionBy :: (a -> a -> Bool) -> [a] -> [a] -> [a]
unionBy eq xs ys =  xs ++ foldl (flip (deleteBy eq)) (List.nubBy eq ys) xs
{-# INLINABLE unionBy #-}

union :: (Eq a) => [a] -> [a] -> [a]
union                   = unionBy (==)
{-# INLINABLE union #-}

-- % Stolen from Data.List
sortBy :: (a -> a -> Ordering) -> [a] -> [a]
sortBy cmp = mergeAll . sequences
  where
    sequences (a:b:xs)
      | (a `cmp` b) == GT = descending b [a]  xs
      | otherwise       = ascending  b (a:) xs
    sequences xs = [xs]

    descending a as (b:bs)
      | (a `cmp` b) == GT = descending b (a:as) bs
    descending a as bs  = (a:as): sequences bs

    ascending a as (b:bs)
      | (a `cmp` b) /= GT = ascending b (\ys -> as (a:ys)) bs
    ascending a as bs   = case as [a]  -- Original used let !x = ...
                          of x -> x : sequences bs

    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs (a:b:xs) = case merge a b -- Original used let !x = ...
                          of x ->  x : mergePairs xs
    mergePairs xs       = xs

    merge as@(a:as') bs@(b:bs')
      | a `cmp` b == GT = b:merge as  bs'
      | otherwise       = a:merge as' bs
    merge [] bs         = bs
    merge as []         = as
{-# INLINABLE sortBy #-}


-----------------------------
-- Figure 1. CSPs in Haskell.
-----------------------------

type Var = Integer
type Value = Integer

data Assign = Var := Value
    deriving stock (Haskell.Show, Haskell.Eq, Haskell.Ord, Generic)
    deriving anyclass (NFData)
instance TxPrelude.Eq Assign
    where (a := b) == (a' := b') = a==a' && b==b'
instance TxPrelude.Ord Assign
    where (a := b) < (a' := b') = (a<a') || (a==a' && b < b')

type Relation = Assign -> Assign -> Bool

data CSP = CSP { vars, vals :: Integer, rel :: Relation }

type State = [Assign]

level :: Assign -> Var
level (var := val) = var
{-# INLINABLE level #-}

value :: Assign -> Value
value (var := val) = val
{-# INLINABLE value #-}

maxLevel :: State -> Var
maxLevel []               = 0
maxLevel ((var := val):_) = var
{-# INLINABLE maxLevel #-}

complete :: CSP -> State -> Bool
complete CSP{vars=vars} s = maxLevel s == vars
{-# INLINABLE complete #-}

generate :: CSP -> [State]
generate CSP{vals=vals,vars=vars} = g vars
  where g 0   = [[]]
        g var = [ (var := val):st | val <- interval 1 vals, st <- g (var-1) ]
{-# INLINABLE generate #-}

inconsistencies :: CSP -> State -> [(Var,Var)]
inconsistencies CSP{rel=rel} as =
  [ (level a, level b) | a <- as, b <- reverse as, a > b, not (rel a b) ]
{-# INLINABLE inconsistencies #-}

consistent :: CSP -> State -> Bool
consistent csp = null . (inconsistencies csp)
{-# INLINABLE consistent #-}

test :: CSP -> [State] -> [State]
test csp = filter (consistent csp)
{-# INLINABLE test #-}

solver :: CSP -> [State]
solver csp  = test csp candidates
  where candidates = generate csp
{-# INLINABLE solver #-}

queens :: Integer -> CSP
queens n = CSP {vars = n, vals = n, rel = safe}
  where safe (i := m) (j := n) = (m /= n) && abs (i - j) /= abs (m - n)
{-# INLINABLE queens #-}

-------------------------------
-- Figure 2.  Trees in Haskell.
-------------------------------

data Tree a = Node a [Tree a]

label :: Tree a -> a
label (Node lab _) = lab

type Transform a b = Tree a -> Tree b

mapTree  :: (a -> b) -> Transform a b
mapTree f (Node a cs) = Node (f a) (map (mapTree f) cs)
{-# INLINABLE mapTree  #-}

foldTree :: (a -> [b] -> b) -> Tree a -> b
foldTree f (Node a cs) = f a (map (foldTree f) cs)
{-# INLINABLE foldTree #-}

filterTree :: (a -> Bool) -> Transform a a
filterTree p = foldTree f
  where f a cs = Node a (filter (p . label) cs)
{-# INLINABLE filterTree #-}

prune :: (a -> Bool) -> Transform a a
prune p = filterTree (not . p)
{-# INLINABLE prune #-}

leaves :: Tree a -> [a]
leaves (Node leaf []) = [leaf]
leaves (Node _ cs)    = concat (map leaves cs)
{-# INLINABLE leaves #-}

initTree :: (a -> [a]) -> a -> Tree a
initTree f a = Node a (map (initTree f) (f a))
{-# INLINABLE initTree #-}

--------------------------------------------------
-- Figure 3.  Simple backtracking solver for CSPs.
--------------------------------------------------

mkTree :: CSP -> Tree State
mkTree CSP{vars=vars,vals=vals} = initTree next []
        -- Removed [1..vals]
  where next ss = [ ((maxLevel ss + 1) := j):ss | maxLevel ss < vars, j <- vallist ]
        vallist = interval 1 vals
{-# INLINABLE mkTree #-}

earliestInconsistency :: CSP -> State -> Maybe (Var,Var)
earliestInconsistency CSP{rel=rel} [] = Nothing
earliestInconsistency CSP{rel=rel} (a:as) =
        case filter (not . rel a) (reverse as) of
          []    -> Nothing
          (b:_) -> Just (level a, level b)
{-# INLINABLE earliestInconsistency #-}

labelInconsistencies :: CSP -> Transform State (State,Maybe (Var,Var))
labelInconsistencies csp = mapTree f
    where f s = (s,earliestInconsistency csp s)
{-# INLINABLE labelInconsistencies #-}

btsolver0 :: CSP -> [State]
btsolver0 csp =
  (filter (complete csp) . leaves . (mapTree fst) . prune ((/= Nothing) . snd)
                                            . (labelInconsistencies csp) .  mkTree) csp
{-# INLINABLE btsolver0 #-}

-----------------------------------------------
-- Figure 6. Conflict-directed solving of CSPs.
-----------------------------------------------

data ConflictSet = Known [Var] | Unknown
instance TxPrelude.Eq ConflictSet where
    Known v == Known w = v == w
    Unknown == Unknown = True
    _ == _             = False

knownConflict :: ConflictSet -> Bool
knownConflict (Known (a:as)) = True
knownConflict _              = False
{-# INLINABLE knownConflict #-}

knownSolution :: ConflictSet -> Bool
knownSolution (Known []) = True
knownSolution _          = False
{-# INLINABLE knownSolution #-}

checkComplete :: CSP -> State -> ConflictSet
checkComplete csp s = if complete csp s then Known [] else Unknown
{-# INLINABLE checkComplete #-}

type Labeler = CSP -> Transform State (State, ConflictSet)

search :: Labeler -> CSP -> [State]
search labeler csp =
  (map
    fst .
      filter
        (knownSolution . snd) . leaves . prune (knownConflict . snd) . labeler csp . mkTree)
        csp
{-# INLINABLE search #-}

bt :: Labeler
bt csp = mapTree f
      where f s = (s,
                   case earliestInconsistency csp s of
                     Nothing    -> checkComplete csp s
                     Just (a,b) -> Known [a,b])
{-# INLINABLE bt #-}

btsolver :: CSP -> [State]
btsolver = search bt
{-# INLINABLE btsolver #-}

-------------------------------------
-- Figure 7. Randomization heuristic.
-------------------------------------

hrandom :: Integer -> Transform a a
hrandom seed (Node a cs) =
  Node a (randomList seed' (zipWith hrandom (randoms (length cs) seed') cs))
  where seed' = random seed
{-# INLINABLE hrandom #-}

btr :: Integer -> Labeler
btr seed csp = bt csp . hrandom seed
{-# INLINABLE btr #-}

---------------------------------------------
-- Support for random numbers (not in paper).
---------------------------------------------

random2 :: Integer -> Integer
random2 n = if test > 0 then test else test + 2147483647
  where test = 16807 * lo - 2836 * hi
        hi   = n `Haskell.div` 127773
        lo   = n `Haskell.rem` 127773
{-# INLINABLE random2 #-}

randoms :: Integer -> Integer -> [Integer]
randoms k = iterateN k random2
{-# INLINABLE randoms #-}

random :: Integer -> Integer
random n = (a * n + c) -- mod m
  where a = 994108973
        c = a
{-# INLINABLE random #-}

randomList :: Integer -> [a] -> [a]
randomList i as = map snd (sortBy (\(a,b) (c,d) -> compare a c) (zip (randoms (length as) i) as))
{-# INLINABLE randomList #-}

-------------------------
-- Figure 8. Backmarking.
-------------------------

type Table = [Row]       -- indexed by Var
type Row = [ConflictSet] -- indexed by Value

bm :: Labeler
bm csp = mapTree fst . lookupCache csp . cacheChecks csp (emptyTable csp)
{-# INLINABLE bm #-}

emptyTable :: CSP -> Table
emptyTable CSP{vars=vars,vals=vals} = []:[[Unknown | m <- interval 1 vals] | n <- interval 1 vars]
{-# INLINABLE emptyTable #-}

cacheChecks :: CSP -> Table -> Transform State (State, Table)
cacheChecks csp tbl (Node s cs) =
  Node (s, tbl) (map (cacheChecks csp (fillTable s csp (tail tbl))) cs)
{-# INLINABLE cacheChecks #-}

fillTable :: State -> CSP -> Table -> Table
fillTable [] csp tbl = tbl
fillTable ((var' := val'):as) CSP{vars=vars,vals=vals,rel=rel} tbl =
    zipWith (zipWith f) tbl [[(var,val) | val <- interval 1 vals] | var <- interval (var'+1) vars]
          where f cs (var,val) = if cs == Unknown && not (rel (var' := val') (var := val)) then
                                   Known [var',var]
                                 else cs
{-# INLINABLE fillTable #-}

lookupCache :: CSP -> Transform (State, Table) ((State, ConflictSet), Table)
lookupCache csp t = mapTree f t
  where f ([], tbl)      = (([], Unknown), tbl)
        f (s@(a:_), tbl) = ((s, cs), tbl)
             where cs = if tableEntry == Unknown then checkComplete csp s else tableEntry
                   tableEntry = (head tbl)!!(value a-1)
{-# INLINABLE lookupCache #-}

--------------------------------------------
-- Figure 10. Conflict-directed backjumping.
--------------------------------------------

bjbt :: Labeler
bjbt csp = bj csp . bt csp
{-# INLINABLE bjbt #-}

bjbt' :: Labeler
bjbt' csp = bj' csp . bt csp
{-# INLINABLE bjbt' #-}

bj :: CSP -> Transform (State, ConflictSet) (State, ConflictSet)
bj csp = foldTree f
  where f (a, Known cs) chs = Node (a,Known cs) chs
        f (a, Unknown)  chs = Node (a,Known cs') chs
          where cs' = combine (map label chs) []
{-# INLINABLE bj #-}

combine :: [(State, ConflictSet)] -> [Var] -> [Var]
combine []                 acc = acc
combine ((s, Known cs):css) acc =
  if maxLevel s `notElem` cs then cs else combine css (cs `union` acc)
{-# INLINABLE combine #-}

bj' :: CSP -> Transform (State, ConflictSet) (State, ConflictSet)
bj' csp = foldTree f
  where f (a, Known cs) chs = Node (a,Known cs) chs
        f (a, Unknown) chs = if knownConflict cs' then Node (a,cs') [] else Node (a,cs') chs
           where cs' = Known (combine (map label chs) [])
{-# INLINABLE bj' #-}

-------------------------------
-- Figure 11. Forward checking.
-------------------------------

fc :: Labeler
fc csp = domainWipeOut csp . lookupCache csp . cacheChecks csp (emptyTable csp)
{-# INLINABLE fc #-}

collect :: [ConflictSet] -> [Var]
collect []             = []
collect (Known cs:css) = cs `union` (collect css)
{-# INLINABLE collect #-}

domainWipeOut :: CSP -> Transform ((State, ConflictSet), Table) (State, ConflictSet)
domainWipeOut CSP{vars=vars} t = mapTree f t
  where f ((as, cs), tbl) = (as, cs')
          where wipedDomains = ([vs | vs <- tbl, all (knownConflict) vs])
                cs' = if null wipedDomains then cs else Known (collect (head wipedDomains))
{-# INLINABLE domainWipeOut #-}

Tx.makeLift ''Assign
