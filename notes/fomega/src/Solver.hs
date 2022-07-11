-- editorconfig-checker-disable-file
module Solver where

import AlgTypes
import Data.Set qualified as S

-----------------------------------------------------
-- Identifying Systems of Mutually Recursive Types --
-----------------------------------------------------

-- 'directReferences sig d'  is the set of declarations directly referred to by name in the definition of d.
directReferences :: AlgSignature -> Decl AlgType -> AlgSignature
directReferences sig (Decl _ t) = S.filter referredTo sig
  where
  referredTo :: Decl AlgType -> Bool
  referredTo (Decl name _) = S.member name (free t)

-- If aDb means "a directly references b", then this is like the transitive closure.
-- i.e., aRb in case a references b. Then aDb => aRb, and (aRb & bRC) => aRc.
references :: AlgSignature -> Decl AlgType -> AlgSignature
references sig d = fix (references' sig) (S.singleton d)
  where
  references' :: AlgSignature -> AlgSignature -> AlgSignature
  references' sig rs = S.foldr S.union
                               rs
                               (S.map (\d -> directReferences sig d) rs)

-- attempt to construct a fixed point of f by repeatedly applying it to x.
-- needless to say, this is exceedingly partial, by we'll use it responsibly.
fix :: (Eq a) => (a -> a) -> a -> a
fix f x = if f x == x then x else fix f (f x)

-- now, two types in a signature are mutually recursive in case they reference one another.
mutuallyRecursive :: AlgSignature -> Decl AlgType -> Decl AlgType -> Bool
mutuallyRecursive sig d1 d2 = S.member d1 (references sig d2) && S.member d2 (references sig d1)

-- splitting a signature up into its component mutually recursive bits.
partitionMRec :: AlgSignature -> [[Decl AlgType]]
partitionMRec sig =
  if S.null sig then []
    else (S.toList mrec) : (partitionMRec rest)
  where
  decl = S.elemAt 0 sig
  (mrec,rest) = S.partition (\x -> mutuallyRecursive sig decl x) sig

-------------------------------------------------
-- Solving Systems of Mutually Recursive Types --
-------------------------------------------------

-- the type of fixed point equations.
type FPEquation = (String,[AlgType] -> AlgType)

--  for t1,...,tn (ti = Ti) -> (i , [t1,...,tn] \mapsto Ti)
fpEquations :: [Decl AlgType] -> [FPEquation]
fpEquations  ds = let allDeclNames :: [String]
                      allDeclNames = map (\(Decl x _) -> x) ds
                  in
                      map (fpEquation allDeclNames) ds

fpEquation :: [String] -> Decl AlgType -> FPEquation
fpEquation names (Decl x t) =
  (x , (\subs -> foldr (\(x,y) a -> sub y x a) t (zip names subs)))


-- The symmetic form of the Bekic identity.
solveTwo :: (FPEquation,FPEquation) -> (Decl AlgType,Decl AlgType)
solveTwo ((t1,bigT1),(t2,bigT2)) = (d1,d2)
  where
  d1 :: Decl AlgType
  d1 = Decl t1
            (Mu t1
                (bigT1 [(Var t1)
                       ,(Mu t2
                            (bigT2 [(Var t1)
                                   ,(Var t2)]))]))
  d2 :: Decl AlgType
  d2 = Decl t2
            (Mu t2
                (bigT2 [(Mu t1
                            (bigT1 [(Var t1)
                                   ,(Var t2)]))
                       ,(Var t2)]))

-- N-ary version of the symmetric form of the Bekic identity. (This is tricky!)
solve :: [FPEquation] -> [Decl AlgType]
solve []  = []
solve [(t,bigT)] = [Decl t (Mu t (bigT [(Var t)]))]
solve [e1,e2] = (\(a,b) -> [a,b]) (solveTwo (e1,e2))
solve es = map (uncurry solveOne) (zip [0..] es)
  where
  solveOne :: Int -> FPEquation -> Decl AlgType
  solveOne i (ti,bigTi) =
    let subs :: [AlgType]
        subs = map (\(Decl _ x) -> x)
                   (solve (map (fixArg i (Var ti))
                               (exclude ti)))
        bigTi' :: [AlgType] -> AlgType -- also fix ith arg of bigTi to be (Var ti)
        bigTi' = snd (fixArg i (Var ti) (ti,bigTi))
    in
      Decl ti (Mu ti (bigTi' subs))

  exclude :: String -> [FPEquation]
  exclude ti = filter (\(x,xT) -> x /= ti) es

-- fix the value of the nth argument of the term function in a fixed point equation
fixArg :: Int -> AlgType -> FPEquation -> FPEquation
fixArg n x (t,bigT) = ( t
                      , bigT . (\tys -> (take n tys) ++ (x:(drop n tys))))

-------------------------
-- Putting It Together --
-------------------------

demutualize :: AlgSignature -> AlgSignature
demutualize sig = algSignature (concatMap (solve . fpEquations) (partitionMRec sig))

