{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module PlutusBenchmark.Casing where

import Control.Monad.Except
import Data.Either
import PlutusBenchmark.Common (Term)
import PlutusCore (DefaultUni (..), SomeTypeIn (..), Type (..), freshName, runQuote)
import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.MkPlc
import UntypedPlutusCore qualified as UPLC

debruijnTermUnsafe :: UPLC.Term UPLC.Name uni fun ann
                    -> UPLC.Term UPLC.NamedDeBruijn uni fun ann
debruijnTermUnsafe =
    fromRight (Prelude.error "debruijnTermUnsafe") . runExcept @UPLC.FreeVariableError . UPLC.deBruijnTerm

nonMatchingBranch :: TermLike term tyname name UPLC.DefaultUni UPLC.DefaultFun => term ()
nonMatchingBranch = mkConstant @Integer () (-1)

-- Note that we don't need to generate casings for the none maching branches because
-- only matching branches get executed.
-- | Generate a term that does a lot of casing on boolean
casingBool :: Integer -> Term
casingBool 0 = mkConstant @Integer () 42
casingBool i
  | i `mod` 2 == 0 =
    kase ()
      (TyBuiltin () (SomeTypeIn DefaultUniInteger))
      (mkConstant @Bool () False)
      [casingBool (i-1), nonMatchingBranch]
  | otherwise =
     kase ()
       (TyBuiltin () (SomeTypeIn DefaultUniInteger))
       (mkConstant @Bool () True)
       [nonMatchingBranch, casingBool (i-1)]

-- | Generate a term that does a lot of boolean casing with single branch.
casingBoolOneBranch :: Integer -> Term
casingBoolOneBranch 0 = mkConstant @Integer () 42
casingBoolOneBranch i =
  kase ()
    (TyBuiltin () (SomeTypeIn DefaultUniInteger))
    (mkConstant @Bool () False)
    [casingBoolOneBranch (i-1)]

-- | Generate a term that does a lot of integer casing.
casingInteger :: Integer -> Term
casingInteger 0 = mkConstant @Integer () 42
casingInteger i =
  let
    numBranches = 5
    -- 5 is arbitrary, this indicates the number of branches to have on each casing
    currentI = i `mod` numBranches
  in kase ()
       (TyBuiltin () (SomeTypeIn DefaultUniInteger))
       (mkConstant @Integer () currentI)
       (replicate (fromIntegral currentI) nonMatchingBranch
        <> [casingInteger (i-1)]
        <> replicate (fromIntegral $ numBranches - 1 - currentI) nonMatchingBranch
       )

-- | UPLC 'cons' parameterized in Haskell.
listConsHandler
  :: TermLike term tyname UPLC.Name UPLC.DefaultUni UPLC.DefaultFun
  => (term () -> term () -> term ()) -> term ()
listConsHandler f = runQuote $ do
  x <- freshName "x"
  xs <- freshName "xs"
  pure $
    lamAbs () x (TyBuiltin () (SomeTypeIn DefaultUniInteger)) $
      lamAbs () xs (TyBuiltin () (SomeTypeIn $ DefaultUniApply DefaultUniProtoList DefaultUniInteger)) $
      f (var () x) (var () xs)

-- | Generate a term that does a lot of casing on list.
casingList :: Integer -> Term
casingList i = debruijnTermUnsafe $ go i arg
  where
    arg = mkConstant @[Integer] () $ replicate (fromIntegral i) 42
    go 0 t = t
    go n t =
      kase ()
        (TyBuiltin () (SomeTypeIn $ DefaultUniApply DefaultUniProtoList DefaultUniInteger))
        t
        [listConsHandler (\_x xs -> go (n-1) xs), nonMatchingBranch]

-- | Generate a term that does a lot of casing on list with one branch.
casingListOneBranch :: Integer -> Term
casingListOneBranch i = debruijnTermUnsafe $ go i arg
  where
    arg =
      mkConstant @[Integer] () $
        replicate (fromIntegral i) 42

    go 0 t = t
    go n t =
      kase ()
        (TyBuiltin () (SomeTypeIn $ DefaultUniApply DefaultUniProtoList DefaultUniInteger))
        t
        [listConsHandler (\_x xs -> go (n-1) xs)]

-- | Generate a term that does a lot of casing on pairs using 'FstPair' and 'SndPair'. It
-- will case first and then second term on each iteration.
pairFstSnd :: Integer -> Term
pairFstSnd i =
  debruijnTermUnsafe $
    foldr (const comp) (mkConstant @Integer () 0) [1..i]
  where
    intTy = PLC.mkTyBuiltin @_ @Integer ()
    pairVal = mkConstant @(Integer, Integer) () (42, 42)
    comp t = runQuote $ do
      x <- freshName "x"
      y <- freshName "y"
      pure $
        apply ()
          (apply ()
            (lamAbs () x intTy $
             lamAbs () y intTy $
             t)
            (apply () (tyInst () (tyInst () (builtin () PLC.FstPair) intTy) intTy) pairVal))
        (apply () (tyInst () (tyInst () (builtin () PLC.SndPair) intTy) intTy) pairVal)

-- | Generate a term that does a lot of casing on pairs. It will case first and then
-- second term on each iteration.
pairCasing :: Integer -> Term
pairCasing i =
  debruijnTermUnsafe $
    foldr (const comp) (mkConstant @Integer () 0) [1..i]
  where
    intTy = PLC.mkTyBuiltin @_ @Integer ()
    pairVal = mkConstant @(Integer, Integer) () (42, 42)
    comp t = runQuote $ do
      x <- freshName "x"
      y <- freshName "y"
      fstL <- freshName "fstL"
      fstR <- freshName "fstR"
      sndL <- freshName "sndL"
      sndR <- freshName "sndR"
      pure $
        apply ()
          (apply ()
            (lamAbs () x intTy $
             lamAbs () y intTy $
             t)
            (kase () intTy pairVal [lamAbs () sndL intTy $ lamAbs () sndR intTy $ var () sndL]))
        (kase () intTy pairVal [lamAbs () fstL intTy $ lamAbs () fstR intTy $ var () fstR])

-- | Generate a term that does a lot of casing on unit using 'ChooseUnit'.
chooseUnit :: Integer -> Term
chooseUnit i =
  debruijnTermUnsafe $
    foldr (const comp) (mkConstant @Integer () 0) [1..i]
  where
    intTy = PLC.mkTyBuiltin @_ @Integer ()
    unitVal = mkConstant () ()
    comp t =
      apply ()
        (apply () (tyInst () (builtin () PLC.ChooseUnit) intTy) unitVal)
      t

-- | Generate a term that does a lot of casing on unit.
unitCasing :: Integer -> Term
unitCasing i =
  debruijnTermUnsafe $
    foldr (const comp) (mkConstant @Integer () 0) [1..i]
  where
    intTy = PLC.mkTyBuiltin @_ @Integer ()
    unitVal = mkConstant () ()
    comp t =
      kase () intTy unitVal [t]

-- | Generate a term that does a lot of casing on head of list using 'HeadList'
headList :: Integer -> Term
headList i =
  debruijnTermUnsafe $
    foldr (const comp) (mkConstant @Integer () 0) [1..i]
  where
    intTy = PLC.mkTyBuiltin @_ @Integer ()
    listVal = mkConstant @[Integer] () [1, 2, 3]
    comp t = runQuote $ do
      x <- freshName "x"
      pure $
        apply ()
          (lamAbs () x intTy t)
        (apply () (tyInst () (builtin () PLC.HeadList) intTy) listVal)

-- | Generate a term that does a lot of casing on head of list.
headListCasing :: Integer -> Term
headListCasing i =
  debruijnTermUnsafe $
    foldr (const comp) (mkConstant @Integer () 0) [1..i]
  where
    intTy = PLC.mkTyBuiltin @_ @Integer ()
    intListTy = PLC.mkTyBuiltin @_ @[Integer] ()
    listVal = mkConstant @[Integer] () [1, 2, 3]
    comp t = runQuote $ do
      x <- freshName "x"
      y <- freshName "y"
      ys <- freshName "ys"
      pure $
        apply ()
          (lamAbs () x intTy t)
        (kase () intTy listVal [lamAbs () y intTy $ lamAbs () ys intListTy $ var () y])
