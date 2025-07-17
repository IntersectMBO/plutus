{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module PlutusBenchmark.Casing where

import Control.Monad.Except
import Data.Either
import PlutusBenchmark.Common (Term)
import PlutusCore (DefaultUni (..), SomeTypeIn (..), Type (..), freshName, runQuote, someValueOf)
import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.MkPlc
import UntypedPlutusCore qualified as UPLC

debruijnTermUnsafe :: UPLC.Term UPLC.Name uni fun ann
                    -> UPLC.Term UPLC.NamedDeBruijn uni fun ann
debruijnTermUnsafe =
    fromRight (Prelude.error "debruijnTermUnsafe") . runExcept @UPLC.FreeVariableError . UPLC.deBruijnTerm

nonMatchingBranch :: TermLike term tyname name UPLC.DefaultUni UPLC.DefaultFun => term ()
nonMatchingBranch = constant () $ someValueOf DefaultUniInteger $ -1

-- Note that we don't need to generate casings for the none maching branches because
-- only matching branches get executed.
-- | Generate a term that does a lot of casing on boolean
casingBool :: Integer -> Term
casingBool 0 = constant () $ someValueOf DefaultUniInteger 42
casingBool i
  | i `mod` 2 == 0 =
    kase ()
      (TyBuiltin () (SomeTypeIn DefaultUniInteger))
      (constant () $ someValueOf DefaultUniBool False)
      [casingBool (i-1), nonMatchingBranch]
  | otherwise =
     kase ()
       (TyBuiltin () (SomeTypeIn DefaultUniInteger))
       (constant () $ someValueOf DefaultUniBool True)
       [nonMatchingBranch, casingBool (i-1)]

casingBoolOneBranch :: Integer -> Term
casingBoolOneBranch 0 = constant () $ someValueOf DefaultUniInteger 42
casingBoolOneBranch i =
  kase ()
    (TyBuiltin () (SomeTypeIn DefaultUniInteger))
    (constant () $ someValueOf DefaultUniBool False)
    [casingBoolOneBranch (i-1)]

casingInteger :: Integer -> Term
casingInteger 0 = constant () $ someValueOf DefaultUniInteger 42
casingInteger i =
  let
    numBranches = 5
    -- 5 is arbitrary, this indicates the number of branches to have on each casing
    currentI = i `mod` numBranches
  in kase ()
       (TyBuiltin () (SomeTypeIn DefaultUniInteger))
       (constant () $ someValueOf DefaultUniInteger currentI)
       (replicate (fromIntegral currentI) nonMatchingBranch
        <> [casingInteger (i-1)]
        <> replicate (fromIntegral $ numBranches - 1 - currentI) nonMatchingBranch
       )

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


casingList :: Integer -> Term
casingList i = debruijnTermUnsafe $ go i arg
  where
    arg =
      constant () $
        someValueOf (DefaultUniApply DefaultUniProtoList DefaultUniInteger) $ replicate (fromIntegral i) 42

    go 0 t = t
    go n t =
      kase ()
        (TyBuiltin () (SomeTypeIn $ DefaultUniApply DefaultUniProtoList DefaultUniInteger))
        t
        [nonMatchingBranch, listConsHandler (\_x xs -> go (n-1) xs)]


casingListOneBranch :: Integer -> Term
casingListOneBranch i = debruijnTermUnsafe $ go i arg
  where
    arg =
      constant () $
        someValueOf (DefaultUniApply DefaultUniProtoList DefaultUniInteger) $ replicate (fromIntegral i) 42

    go 0 t = t
    go n t =
      kase ()
        (TyBuiltin () (SomeTypeIn $ DefaultUniApply DefaultUniProtoList DefaultUniInteger))
        t
        [listConsHandler (\_x xs -> go (n-1) xs)]

pairFstSnd :: Integer -> Term
pairFstSnd i =
  debruijnTermUnsafe $
    foldr (const comp) (constant () $ someValueOf DefaultUniInteger 0) [1..i]
  where
    intTy = PLC.mkTyBuiltin @_ @Integer ()
    pairVal =
      constant () $
        someValueOf (PLC.DefaultUniPair DefaultUniInteger DefaultUniInteger) (42, 42)
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

pairCasing :: Integer -> Term
pairCasing i =
  debruijnTermUnsafe $
    foldr (const comp) (constant () $ someValueOf DefaultUniInteger 0) [1..i]
  where
    intTy = PLC.mkTyBuiltin @_ @Integer ()
    pairVal =
      constant () $
        someValueOf (PLC.DefaultUniPair DefaultUniInteger DefaultUniInteger) (42, 42)
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

chooseUnit :: Integer -> Term
chooseUnit i =
  debruijnTermUnsafe $
    foldr (const comp) (constant () $ someValueOf DefaultUniInteger 0) [1..i]
  where
    intTy = PLC.mkTyBuiltin @_ @Integer ()
    unitVal = constant () $ someValueOf PLC.DefaultUniUnit ()
    comp t =
      apply ()
        (apply () (tyInst () (builtin () PLC.ChooseUnit) intTy) unitVal)
      t

unitCasing :: Integer -> Term
unitCasing i =
  debruijnTermUnsafe $
    foldr (const comp) (constant () $ someValueOf DefaultUniInteger 0) [1..i]
  where
    intTy = PLC.mkTyBuiltin @_ @Integer ()
    unitVal = constant () $ someValueOf PLC.DefaultUniUnit ()
    comp t =
      kase () intTy unitVal [t]
