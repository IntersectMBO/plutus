{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module PlutusBenchmark.Casing where

import Control.Monad.Except
import Data.Either
import PlutusBenchmark.Common (Term)
import PlutusCore (DefaultUni (..), SomeTypeIn (..), Type (..), freshName, runQuote, someValueOf)
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
