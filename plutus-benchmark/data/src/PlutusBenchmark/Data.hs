{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module PlutusBenchmark.Data where

import Control.Monad.Except
import Data.ByteString (ByteString)
import Data.Either
import PlutusBenchmark.Common (Term)
import PlutusCore (DefaultUni (..), SomeTypeIn (..), Type (..), freshName, runQuote)
import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Data qualified as PLC
import PlutusCore.MkPlc
import UntypedPlutusCore qualified as UPLC

debruijnTermUnsafe :: UPLC.Term UPLC.Name UPLC.DefaultUni UPLC.DefaultFun ann
                    -> UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ann
debruijnTermUnsafe =
    fromRight (Prelude.error "debruijnTermUnsafe") . runExcept @UPLC.FreeVariableError . UPLC.deBruijnTerm

conDeconI :: Integer -> Term
conDeconI i =
  debruijnTermUnsafe $
    foldr (const comp) (mkConstant @Integer () 0) [1..i]
  where
    intTy = PLC.mkTyBuiltin @_ @Integer ()
    comp t = runQuote $ do
      x <- freshName "x"
      pure $
        apply ()
          (lamAbs () x intTy t)
          (apply ()
            (builtin () PLC.UnIData)
            (apply () (builtin () PLC.IData) (mkConstant @Integer () 42)))

conI :: Integer -> Term
conI i =
  debruijnTermUnsafe $
    foldr (const comp) (mkConstant @Integer () 0) [1..i]
  where
    intTy = PLC.mkTyBuiltin @_ @Integer ()
    comp t = runQuote $ do
      x <- freshName "x"
      pure $
        apply ()
          (lamAbs () x intTy t)
          (apply () (builtin () PLC.IData) (mkConstant @Integer () 42))

conDeconB :: ByteString -> Integer -> Term
conDeconB bs i =
  debruijnTermUnsafe $
    foldr (const comp) (mkConstant @Integer () 0) [1..i]
  where
    intTy = PLC.mkTyBuiltin @_ @Integer ()
    comp t = runQuote $ do
      x <- freshName "x"
      pure $
        apply ()
          (lamAbs () x intTy t)
          (apply ()
            (builtin () PLC.UnBData)
            (apply () (builtin () PLC.BData) (mkConstant @ByteString () bs)))

conB :: ByteString -> Integer -> Term
conB bs i =
  debruijnTermUnsafe $
    foldr (const comp) (mkConstant @Integer () 0) [1..i]
  where
    intTy = PLC.mkTyBuiltin @_ @Integer ()
    comp t = runQuote $ do
      x <- freshName "x"
      pure $
        apply ()
          (lamAbs () x intTy t)
          (apply () (builtin () PLC.BData) (mkConstant @ByteString () bs))

constrDataWithRelease :: Integer -> Term
constrDataWithRelease i =
  debruijnTermUnsafe $ comp (i-1) d
  where
    chuckSize = 2000
    dataTy = PLC.mkTyBuiltin @_ @PLC.Data ()
    nilData = mkConstant @([PLC.Data]) () []
    d = mkConstant @PLC.Data () (PLC.I 42)
    work t =
      (apply ()
        (apply ()
          (builtin () PLC.ConstrData)
          (mkConstant @Integer () 1))
        (apply () (apply () (tyInst () (builtin () PLC.MkCons) dataTy) t) nilData))
    comp 0 t = work t
    comp n t
      | n `mod` chuckSize == 0 = runQuote $ do
          x <- freshName "x"
          pure $
            apply ()
              (lamAbs () x dataTy (comp (n - 1) d))
              (work t)
      | otherwise = runQuote $ do
          pure $ comp (n - 1) $ work t

constrDataNoRelease :: Integer -> Term
constrDataNoRelease i =
  debruijnTermUnsafe $ comp (i-1) d
  where
    chuckSize = 2000
    dataTy = PLC.mkTyBuiltin @_ @PLC.Data ()
    nilData = mkConstant @([PLC.Data]) () []
    d = mkConstant @PLC.Data () (PLC.I 42)
    work t =
      (apply ()
        (apply ()
          (builtin () PLC.ConstrData)
          (mkConstant @Integer () 1))
        (apply () (apply () (tyInst () (builtin () PLC.MkCons) dataTy) t) nilData))
    comp 0 t = work t
    comp n t
      | n `mod` chuckSize == 0 = runQuote $ do
          x <- freshName "x"
          pure $
            apply ()
              (lamAbs () x dataTy (comp (n - 1) $ work t))
              (mkConstant @() () ())
      | otherwise = runQuote $ do
          pure $ comp (n - 1) $ work t
