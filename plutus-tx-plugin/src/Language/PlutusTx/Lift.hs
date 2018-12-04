{-# LANGUAGE FlexibleContexts #-}
module Language.PlutusTx.Lift (
    module Lift,
    makeLift,
    liftPlc,
    liftPlcProgram,
    unsafeLiftPlc,
    unsafeLiftPlcProgram) where

import           Language.PlutusTx.Lift.Instances       ()
import           Language.PlutusTx.Lift.LiftPir         as Lift

import           Language.PlutusIR
import           Language.PlutusIR.Compiler
import           Language.PlutusIR.Compiler.Definitions

import qualified Language.PlutusCore                    as PLC
import           Language.PlutusCore.Quote

import           Control.Exception
import           Control.Monad.Except
import           Control.Monad.Reader

import qualified Language.Haskell.TH                    as TH

-- | Get a Plutus Core term corresponding to the given value.
liftPlc :: (LiftPir a, AsError e (Provenance ()), MonadError e m, MonadQuote m) => a -> m (PLC.Term TyName Name ())
liftPlc x = do
    lifted <- runDefT () $ Lift.lift x
    compiled <- flip runReaderT NoProvenance $ compileTerm lifted
    pure $ void compiled

-- | Get a Plutus Core program corresponding to the given value.
liftPlcProgram :: (LiftPir a, AsError e (Provenance ()), MonadError e m, MonadQuote m) => a -> m (PLC.Program TyName Name ())
liftPlcProgram x = PLC.Program () (PLC.defaultVersion ()) <$> liftPlc x

-- | Get a Plutus Core term corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
unsafeLiftPlc :: LiftPir a => a -> PLC.Term TyName Name ()
unsafeLiftPlc a = runQuote $ do
    run <- runExceptT $ liftPlc a
    case run of
        Left (e::Error (Provenance ())) -> throw e
        Right t                         -> pure t

-- | Get a Plutus Core program corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
unsafeLiftPlcProgram :: LiftPir a => a -> PLC.Program TyName Name ()
unsafeLiftPlcProgram x = PLC.Program () (PLC.defaultVersion ()) $ unsafeLiftPlc x

-- | Make lift typeclass instances for the given type constructor name.
makeLift :: TH.Name -> TH.Q [TH.Dec]
makeLift = makeLiftPir
