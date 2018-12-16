{-# LANGUAGE FlexibleContexts #-}
-- Note that we don't export the Lift class itself, most consumers shouldn't need that.
module Language.PlutusTx.Lift (
    makeLift,
    lift,
    liftProgram,
    unsafeLift,
    unsafeLiftProgram) where

import           Language.PlutusTx.Lift.Class           (makeLift)
import qualified Language.PlutusTx.Lift.Class           as Lift
import           Language.PlutusTx.Lift.Instances       ()

import           Language.PlutusIR
import           Language.PlutusIR.Compiler
import           Language.PlutusIR.Compiler.Definitions

import qualified Language.PlutusCore                    as PLC
import           Language.PlutusCore.Quote

import           Control.Exception
import           Control.Monad.Except                   hiding (lift)
import           Control.Monad.Reader                   hiding (lift)

-- | Get a Plutus Core term corresponding to the given value.
lift :: (Lift.Lift a, AsError e (Provenance ()), MonadError e m, MonadQuote m) => a -> m (PLC.Term TyName Name ())
lift x = do
    lifted <- runDefT () $ Lift.lift x
    compiled <- flip runReaderT NoProvenance $ compileTerm lifted
    pure $ void compiled

-- | Get a Plutus Core program corresponding to the given value.
liftProgram :: (Lift.Lift a, AsError e (Provenance ()), MonadError e m, MonadQuote m) => a -> m (PLC.Program TyName Name ())
liftProgram x = PLC.Program () (PLC.defaultVersion ()) <$> lift x

-- | Get a Plutus Core term corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
unsafeLift :: Lift.Lift a => a -> PLC.Term TyName Name ()
unsafeLift a = runQuote $ do
    run <- runExceptT $ lift a
    case run of
        Left (e::Error (Provenance ())) -> throw e
        Right t                         -> pure t

-- | Get a Plutus Core program corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
unsafeLiftProgram :: Lift.Lift a => a -> PLC.Program TyName Name ()
unsafeLiftProgram x = PLC.Program () (PLC.defaultVersion ()) $ unsafeLift x
