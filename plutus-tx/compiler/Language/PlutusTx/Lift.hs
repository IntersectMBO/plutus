{-# LANGUAGE FlexibleContexts #-}
module Language.PlutusTx.Lift (
    makeLift,
    safeLift,
    safeLiftProgram,
    safeLiftCode,
    safeConstCode,
    lift,
    liftProgram,
    liftCode,
    constCode,
    typeCheckAgainst,
    typeCode) where

import           Language.PlutusTx.Code
import           Language.PlutusTx.Lift.Class                  (makeLift)
import qualified Language.PlutusTx.Lift.Class                  as Lift
import           Language.PlutusTx.Lift.Instances              ()

import           Language.PlutusIR
import           Language.PlutusIR.Compiler
import           Language.PlutusIR.Compiler.Definitions
import qualified Language.PlutusIR.MkPir                       as PIR

import qualified Language.PlutusCore                           as PLC
import qualified Language.PlutusCore.Constant.Dynamic          as PLC
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.StdLib.Data.Function      as PLC
import qualified Language.PlutusCore.StdLib.Meta.Data.Function as PLC

import           Control.Exception
import           Control.Monad.Except                          hiding (lift)
import           Control.Monad.Reader                          hiding (lift)

import           Data.Functor                                  (void)
import           Data.Proxy

-- | Get a Plutus Core term corresponding to the given value.
safeLift :: (Lift.Lift a, AsError e (Provenance ()), MonadError e m, MonadQuote m) => a -> m (PLC.Term TyName Name ())
safeLift x = do
    lifted <- liftQuote $ runDefT () $ Lift.lift x
    compiled <- flip runReaderT defaultCompilationCtx $ compileTerm lifted
    pure $ void compiled

-- | Get a Plutus Core program corresponding to the given value.
safeLiftProgram :: (Lift.Lift a, AsError e (Provenance ()), MonadError e m, MonadQuote m) => a -> m (PLC.Program TyName Name ())
safeLiftProgram x = PLC.Program () (PLC.defaultVersion ()) <$> safeLift x

safeLiftCode :: (Lift.Lift a, AsError e (Provenance ()), MonadError e m, MonadQuote m) => a -> m (CompiledCode a)
safeLiftCode x = DeserializedCode <$> safeLiftProgram x <*> pure Nothing

safeConstCode
    :: (Lift.Typeable a, AsError e (Provenance ()), MonadError e m, MonadQuote m)
    => Proxy a
    -> CompiledCode b
    -> m (CompiledCode (a -> b))
safeConstCode proxy code = do
    newTerm <- liftQuote $ runDefT () $ do
        term <- Lift.lift code
        ty <- Lift.typeRep proxy
        pure $ TyInst () (PLC.constPartial term) ty
    compiled <- flip runReaderT defaultCompilationCtx $ compileTerm newTerm
    pure $ DeserializedCode (PLC.Program () (PLC.defaultVersion ()) (void compiled)) Nothing

unsafely :: ExceptT (Error (Provenance ())) Quote a -> a
unsafely ma = runQuote $ do
    run <- runExceptT ma
    case run of
        Left e  -> throw e
        Right t -> pure t

-- | Get a Plutus Core term corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
lift :: Lift.Lift a => a -> PLC.Term TyName Name ()
lift a = unsafely $ safeLift a

-- | Get a Plutus Core program corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
liftProgram :: Lift.Lift a => a -> PLC.Program TyName Name ()
liftProgram x = PLC.Program () (PLC.defaultVersion ()) $ lift x

-- | Get a Plutus Core program corresponding to the given value as a 'CompiledCode', throwing any errors that occur as exceptions and ignoring fresh names.
liftCode :: Lift.Lift a => a -> CompiledCode a
liftCode x = unsafely $ safeLiftCode x

-- | Creates a program that ignores an argument of the given type and returns the program given.
constCode
    :: Lift.Typeable a
    => Proxy a
    -> CompiledCode b
    -> CompiledCode (a -> b)
constCode proxy b = unsafely $ safeConstCode proxy b

{- Note [Checking the type of a term with Typeable]
Checking the type of a term should be simple, right? We can just use 'checkType', easy peasy.

Not so fast - Typeable gives us a PLC type corresponding to a Haskell type, but *inside the PIR Def monad*.
This is because it might have type definitions that it refers to, and we use the standard machinery for that.
We can only discharge the Def monad into a *term*, because of course we have to turn those definitions into
let bindings.

So we don't have access to the type directly, annoyingly. Instead, we can construct a term that typechecks
iff the original term has the given type. We opt for `(\x : <the type> -> x) term`.
-}

-- | Check that PLC term has the given type.
typeCheckAgainst
    :: forall e a m . (Lift.Typeable a, PLC.AsTypeError e (Provenance ()), AsError e (Provenance ()), MonadError e m, MonadQuote m)
    => Proxy a
    -> PLC.Term PLC.TyName PLC.Name ()
    -> m ()
typeCheckAgainst p plcTerm = do
    -- See Note [Checking the type of a term with Typeable]
    term <- PIR.embed <$> PLC.rename plcTerm
    -- We need to run Def *before* applying to the term, otherwise we may refer to abstract
    -- types and we won't match up with the term.
    idFun <- liftQuote $ runDefT () $ do
        ty <- Lift.typeRep p
        pure $ TyInst () PLC.idFun ty
    let applied = Apply () idFun term
    compiled <- flip runReaderT defaultCompilationCtx $ compileTerm applied
    types <- PLC.getStringBuiltinTypes NoProvenance
    void $ PLC.inferType (PLC.defOffChainConfig { PLC._tccDynamicBuiltinNameTypes = types }) compiled

-- | Try to interpret a PLC program as a 'CompiledCode' of the given type. Returns successfully iff the program has the right type.
typeCode
    :: forall e a m . (Lift.Typeable a, PLC.AsTypeError e (Provenance ()), AsError e (Provenance ()), MonadError e m, MonadQuote m)
    => Proxy a
    -> PLC.Program PLC.TyName PLC.Name ()
    -> m (CompiledCode a)
typeCode p prog@(PLC.Program _ _ term) = do
    _ <- typeCheckAgainst p term
    pure $ DeserializedCode prog Nothing
