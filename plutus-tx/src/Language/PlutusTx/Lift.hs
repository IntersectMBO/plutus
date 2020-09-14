{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE PartialTypeSignatures    #-}
module Language.PlutusTx.Lift (
    makeLift,
    safeLift,
    safeLiftProgram,
    safeLiftCode,
    safeConstCode,
    lift,
    liftProgram,
    liftProgramDef,
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
import qualified           Language.PlutusIR.Error as PIR
import           Language.PlutusIR.Compiler.Definitions
import qualified Language.PlutusIR                       as PIR
import qualified Language.PlutusIR.MkPir                       as PIR
import Data.Bifunctor

import qualified Language.PlutusCore                           as PLC
import qualified Language.PlutusCore.Constant.Dynamic          as PLC
import           Language.PlutusCore.Pretty                    (PrettyConst)
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.StdLib.Data.Function      as PLC
import qualified Language.PlutusCore.StdLib.Meta.Data.Function as PLC

import           Codec.Serialise
import           Control.Exception
import           Control.Monad.Except                          hiding (lift)
import           Control.Monad.Reader                          hiding (lift)
import Control.Lens hiding (lifted)

import           Data.Proxy
import qualified Data.Typeable                                 as GHC

type Throwable uni = (PLC.GShow uni, PLC.GEq uni, PLC.DefaultUni PLC.<: uni, PLC.Closed uni, uni `PLC.Everywhere` PrettyConst, GHC.Typeable uni)

-- | Get a Plutus Core term corresponding to the given value.
safeLift
    :: (Lift.Lift uni a
       , PIR.AsTypeError e (PIR.Term TyName Name uni ()) uni (Provenance ()), PLC.GShow uni, PLC.GEq uni
       , PIR.AsTypeErrorExt e uni (Provenance ())
       , PLC.DefaultUni PLC.<: uni
       , AsError e uni (Provenance ()), MonadError e m, MonadQuote m
       )
    => a -> m (PLC.Term TyName Name uni ())
safeLift x = do
    lifted <- liftQuote $ runDefT () $ Lift.lift x
    -- note: we typecheck&compile the plutus-tx term inside an empty builtin context (PLC.defConfig)
    compiled <- flip runReaderT defaultCompilationCtx $ compileTerm True lifted
    pure $ void compiled

-- | Get a Plutus Core program corresponding to the given value.
safeLiftProgram
    :: (Lift.Lift uni a
       , PIR.AsTypeError e (PIR.Term TyName Name uni ()) uni (Provenance ()), PLC.GShow uni, PLC.GEq uni
       , PIR.AsTypeErrorExt e uni (Provenance ())
       , PLC.DefaultUni PLC.<: uni
       , AsError e uni (Provenance ()), MonadError e m, MonadQuote m)
    => a -> m (PLC.Program TyName Name uni ())
safeLiftProgram x = PLC.Program () (PLC.defaultVersion ()) <$> safeLift x

safeLiftCode
    :: (Lift.Lift uni a
       , PIR.AsTypeError e (PIR.Term TyName Name uni ()) uni (Provenance ()), PLC.GShow uni, PLC.GEq uni       , PLC.DefaultUni PLC.<: uni
       , PIR.AsTypeErrorExt e uni (Provenance ())
       , AsError e uni (Provenance ()), MonadError e m, MonadQuote m)
    => a -> m (CompiledCode uni a)
safeLiftCode x = DeserializedCode <$> safeLiftProgram x <*> pure Nothing

safeConstCode
    :: ( Lift.Typeable uni a, AsError e uni (Provenance ()), MonadError e m, MonadQuote m
       , PIR.AsTypeError e (PIR.Term TyName Name uni ()) uni (Provenance ()), PLC.GShow uni, PLC.GEq uni
       , PIR.AsTypeErrorExt e uni (Provenance ())
       , PLC.DefaultUni PLC.<: uni
       , PLC.Closed uni, uni `PLC.Everywhere` Serialise
       )
    => Proxy a
    -> CompiledCode uni b
    -> m (CompiledCode uni (a -> b))
safeConstCode proxy code = do
    newTerm <- liftQuote $ runDefT () $ do
        term <- Lift.lift code
        ty <- Lift.typeRep proxy
        pure $ TyInst () (PLC.constPartial term) ty
    -- FIXME: we need to pass the real dynamic builtin tcconfig map in compileterm
    compiled <- flip runReaderT defaultCompilationCtx $ compileTerm True newTerm
    pure $ DeserializedCode (PLC.Program () (PLC.defaultVersion ()) (void compiled)) Nothing

unsafely :: Throwable uni => ExceptT (Error uni (Provenance ())) Quote a -> a
unsafely ma = runQuote $ do
    run <- runExceptT ma
    case run of
        Left e  -> throw e
        Right t -> pure t

-- | Get a Plutus Core term corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
lift :: (Lift.Lift uni a, Throwable uni) => a -> PLC.Term TyName Name uni ()
lift a = unsafely $ safeLift a

-- | Get a Plutus Core program corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
liftProgram :: (Lift.Lift uni a, Throwable uni) => a -> PLC.Program TyName Name uni ()
liftProgram x = PLC.Program () (PLC.defaultVersion ()) $ lift x

-- | Get a Plutus Core program in the default universe corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
liftProgramDef :: Lift.Lift PLC.DefaultUni a => a -> PLC.Program TyName Name PLC.DefaultUni ()
liftProgramDef = liftProgram

-- | Get a Plutus Core program corresponding to the given value as a 'CompiledCode', throwing any errors that occur as exceptions and ignoring fresh names.
liftCode :: (Lift.Lift uni a, Throwable uni) => a -> CompiledCode uni a
liftCode x = unsafely $ safeLiftCode x

-- | Creates a program that ignores an argument of the given type and returns the program given.
constCode
    :: (Lift.Typeable uni a, Throwable uni
       , uni `PLC.Everywhere` Serialise)
    => Proxy a
    -> CompiledCode uni b
    -> CompiledCode uni (a -> b)
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
    :: forall e a uni m .
       ( Lift.Typeable uni a
       , PIR.AsTypeError e (PIR.Term TyName Name uni ()) uni (Provenance ())
       , PIR.AsTypeErrorExt e uni (Provenance ())
       , PIR.AsError e uni (Provenance ())
       , MonadError e m, MonadQuote m
       , PLC.GShow uni, PLC.GEq uni, PLC.DefaultUni PLC.<: uni
       )
    => Proxy a
    -> PLC.Term PLC.TyName PLC.Name uni ()
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
    -- FIXME: we need to pass the real dynamic builtin tcconfig map in compileterm
    compiled <- flip runReaderT defaultCompilationCtx $ compileTerm True applied
    -- PLC errors are parameterized over PLC.Terms, whereas PIR errors over PIR.Terms and as such, these prism errors cannot be unified.
    -- We instead run the ExceptT, collect any PLC error and explicitly lift into a PIR error by wrapping with PIR._PLCError
    plcConcrete <-
        runExceptT $ do
          types <- PLC.getStringBuiltinTypes noProvenance
          void $ PLC.inferType (PLC.defConfig { PLC._tccDynamicBuiltinNameTypes = types }) compiled
    -- note: e is a scoped tyvar acting here AsError e uni (Provenance ())
    let plcPrismatic = first (view (re PIR._PLCError)) plcConcrete
    liftEither plcPrismatic -- embed prismatic-either to a monaderror

-- | Try to interpret a PLC program as a 'CompiledCode' of the given type. Returns successfully iff the program has the right type.
typeCode
    :: forall e a uni m .
       ( Lift.Typeable uni a
       , PIR.AsTypeError e (PIR.Term TyName Name uni ()) uni (Provenance ())
       , PIR.AsTypeErrorExt e uni (Provenance ())
       , PIR.AsError e uni (Provenance ())
       , MonadError e m, MonadQuote m
       , PLC.GShow uni, PLC.GEq uni, PLC.DefaultUni PLC.<: uni
       )
    => Proxy a
    -> PLC.Program PLC.TyName PLC.Name uni ()
    -> m (CompiledCode uni a)
typeCode p prog@(PLC.Program _ _ term) = do
    _ <- typeCheckAgainst p term
    pure $ DeserializedCode prog Nothing
