{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
module Language.PlutusTx.Lift (
    makeLift,
    safeLift,
    safeLiftProgram,
    safeLiftCode,
    lift,
    liftProgram,
    liftProgramDef,
    liftCode,
    typeCheckAgainst,
    typeCode) where

import           Language.PlutusTx.Code
import           Language.PlutusTx.Lift.Class             (makeLift)
import qualified Language.PlutusTx.Lift.Class             as Lift
import           Language.PlutusTx.Lift.Instances         ()

import           Data.Bifunctor
import           Language.PlutusIR
import qualified Language.PlutusIR                        as PIR
import           Language.PlutusIR.Compiler
import           Language.PlutusIR.Compiler.Definitions
import qualified Language.PlutusIR.Error                  as PIR
import qualified Language.PlutusIR.MkPir                  as PIR

import qualified Language.PlutusCore                      as PLC
import qualified Language.PlutusCore.Constant             as PLC
import           Language.PlutusCore.Pretty               (PrettyConst)
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.StdLib.Data.Function as PLC

import qualified Language.UntypedPlutusCore               as UPLC

import           Control.Exception
import           Control.Lens                             hiding (lifted)
import           Control.Monad.Except                     hiding (lift)
import           Control.Monad.Reader                     hiding (lift)

import           Data.Proxy
import           Data.Text.Prettyprint.Doc
import qualified Data.Typeable                            as GHC

type Throwable uni = (PLC.GShow uni, PLC.GEq uni, PLC.Closed uni, uni `PLC.Everywhere` PrettyConst, GHC.Typeable uni)

-- | Get a Plutus Core term corresponding to the given value.
safeLift
    :: (Lift.Lift uni fun a
       , PIR.AsTypeError e (PIR.Term TyName Name uni fun ()) uni fun (Provenance ()), PLC.GShow uni, PLC.GEq uni
       , PIR.AsTypeErrorExt e uni (Provenance ())

       , AsError e uni fun (Provenance ()), MonadError e m, MonadQuote m
       , PLC.ToBuiltinMeaning uni fun
       )
    => a -> m (UPLC.Term Name uni fun ())
safeLift x = do
    lifted <- liftQuote $ runDefT () $ Lift.lift x
    tcConfig <- PLC.getDefTypeCheckConfig $ Original ()
    compiled <- flip runReaderT (toDefaultCompilationCtx tcConfig) $ compileTerm True lifted
    pure $ void $ UPLC.erase compiled

-- | Get a Plutus Core program corresponding to the given value.
safeLiftProgram
    :: (Lift.Lift uni fun a
       , PIR.AsTypeError e (PIR.Term TyName Name uni fun ()) uni fun (Provenance ()), PLC.GShow uni, PLC.GEq uni
       , PIR.AsTypeErrorExt e uni (Provenance ())

       , AsError e uni fun (Provenance ()), MonadError e m, MonadQuote m
       , PLC.ToBuiltinMeaning uni fun
       )
    => a -> m (UPLC.Program Name uni fun ())
safeLiftProgram x = UPLC.Program () (PLC.defaultVersion ()) <$> safeLift x

safeLiftCode
    :: (Lift.Lift uni fun a
       , PIR.AsTypeError e (PIR.Term TyName Name uni fun ()) uni fun (Provenance ()), PLC.GShow uni, PLC.GEq uni
       , PIR.AsTypeErrorExt e uni (Provenance ())
       , AsError e uni fun (Provenance ()), MonadError e m, MonadQuote m
       , PLC.ToBuiltinMeaning uni fun
       )
    => a -> m (CompiledCode uni fun a)
safeLiftCode x = DeserializedCode <$> safeLiftProgram x <*> pure Nothing

unsafely
    :: (Throwable uni, GHC.Typeable fun, Pretty fun)
    => ExceptT (Error uni fun (Provenance ())) Quote a -> a
unsafely ma = runQuote $ do
    run <- runExceptT ma
    case run of
        Left e  -> throw e
        Right t -> pure t

-- | Get a Plutus Core term corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
lift
    :: ( Lift.Lift uni fun a, Throwable uni
       , GHC.Typeable fun, Pretty fun, PLC.ToBuiltinMeaning uni fun
       )
    => a -> UPLC.Term Name uni fun ()
lift a = unsafely $ safeLift a

-- | Get a Plutus Core program corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
liftProgram
    :: ( Lift.Lift uni fun a, Throwable uni
       , GHC.Typeable fun, Pretty fun, PLC.ToBuiltinMeaning uni fun
       )
    => a -> UPLC.Program Name uni fun ()
liftProgram x = UPLC.Program () (PLC.defaultVersion ()) $ lift x

-- | Get a Plutus Core program in the default universe corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
liftProgramDef
    :: Lift.Lift PLC.DefaultUni PLC.DefaultFun a
    => a -> UPLC.Program Name PLC.DefaultUni PLC.DefaultFun ()
liftProgramDef = liftProgram

-- | Get a Plutus Core program corresponding to the given value as a 'CompiledCode', throwing any errors that occur as exceptions and ignoring fresh names.
liftCode
    :: ( Lift.Lift uni fun a, Throwable uni
       , GHC.Typeable fun, Pretty fun, PLC.ToBuiltinMeaning uni fun
       ) => a -> CompiledCode uni fun a
liftCode x = unsafely $ safeLiftCode x

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
    :: forall e a uni fun m .
       ( Lift.Typeable uni fun a
       , PIR.AsTypeError e (PIR.Term TyName Name uni fun ()) uni fun (Provenance ())
       , PIR.AsTypeErrorExt e uni (Provenance ())
       , PIR.AsError e uni fun (Provenance ())
       , MonadError e m, MonadQuote m
       , PLC.GShow uni, PLC.GEq uni
       , PLC.ToBuiltinMeaning uni fun
       )
    => Proxy a
    -> PLC.Term PLC.TyName PLC.Name uni fun ()
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
    tcConfig <- PLC.getDefTypeCheckConfig (Original ())
    compiled <- flip runReaderT (toDefaultCompilationCtx tcConfig) $ compileTerm True applied
    -- PLC errors are parameterized over PLC.Terms, whereas PIR errors over PIR.Terms and as such, these prism errors cannot be unified.
    -- We instead run the ExceptT, collect any PLC error and explicitly lift into a PIR error by wrapping with PIR._PLCError
    plcConcrete <- runExceptT $ void $ PLC.inferType tcConfig compiled
    -- note: e is a scoped tyvar acting here AsError e uni (Provenance ())
    let plcPrismatic = first (view (re PIR._PLCError)) plcConcrete
    liftEither plcPrismatic -- embed prismatic-either to a monaderror

-- | Try to interpret a PLC program as a 'CompiledCode' of the given type. Returns successfully iff the program has the right type.
typeCode
    :: forall e a uni fun m .
       ( Lift.Typeable uni fun a
       , PIR.AsTypeError e (PIR.Term TyName Name uni fun ()) uni fun (Provenance ())
       , PIR.AsTypeErrorExt e uni (Provenance ())
       , PIR.AsError e uni fun (Provenance ())
       , MonadError e m, MonadQuote m
       , PLC.GShow uni, PLC.GEq uni
       , PLC.ToBuiltinMeaning uni fun
       )
    => Proxy a
    -> PLC.Program PLC.TyName PLC.Name uni fun ()
    -> m (CompiledCode uni fun a)
typeCode p prog@(PLC.Program _ _ term) = do
    _ <- typeCheckAgainst p term
    pure $ DeserializedCode (UPLC.eraseProgram prog) Nothing
