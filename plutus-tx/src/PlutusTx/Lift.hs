{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
module PlutusTx.Lift (
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

import PlutusTx.Code
import PlutusTx.Lift.Class (makeLift)
import PlutusTx.Lift.Class qualified as Lift
import PlutusTx.Lift.Instances ()

import Data.Bifunctor
import PlutusIR
import PlutusIR qualified as PIR
import PlutusIR.Compiler
import PlutusIR.Compiler.Definitions
import PlutusIR.Error qualified as PIR
import PlutusIR.MkPir qualified as PIR

import PlutusCore qualified as PLC
import PlutusCore.Pretty (PrettyConst)
import PlutusCore.Quote
import PlutusCore.StdLib.Data.Function qualified as PLC

import UntypedPlutusCore qualified as UPLC

import Control.Exception
import Control.Lens hiding (lifted)
import Control.Monad.Except hiding (lift)
import Control.Monad.Reader hiding (lift)

import Data.Proxy
import Data.Typeable qualified as GHC
import Prettyprinter

-- We do not use qualified import because the whole module contains off-chain code
import Prelude as Haskell

type PrettyPrintable uni fun = ( PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PrettyConst, Pretty fun)

type Throwable uni fun =
    ( PLC.GShow uni, PLC.GEq uni, PLC.Closed uni, uni `PLC.Everywhere` PrettyConst, GHC.Typeable uni
    , Pretty fun, GHC.Typeable fun
    )

-- | Get a Plutus Core term corresponding to the given value.
safeLift
    :: (Lift.Lift uni a
       , PIR.AsTypeError e (PIR.Term TyName Name uni fun ()) uni fun (Provenance ()), PLC.GEq uni
       , PIR.AsTypeErrorExt e uni (Provenance ())
       , PLC.AsFreeVariableError e
       , AsError e uni fun (Provenance ()), MonadError e m, MonadQuote m
       , PLC.Typecheckable uni fun
       , PrettyPrintable uni fun
       )
    => a -> m (UPLC.Term UPLC.NamedDeBruijn uni fun ())
safeLift x = do
    lifted <- liftQuote $ runDefT () $ Lift.lift x
    tcConfig <- PLC.getDefTypeCheckConfig $ Original ()
    -- NOTE:  Disabling simplifier, as it takes a lot of time during runtime
    let ccConfig = set (ccOpts . coMaxSimplifierIterations) 0 (toDefaultCompilationCtx tcConfig)
    compiled <- flip runReaderT ccConfig $ compileTerm lifted
    let erased = UPLC.erase compiled
    db <- UPLC.deBruijnTerm $ UPLC.simplifyTerm erased
    pure $ void db

-- | Get a Plutus Core program corresponding to the given value.
safeLiftProgram
    :: (Lift.Lift uni a
       , PIR.AsTypeError e (PIR.Term TyName Name uni fun ()) uni fun (Provenance ()),  PLC.GEq uni
       , PIR.AsTypeErrorExt e uni (Provenance ())
       , PLC.AsFreeVariableError e
       , AsError e uni fun (Provenance ()), MonadError e m, MonadQuote m
       , PLC.Typecheckable uni fun
       , PrettyPrintable uni fun
       )
    => a -> m (UPLC.Program UPLC.NamedDeBruijn uni fun ())
safeLiftProgram x = UPLC.Program () (PLC.defaultVersion ()) <$> safeLift x

safeLiftCode
    :: (Lift.Lift uni a
       , PIR.AsTypeError e (PIR.Term TyName Name uni fun ()) uni fun (Provenance ()), PLC.GEq uni
       , PIR.AsTypeErrorExt e uni (Provenance ())
       , PLC.AsFreeVariableError e
       , AsError e uni fun (Provenance ()), MonadError e m, MonadQuote m
       , PLC.Typecheckable uni fun
       , PrettyPrintable uni fun
       )
    => a -> m (CompiledCodeIn uni fun a)
safeLiftCode x = DeserializedCode <$> safeLiftProgram x <*> pure Nothing <*> pure mempty

unsafely
    :: Throwable uni fun
    => ExceptT (Error uni fun (Provenance ())) Quote a -> a
unsafely ma = runQuote $ do
    run <- runExceptT ma
    case run of
        Left e  -> throw e
        Right t -> pure t

-- | Get a Plutus Core term corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
lift
    :: (Lift.Lift uni a, Throwable uni fun, PLC.Typecheckable uni fun)
    => a -> UPLC.Term UPLC.NamedDeBruijn uni fun ()
lift a = unsafely $ safeLift a

-- | Get a Plutus Core program corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
liftProgram
    :: (Lift.Lift uni a, Throwable uni fun, PLC.Typecheckable uni fun)
    => a -> UPLC.Program UPLC.NamedDeBruijn uni fun ()
liftProgram x = UPLC.Program () (PLC.defaultVersion ()) $ lift x

-- | Get a Plutus Core program in the default universe corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
liftProgramDef
    :: Lift.Lift PLC.DefaultUni a
    => a -> UPLC.Program UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ()
liftProgramDef = liftProgram

-- | Get a Plutus Core program corresponding to the given value as a 'CompiledCodeIn', throwing any errors that occur as exceptions and ignoring fresh names.
liftCode
    :: (Lift.Lift uni a, Throwable uni fun, PLC.Typecheckable uni fun)
    => a -> CompiledCodeIn uni fun a
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
       ( Lift.Typeable uni a
       , PIR.AsTypeError e (PIR.Term TyName Name uni fun ()) uni fun (Provenance ())
       , PIR.AsTypeErrorExt e uni (Provenance ())
       , PIR.AsError e uni fun (Provenance ())
       , MonadError e m, MonadQuote m
       , PLC.GEq uni
       , PLC.Typecheckable uni fun
       , PrettyPrintable uni fun
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
    compiled <- flip runReaderT (toDefaultCompilationCtx tcConfig) $ compileTerm applied
    -- PLC errors are parameterized over PLC.Terms, whereas PIR errors over PIR.Terms and as such, these prism errors cannot be unified.
    -- We instead run the ExceptT, collect any PLC error and explicitly lift into a PIR error by wrapping with PIR._PLCError
    plcConcrete <- runExceptT $ void $ PLC.inferType tcConfig compiled
    -- note: e is a scoped tyvar acting here AsError e uni (Provenance ())
    let plcPrismatic = first (view (re PIR._PLCError)) plcConcrete
    liftEither plcPrismatic -- embed prismatic-either to a monaderror

-- | Try to interpret a PLC program as a 'CompiledCodeIn' of the given type. Returns successfully iff the program has the right type.
typeCode
    :: forall e a uni fun m .
       ( Lift.Typeable uni a
       , PIR.AsTypeError e (PIR.Term TyName Name uni fun ()) uni fun (Provenance ())
       , PIR.AsTypeErrorExt e uni (Provenance ())
       , PLC.AsFreeVariableError e
       , PIR.AsError e uni fun (Provenance ())
       , MonadError e m, MonadQuote m
       , PLC.GEq uni
       , PLC.Typecheckable uni fun
       , PrettyPrintable uni fun
       )
    => Proxy a
    -> PLC.Program PLC.TyName PLC.Name uni fun ()
    -> m (CompiledCodeIn uni fun a)
typeCode p prog@(PLC.Program _ _ term) = do
    _ <- typeCheckAgainst p term
    let erased = UPLC.eraseProgram prog
    db <-  traverseOf UPLC.progTerm (UPLC.deBruijnTerm . UPLC.simplifyTerm) erased
    pure $ DeserializedCode db Nothing mempty
