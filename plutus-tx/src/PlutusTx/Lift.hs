-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
module PlutusTx.Lift (
    safeLift,
    safeLiftProgram,
    safeLiftCode,
    lift,
    liftProgram,
    liftProgramDef,
    liftCode,
    liftCodeDef,
    typeCheckAgainst,
    typeCode,
    makeTypeable,
    makeLift,
    LiftError(..)) where

import PlutusTx.Code
import PlutusTx.Lift.Class qualified as Lift
import PlutusTx.Lift.Instances ()
import PlutusTx.Lift.TH (LiftError (..), makeLift, makeTypeable)

import PlutusIR
import PlutusIR qualified as PIR
import PlutusIR.Compiler
import PlutusIR.Compiler.Definitions
import PlutusIR.Error qualified as PIR
import PlutusIR.MkPir qualified as PIR

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Compiler qualified as PLC
import PlutusCore.Pretty
import PlutusCore.Quote
import PlutusCore.StdLib.Data.Function qualified as PLC
import PlutusCore.Version qualified as PLC

import UntypedPlutusCore qualified as UPLC

import Control.Exception
import Control.Lens hiding (lifted)
import Control.Monad (void)
import Control.Monad.Except (ExceptT, MonadError, liftEither, runExceptT)
import Control.Monad.Reader (runReaderT)
import Data.Bifunctor
import Data.Default.Class
import Data.Proxy

-- We do not use qualified import because the whole module contains off-chain code
import Prelude as Haskell

-- | Get a Plutus Core term corresponding to the given value.
safeLift
    :: (Lift.Lift uni a
       , PIR.AsTypeError e (PIR.Term TyName Name uni fun ()) uni fun (Provenance ()), PLC.GEq uni
       , PIR.AsTypeErrorExt e uni (Provenance ())
       , PLC.AsFreeVariableError e
       , AsError e uni fun (Provenance ()), MonadError e m, MonadQuote m
       , PLC.Typecheckable uni fun
       , PrettyUni uni, Pretty fun
       , Default (PLC.CostingPart uni fun)
       )
    => PLC.Version -> a -> m (PIR.Term PLC.TyName PLC.Name uni fun (), UPLC.Term UPLC.NamedDeBruijn uni fun ())
safeLift v x = do
    pir <- liftQuote $ runDefT () $ Lift.lift x
    tcConfig <- PLC.getDefTypeCheckConfig $ Original ()
    -- NOTE:  Disabling simplifier, as it takes a lot of time during runtime
    let ccConfig = toDefaultCompilationCtx tcConfig
          & set (ccOpts . coMaxSimplifierIterations) 0
          -- This is a bit awkward as it makes the choice not configurable by the user. But it's already
          -- prety annoying passing in the version. We may eventually need to bite the bullet and provide a version
          -- that takes all the compilation options and everything.
          & set (ccOpts . coDatatypes . dcoStyle) (if v >= PLC.plcVersion110 then SumsOfProducts else ScottEncoding)
        ucOpts = PLC.defaultCompilationOpts & PLC.coSimplifyOpts . UPLC.soMaxSimplifierIterations .~ 0
    plc <- flip runReaderT ccConfig $ compileProgram (Program () v pir)
    uplc <- flip runReaderT ucOpts $ PLC.compileProgram plc
    (UPLC.Program _ _ db) <- traverseOf UPLC.progTerm UPLC.deBruijnTerm uplc
    pure $ (void pir, void db)

-- | Get a Plutus Core program corresponding to the given value.
safeLiftProgram
    :: (Lift.Lift uni a
       , PIR.AsTypeError e (PIR.Term TyName Name uni fun ()) uni fun (Provenance ()),  PLC.GEq uni
       , PIR.AsTypeErrorExt e uni (Provenance ())
       , PLC.AsFreeVariableError e
       , AsError e uni fun (Provenance ()), MonadError e m, MonadQuote m
       , PLC.Typecheckable uni fun
       , PrettyUni uni, Pretty fun
       , Default (PLC.CostingPart uni fun)
       )
    => PLC.Version -> a -> m (PIR.Program PLC.TyName PLC.Name uni fun (), UPLC.Program UPLC.NamedDeBruijn uni fun ())
safeLiftProgram v x = bimap (PIR.Program () v) (UPLC.Program () v) <$> safeLift v x

safeLiftCode
    :: (Lift.Lift uni a
       , PIR.AsTypeError e (PIR.Term TyName Name uni fun ()) uni fun (Provenance ()), PLC.GEq uni
       , PIR.AsTypeErrorExt e uni (Provenance ())
       , PLC.AsFreeVariableError e
       , AsError e uni fun (Provenance ()), MonadError e m, MonadQuote m
       , PLC.Typecheckable uni fun
       , PrettyUni uni, Pretty fun
       , Default (PLC.CostingPart uni fun)
       )
    => PLC.Version -> a -> m (CompiledCodeIn uni fun a)
safeLiftCode v =
    fmap
        ( \(pir, uplc) ->
            DeserializedCode (mempty <$ uplc) (Just (mempty <$ pir)) mempty
        )
        . safeLiftProgram v

unsafely
    :: ThrowableBuiltins uni fun
    => ExceptT (Error uni fun (Provenance ())) Quote a -> a
unsafely ma = runQuote $ do
    run <- runExceptT ma
    case run of
        Left e  -> throw e
        Right t -> pure t

-- | Get a Plutus Core term corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
lift
    :: ( Lift.Lift uni a, ThrowableBuiltins uni fun, PLC.Typecheckable uni fun, PLC.GEq uni
       , Default (PLC.CostingPart uni fun)
       )
    => PLC.Version -> a -> (PIR.Term PLC.TyName PLC.Name uni fun (), UPLC.Term UPLC.NamedDeBruijn uni fun ())
lift v a = unsafely $ safeLift v a

-- | Get a Plutus Core program corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
liftProgram
    :: ( Lift.Lift uni a, ThrowableBuiltins uni fun, PLC.Typecheckable uni fun, PLC.GEq uni
       , Default (PLC.CostingPart uni fun)
       )
    => PLC.Version -> a -> (PIR.Program PLC.TyName PLC.Name uni fun (), UPLC.Program UPLC.NamedDeBruijn uni fun ())
liftProgram v x = unsafely $ safeLiftProgram v x

-- | Get a Plutus Core program in the default universe with the default version, corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
liftProgramDef
    :: Lift.Lift PLC.DefaultUni a
    => a -> (PIR.Program PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun (), UPLC.Program UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ())
liftProgramDef = liftProgram PLC.latestVersion

-- | Get a Plutus Core program corresponding to the given value as a 'CompiledCodeIn', throwing any errors that occur as exceptions and ignoring fresh names.
liftCode
    :: ( Lift.Lift uni a, PLC.GEq uni, ThrowableBuiltins uni fun, PLC.Typecheckable uni fun
       , Default (PLC.CostingPart uni fun)
       )
    => PLC.Version -> a -> CompiledCodeIn uni fun a
liftCode v x = unsafely $ safeLiftCode v x

-- | Get a Plutus Core program with the default version, corresponding to the given value as a 'CompiledCodeIn', throwing any errors that occur as exceptions and ignoring fresh names.
liftCodeDef
    :: ( Lift.Lift uni a, PLC.GEq uni, ThrowableBuiltins uni fun, PLC.Typecheckable uni fun
       , Default (PLC.CostingPart uni fun)
       )
    => a -> CompiledCodeIn uni fun a
liftCodeDef = liftCode PLC.latestVersion

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
       , PrettyUni uni, Pretty fun
       , Default (PLC.CostingPart uni fun)
       )
    => Proxy a
    -> PLC.Program PLC.TyName PLC.Name uni fun ()
    -> m ()
typeCheckAgainst p (PLC.Program _ v plcTerm) = do
    -- See Note [Checking the type of a term with Typeable]
    term <- PIR.embed <$> PLC.rename plcTerm
    -- We need to run Def *before* applying to the term, otherwise we may refer to abstract
    -- types and we won't match up with the term.
    idFun <- liftQuote $ runDefT () $ do
        ty <- Lift.typeRep p
        pure $ TyInst () PLC.idFun ty
    let applied = Apply () idFun term
    -- Here we use a 'Default' builtin semantics variant, because the
    -- typechecker needs to be handed a builtin semantics variant (implementation detail).
    -- See Note [Builtin semantics variants]
    tcConfig <- PLC.getDefTypeCheckConfig (Original ())
    -- The PIR compiler *pointfully* needs a builtin semantics variant, but in
    -- this instance of only "lifting" it is safe to default to any builtin
    -- semantics variant, since the 'Lift' is impervious to builtins and will
    -- not generate code containing builtins.  See Note [Builtin semantics variants]
    compiled <- flip runReaderT (toDefaultCompilationCtx tcConfig) $ compileProgram (Program () v applied)
    -- PLC errors are parameterized over PLC.Terms, whereas PIR errors over PIR.Terms and as such, these prism errors cannot be unified.
    -- We instead run the ExceptT, collect any PLC error and explicitly lift into a PIR error by wrapping with PIR._PLCError
    plcConcrete <- runExceptT $ void $ PLC.inferTypeOfProgram tcConfig compiled
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
       , PrettyUni uni, Pretty fun
       , Default (PLC.CostingPart uni fun)
       )
    => Proxy a
    -> PLC.Program PLC.TyName PLC.Name uni fun ()
    -> m (CompiledCodeIn uni fun a)
typeCode p prog = do
    _ <- typeCheckAgainst p prog
    compiled <- flip runReaderT PLC.defaultCompilationOpts $ PLC.compileProgram prog
    db <- traverseOf UPLC.progTerm UPLC.deBruijnTerm compiled
    pure $ DeserializedCode (const mempty <$> db) Nothing mempty
