-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

module PlutusTx.Lift
  ( safeLiftWith
  , safeLift
  , safeLiftUnopt
  , safeLiftProgram
  , safeLiftProgramUnopt
  , safeLiftCode
  , safeLiftCodeUnopt
  , lift
  , liftUnopt
  , liftProgram
  , liftProgramUnopt
  , liftProgramDef
  , liftProgramDefUnopt
  , liftCode
  , liftCodeUnopt
  , liftCodeDef
  , liftCodeDefUnopt
  , typeCheckAgainst
  , typeCode
  , makeTypeable
  , makeLift
  , LiftError (..)
  ) where

import PlutusTx.Code
import PlutusTx.Lift.Class qualified as Lift
import PlutusTx.Lift.Instances ()
import PlutusTx.Lift.TH (LiftError (..), makeLift, makeTypeable)

import PlutusIR
import PlutusIR qualified as PIR
import PlutusIR.Analysis.Builtins as PIR
import PlutusIR.Compiler
import PlutusIR.Compiler.Definitions
import PlutusIR.Compiler.Types qualified as PIR
import PlutusIR.Error qualified as PIR
import PlutusIR.MkPir qualified as PIR
import PlutusIR.Transform.RewriteRules as PIR

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
import Control.Monad.Except (ExceptT, MonadError, modifyError, runExceptT)
import Control.Monad.Reader (runReaderT)
import Data.Default.Class
import Data.Hashable
import Data.Proxy

-- We do not use qualified import because the whole module contains off-chain code
import Prelude as Haskell

{-| Get a Plutus Core term corresponding to the given value. Allows configuring
PIR and UPLC optimization options. -}
safeLiftWith
  :: forall a uni fun m
   . ( Lift.Lift uni a
     , PLC.GEq uni
     , PLC.Everywhere uni Eq
     , MonadError (PIR.Error uni fun (Provenance ())) m
     , MonadQuote m
     , PLC.Typecheckable uni fun
     , PLC.CaseBuiltin uni
     , PrettyUni uni
     , Pretty fun
     , Default (PLC.CostingPart uni fun)
     , Default (PIR.BuiltinsInfo uni fun)
     , Default (PIR.RewriteRules uni fun)
     , Hashable fun
     )
  => (PIR.CompilationOpts () -> PIR.CompilationOpts ())
  -- ^ Modifier of PIR compilation options
  -> (PLC.CompilationOpts Name fun (Provenance ()) -> PLC.CompilationOpts Name fun (Provenance ()))
  -- ^ Modifier of UPLC compilation options
  -> PLC.Version
  -> a
  -> m (PIR.Term PLC.TyName PLC.Name uni fun (), UPLC.Term UPLC.NamedDeBruijn uni fun ())
safeLiftWith f g v x = do
  pir <- liftQuote $ runDefT () $ Lift.lift x
  tcConfig <- modifyError (PLCError . PLC.TypeErrorE) $ PLC.getDefTypeCheckConfig $ Original ()
  let ccConfig =
        toDefaultCompilationCtx tcConfig
          & over ccOpts f
          -- This is a bit awkward as it makes the choice not configurable by the user. But it's already
          -- prety annoying passing in the version. We may eventually need to bite the bullet and provide a version
          -- that takes all the compilation options and everything.
          & set
            (ccOpts . coDatatypes . dcoStyle)
            (if v >= PLC.plcVersion110 then SumsOfProducts else ScottEncoding)
      ucOpts = g PLC.defaultCompilationOpts
  plc <- flip runReaderT ccConfig $ compileProgram (Program () v pir)
  uplc <- flip runReaderT ucOpts $ PLC.compileProgram plc
  UPLC.Program _ _ db <-
    modifyError (PLCError . PLC.FreeVariableErrorE) $ traverseOf UPLC.progTerm UPLC.deBruijnTerm uplc
  pure (void pir, void db)

{-| Get a Plutus Core term corresponding to the given value, applying default PIR/UPLC
optimizations. -}
safeLift
  :: forall a uni fun m
   . ( Lift.Lift uni a
     , PLC.GEq uni
     , PLC.Everywhere uni Eq
     , MonadError (PIR.Error uni fun (Provenance ())) m
     , MonadQuote m
     , PLC.Typecheckable uni fun
     , PLC.CaseBuiltin uni
     , PrettyUni uni
     , Pretty fun
     , Default (PLC.CostingPart uni fun)
     , Default (PIR.BuiltinsInfo uni fun)
     , Default (PIR.RewriteRules uni fun)
     , Hashable fun
     )
  => PLC.Version
  -> a
  -> m (PIR.Term PLC.TyName PLC.Name uni fun (), UPLC.Term UPLC.NamedDeBruijn uni fun ())
safeLift = safeLiftWith id id

{-| Like `safeLift` but does not apply PIR/UPLC optimizations. Use this option
where lifting speed is more important than optimal code. -}
safeLiftUnopt
  :: forall a uni fun m
   . ( Lift.Lift uni a
     , PLC.GEq uni
     , PLC.Everywhere uni Eq
     , MonadError (PIR.Error uni fun (Provenance ())) m
     , MonadQuote m
     , PLC.Typecheckable uni fun
     , PLC.CaseBuiltin uni
     , PrettyUni uni
     , Pretty fun
     , Default (PLC.CostingPart uni fun)
     , Default (PIR.BuiltinsInfo uni fun)
     , Default (PIR.RewriteRules uni fun)
     , Hashable fun
     )
  => PLC.Version
  -> a
  -> m (PIR.Term PLC.TyName PLC.Name uni fun (), UPLC.Term UPLC.NamedDeBruijn uni fun ())
safeLiftUnopt =
  safeLiftWith
    (set coMaxSimplifierIterations 0)
    ( set (PLC.coSimplifyOpts . UPLC.soMaxSimplifierIterations) 0
        . set (PLC.coSimplifyOpts . UPLC.soMaxCseIterations) 0
    )

{-| Get a Plutus Core program corresponding to the given value, applying default PIR/UPLC
optimizations. -}
safeLiftProgram
  :: ( Lift.Lift uni a
     , PLC.GEq uni
     , PLC.Everywhere uni Eq
     , MonadError (PIR.Error uni fun (Provenance ())) m
     , MonadQuote m
     , PLC.Typecheckable uni fun
     , PLC.CaseBuiltin uni
     , PrettyUni uni
     , Pretty fun
     , Default (PLC.CostingPart uni fun)
     , Default (PIR.BuiltinsInfo uni fun)
     , Default (PIR.RewriteRules uni fun)
     , Hashable fun
     )
  => PLC.Version
  -> a
  -> m (PIR.Program PLC.TyName PLC.Name uni fun (), UPLC.Program UPLC.NamedDeBruijn uni fun ())
safeLiftProgram v x = bimap (PIR.Program () v) (UPLC.Program () v) <$> safeLift v x

{-| Like `safeLiftProgram` but does not apply PIR/UPLC optimizations. Use this option
where lifting speed is more important than optimal code. -}
safeLiftProgramUnopt
  :: ( Lift.Lift uni a
     , PLC.GEq uni
     , PLC.Everywhere uni Eq
     , MonadError (PIR.Error uni fun (Provenance ())) m
     , MonadQuote m
     , PLC.Typecheckable uni fun
     , PLC.CaseBuiltin uni
     , PrettyUni uni
     , Pretty fun
     , Default (PLC.CostingPart uni fun)
     , Default (PIR.BuiltinsInfo uni fun)
     , Default (PIR.RewriteRules uni fun)
     , Hashable fun
     )
  => PLC.Version
  -> a
  -> m (PIR.Program PLC.TyName PLC.Name uni fun (), UPLC.Program UPLC.NamedDeBruijn uni fun ())
safeLiftProgramUnopt v x = bimap (PIR.Program () v) (UPLC.Program () v) <$> safeLiftUnopt v x

safeLiftCode
  :: ( Lift.Lift uni a
     , PLC.GEq uni
     , PLC.Everywhere uni Eq
     , MonadError (PIR.Error uni fun (Provenance ())) m
     , MonadQuote m
     , PLC.Typecheckable uni fun
     , PLC.CaseBuiltin uni
     , PrettyUni uni
     , Pretty fun
     , Default (PLC.CostingPart uni fun)
     , Default (PIR.BuiltinsInfo uni fun)
     , Default (PIR.RewriteRules uni fun)
     , Hashable fun
     )
  => PLC.Version -> a -> m (CompiledCodeIn uni fun a)
safeLiftCode v =
  fmap
    ( \(pir, uplc) ->
        DeserializedCode (mempty <$ uplc) (Just (mempty <$ pir)) mempty
    )
    . safeLiftProgram v

{-| Like `safeLiftCode` but does not apply PIR/UPLC optimizations. Use this option
where lifting speed is more important than optimal code. -}
safeLiftCodeUnopt
  :: ( Lift.Lift uni a
     , PLC.GEq uni
     , PLC.Everywhere uni Eq
     , MonadError (PIR.Error uni fun (Provenance ())) m
     , MonadQuote m
     , PLC.Typecheckable uni fun
     , PLC.CaseBuiltin uni
     , PrettyUni uni
     , Pretty fun
     , Default (PLC.CostingPart uni fun)
     , Default (PIR.BuiltinsInfo uni fun)
     , Default (PIR.RewriteRules uni fun)
     , Hashable fun
     )
  => PLC.Version -> a -> m (CompiledCodeIn uni fun a)
safeLiftCodeUnopt v =
  fmap
    ( \(pir, uplc) ->
        DeserializedCode (mempty <$ uplc) (Just (mempty <$ pir)) mempty
    )
    . safeLiftProgramUnopt v

unsafely
  :: ThrowableBuiltins uni fun
  => ExceptT (Error uni fun (Provenance ())) Quote a -> a
unsafely ma = runQuote $ do
  run <- runExceptT ma
  case run of
    Left e -> throw e
    Right t -> pure t

{-| Get a Plutus Core term corresponding to the given value, throwing any errors that
occur as exceptions and ignoring fresh names. The default PIR/UPLC optimizations
are applied. -}
lift
  :: ( Lift.Lift uni a
     , ThrowableBuiltins uni fun
     , PLC.Typecheckable uni fun
     , PLC.GEq uni
     , PLC.Everywhere uni Eq
     , PLC.CaseBuiltin uni
     , Default (PLC.CostingPart uni fun)
     , Default (PIR.BuiltinsInfo uni fun)
     , Default (PIR.RewriteRules uni fun)
     , Hashable fun
     )
  => PLC.Version
  -> a
  -> (PIR.Term PLC.TyName PLC.Name uni fun (), UPLC.Term UPLC.NamedDeBruijn uni fun ())
lift v a = unsafely $ safeLift v a

{-| Like `lift` but does not apply PIR/UPLC optimizations. Use this option
where lifting speed is more important than optimal code. -}
liftUnopt
  :: ( Lift.Lift uni a
     , ThrowableBuiltins uni fun
     , PLC.Typecheckable uni fun
     , PLC.GEq uni
     , PLC.Everywhere uni Eq
     , PLC.CaseBuiltin uni
     , Default (PLC.CostingPart uni fun)
     , Default (PIR.BuiltinsInfo uni fun)
     , Default (PIR.RewriteRules uni fun)
     , Hashable fun
     )
  => PLC.Version
  -> a
  -> (PIR.Term PLC.TyName PLC.Name uni fun (), UPLC.Term UPLC.NamedDeBruijn uni fun ())
liftUnopt v a = unsafely $ safeLiftUnopt v a

-- | Get a Plutus Core program corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
liftProgram
  :: ( Lift.Lift uni a
     , ThrowableBuiltins uni fun
     , PLC.Typecheckable uni fun
     , PLC.GEq uni
     , PLC.Everywhere uni Eq
     , PLC.CaseBuiltin uni
     , Default (PLC.CostingPart uni fun)
     , Default (PIR.BuiltinsInfo uni fun)
     , Default (PIR.RewriteRules uni fun)
     , Hashable fun
     )
  => PLC.Version
  -> a
  -> (PIR.Program PLC.TyName PLC.Name uni fun (), UPLC.Program UPLC.NamedDeBruijn uni fun ())
liftProgram v x = unsafely $ safeLiftProgram v x

{-| Like `liftProgram` but does not apply PIR/UPLC optimizations. Use this option
where lifting speed is more important than optimal code. -}
liftProgramUnopt
  :: ( Lift.Lift uni a
     , ThrowableBuiltins uni fun
     , PLC.Typecheckable uni fun
     , PLC.GEq uni
     , PLC.Everywhere uni Eq
     , PLC.CaseBuiltin uni
     , Default (PLC.CostingPart uni fun)
     , Default (PIR.BuiltinsInfo uni fun)
     , Default (PIR.RewriteRules uni fun)
     , Hashable fun
     )
  => PLC.Version
  -> a
  -> (PIR.Program PLC.TyName PLC.Name uni fun (), UPLC.Program UPLC.NamedDeBruijn uni fun ())
liftProgramUnopt v x = unsafely $ safeLiftProgram v x

-- | Get a Plutus Core program in the default universe with the default version, corresponding to the given value, throwing any errors that occur as exceptions and ignoring fresh names.
liftProgramDef
  :: Lift.Lift PLC.DefaultUni a
  => a
  -> ( PIR.Program PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ()
     , UPLC.Program UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ()
     )
liftProgramDef = liftProgram PLC.latestVersion

{-| Like `liftProgramDef` but does not apply PIR/UPLC optimizations. Use this option
where lifting speed is more important than optimal code. -}
liftProgramDefUnopt
  :: Lift.Lift PLC.DefaultUni a
  => a
  -> ( PIR.Program PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ()
     , UPLC.Program UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ()
     )
liftProgramDefUnopt = liftProgramUnopt PLC.latestVersion

-- | Get a Plutus Core program corresponding to the given value as a 'CompiledCodeIn', throwing any errors that occur as exceptions and ignoring fresh names.
liftCode
  :: ( Lift.Lift uni a
     , PLC.GEq uni
     , PLC.Everywhere uni Eq
     , ThrowableBuiltins uni fun
     , PLC.Typecheckable uni fun
     , PLC.CaseBuiltin uni
     , Default (PLC.CostingPart uni fun)
     , Default (PIR.BuiltinsInfo uni fun)
     , Default (PIR.RewriteRules uni fun)
     , Hashable fun
     )
  => PLC.Version -> a -> CompiledCodeIn uni fun a
liftCode v x = unsafely $ safeLiftCode v x

{-| Like `liftCode` but does not apply PIR/UPLC optimizations. Use this option
where lifting speed is more important than optimal code. -}
liftCodeUnopt
  :: ( Lift.Lift uni a
     , PLC.GEq uni
     , PLC.Everywhere uni Eq
     , ThrowableBuiltins uni fun
     , PLC.Typecheckable uni fun
     , PLC.CaseBuiltin uni
     , Default (PLC.CostingPart uni fun)
     , Default (PIR.BuiltinsInfo uni fun)
     , Default (PIR.RewriteRules uni fun)
     , Hashable fun
     )
  => PLC.Version -> a -> CompiledCodeIn uni fun a
liftCodeUnopt v x = unsafely $ safeLiftCodeUnopt v x

-- | Get a Plutus Core program with the default version, corresponding to the given value as a 'CompiledCodeIn', throwing any errors that occur as exceptions and ignoring fresh names.
liftCodeDef
  :: ( Lift.Lift uni a
     , PLC.GEq uni
     , PLC.Everywhere uni Eq
     , ThrowableBuiltins uni fun
     , PLC.Typecheckable uni fun
     , PLC.CaseBuiltin uni
     , Default (PLC.CostingPart uni fun)
     , Default (PIR.BuiltinsInfo uni fun)
     , Default (PIR.RewriteRules uni fun)
     , Hashable fun
     )
  => a -> CompiledCodeIn uni fun a
liftCodeDef = liftCode PLC.latestVersion

{-| Like `liftCodeDef` but does not apply PIR/UPLC optimizations. Use this option
where lifting speed is more important than optimal code. -}
liftCodeDefUnopt
  :: ( Lift.Lift uni a
     , PLC.GEq uni
     , PLC.Everywhere uni Eq
     , ThrowableBuiltins uni fun
     , PLC.Typecheckable uni fun
     , PLC.CaseBuiltin uni
     , Default (PLC.CostingPart uni fun)
     , Default (PIR.BuiltinsInfo uni fun)
     , Default (PIR.RewriteRules uni fun)
     , Hashable fun
     )
  => a -> CompiledCodeIn uni fun a
liftCodeDefUnopt = liftCodeUnopt PLC.latestVersion

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
  :: forall a uni fun m
   . ( Lift.Typeable uni a
     , MonadError (PIR.Error uni fun (Provenance ())) m
     , MonadQuote m
     , PLC.GEq uni
     , PLC.Typecheckable uni fun
     , PLC.CaseBuiltin uni
     , PrettyUni uni
     , Pretty fun
     , Default (PLC.CostingPart uni fun)
     , Default (PIR.BuiltinsInfo uni fun)
     , Default (PIR.RewriteRules uni fun)
     )
  => Proxy a
  -> PLC.Program PLC.TyName PLC.Name uni fun ()
  -> m ()
typeCheckAgainst p (PLC.Program _ v plcTerm) = do
  -- See Note [Checking the type of a term with Typeable]
  term <- PIR.embedTerm <$> PLC.rename plcTerm
  -- We need to run Def *before* applying to the term, otherwise we may refer to abstract
  -- types and we won't match up with the term.
  idFun <- liftQuote $ runDefT () $ do
    ty <- Lift.typeRep p
    pure $ TyInst () PLC.idFun ty
  let applied = Apply () idFun term
  -- Here we use a 'Default' builtin semantics variant, because the
  -- typechecker needs to be handed a builtin semantics variant (implementation detail).
  -- See Note [Builtin semantics variants]
  tcConfig <- modifyError (PLCError . PLC.TypeErrorE) $ PLC.getDefTypeCheckConfig (Original ())
  -- The PIR compiler *pointfully* needs a builtin semantics variant, but in
  -- this instance of only "lifting" it is safe to default to any builtin
  -- semantics variant, since the 'Lift' is impervious to builtins and will
  -- not generate code containing builtins.  See Note [Builtin semantics variants]
  compiled <-
    flip runReaderT (toDefaultCompilationCtx tcConfig) $ compileProgram (Program () v applied)

  void $ modifyError (PLCError . PLC.TypeErrorE) $ PLC.inferTypeOfProgram tcConfig compiled

-- | Try to interpret a PLC program as a 'CompiledCodeIn' of the given type. Returns successfully iff the program has the right type.
typeCode
  :: forall a uni fun m
   . ( Lift.Typeable uni a
     , MonadError (PIR.Error uni fun (Provenance ())) m
     , MonadQuote m
     , PLC.GEq uni
     , PLC.Everywhere uni Eq
     , PLC.Typecheckable uni fun
     , PLC.CaseBuiltin uni
     , PrettyUni uni
     , Pretty fun
     , Default (PLC.CostingPart uni fun)
     , Default (PIR.BuiltinsInfo uni fun)
     , Default (PIR.RewriteRules uni fun)
     , Hashable fun
     )
  => Proxy a
  -> PLC.Program PLC.TyName PLC.Name uni fun ()
  -> m (CompiledCodeIn uni fun a)
typeCode p prog = do
  _ <- typeCheckAgainst p prog
  compiled <-
    flip runReaderT PLC.defaultCompilationOpts $
      PLC.compileProgram prog
  db <-
    modifyError (PLCError . PLC.FreeVariableErrorE) $
      traverseOf UPLC.progTerm UPLC.deBruijnTerm compiled
  pure $ DeserializedCode (mempty <$ db) Nothing mempty
