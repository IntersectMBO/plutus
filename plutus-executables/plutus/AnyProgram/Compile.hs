{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module AnyProgram.Compile
  ( compileProgram
  , checkProgram
  , toOutAnn
  , plcToOutName
  , uplcToOutName
  , uplcToOutName'
  ) where

import AnyProgram.With
import GetOpt
import Types

import PlutusCore qualified as PLC
import PlutusCore.Annotation
import PlutusCore.Compiler qualified as PLC
import PlutusCore.DeBruijn qualified as PLC
import PlutusCore.Default
import PlutusCore.Error as PLC
import PlutusCore.MkPlc hiding (error)
import PlutusIR qualified as PIR
import PlutusIR.Compiler qualified as PIR
import PlutusIR.TypeCheck qualified as PIR
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Check.Uniques qualified as UPLC

import Control.Lens hiding ((%~))
import Control.Monad.Except
import Control.Monad.Reader
import Data.Singletons.Decide
import Data.Text
import PlutusPrelude hiding ((%~))

-- Note that we use for erroring the original term's annotation
compileProgram
  :: ( ?opts :: Opts
     , e ~ PIR.Provenance (FromAnn (US_ann s1))
     , MonadError (PIR.Error DefaultUni DefaultFun e) m
     )
  => SLang s1
  -> SLang s2
  -> FromLang s1
  -> m (FromLang s2)
compileProgram = curry $ \case
  -- exclude all pir-debruijn input&output combinations
  ----------------------------------------
  (SPir SNamedDeBruijn _, _) -> throwingPIR "pir input cannot be debruijn"
  (SPir SDeBruijn _, _) -> throwingPIR "pir input cannot be nameddebruijn"
  (_, SPir SDeBruijn _) -> throwingPIR "pir out cannot be debruijn"
  (_, SPir SNamedDeBruijn _) -> throwingPIR "pir out cannot be nameddebruijn"
  -- self-lang to self-lang patterns
  ----------------------------------------
  (SPir n1@SName a1, SPir n2@SName a2) ->
    through (modifyError (fmap PIR.Original) . pirTypecheck a1)
      -- TODO: optimise
      >=> pirToOutName n1 n2
      >=> toOutAnn a1 a2
  (SPlc n1 a1, SPlc n2 a2) ->
    -- TODO: modifyError ... is repeated multiple times
    through (modifyError (fmap PIR.Original) . plcTypecheck n1 a1)
      >=> modifyError (fmap PIR.Original . PIR.PLCError . PLC.FreeVariableErrorE)
      . plcToOutName n1 n2
      >=> toOutAnn a1 a2
  (SUplc n1 a1, SUplc n2 a2) ->
    through (modifyError (fmap PIR.Original . PIR.PLCError) . uplcTypecheck n1 a1)
      >=> modifyError (fmap PIR.Original)
      . uplcOptimise n1
      >=> modifyError (fmap PIR.Original . PIR.PLCError . PLC.FreeVariableErrorE)
      . uplcToOutName n1 n2
      >=> toOutAnn a1 a2
  -- nothing to be done; seems silly, but can be used for later changing format of Data
  (SData, SData) -> pure
  -- exclude other cases of Data as target
  (_, SData) -> throwingPIR "Cannot compile a pir/tplc/uplc program to Data"
  -- pir to plc
  ----------------------------------------
  (SPir n1@SName a1, SPlc n2 SUnit) ->
    withA @Ord a1 $
      withA @Pretty a1 $
        withA @AnnInline a1 $
          -- Note: PIR.compileProgram subsumes pir typechecking
          (PLC.runQuoteT . flip runReaderT compCtx . PIR.compileProgram)
            >=> modifyError (fmap PIR.Original . PIR.PLCError . PLC.FreeVariableErrorE)
            . plcToOutName n1 n2
            -- completely drop annotations for now
            >=> pure
            . void
    where
      compCtx =
        PIR.toDefaultCompilationCtx $
          unsafeFromRight @(PIR.Error DefaultUni DefaultFun ()) $
            modifyError (PIR.PLCError . TypeErrorE) $
              PLC.getDefTypeCheckConfig ()

  -- note to self: this restriction is because of PIR.Provenance appearing in the output
  (SPir _n1@SName _, SPlc _ _) -> throwingPIR "only support unit-ann output for now"
  -- plc to pir (a special case of embedding, since plc is subset of pir)
  ----------------------------------------
  (sng1@(SPlc _n1 a1), SPir n2@SName a2) ->
    -- first self-"compile" to plc (just for reusing code)
    compileProgram sng1 (SPlc n2 a1)
      >=> pure
      . embedProgram
      -- here we also run the pir typechecker, and pir optimiser
      -- MAYBE: we shouldn't do the above?
      >=> compileProgram (SPir n2 a1) (SPir n2 a2)
  -- pir to uplc
  ----------------------------------------
  (sng1@(SPir _n1@SName a1), sng2@(SUplc n2 _a2)) ->
    -- intermediate through plc==sng12
    let sng12 = SPlc n2 a1
     in compileProgram sng1 sng12
          >=> compileProgram sng12 sng2
  -- plc to uplc
  ----------------------------------------
  (sng1@(SPlc _n1 _a1), SUplc n2 a2) ->
    -- first self-"compile" to plc (just for reusing code)
    compileProgram sng1 (SPlc n2 a2)
      -- PLC.compileProgram subsumes uplcOptimise
      >=> ( PLC.runQuoteT
              . flip runReaderT PLC.defaultCompilationOpts
              . plcToUplcViaName n2 PLC.compileProgram
          )
      >=> pure
      . UPLC.UnrestrictedProgram
  -- data to pir/plc/uplc

  -- TODO: deduplicate if we had `withTermLikeL`
  (SData, SPir _ a2) ->
    withA @Monoid a2 $
      pure . PIR.Program mempty PLC.latestVersion . PIR.Constant mempty . someValue
  (SData, SPlc _ a2) ->
    withA @Monoid a2 $
      pure . PLC.Program mempty PLC.latestVersion . PLC.Constant mempty . someValue
  (SData, SUplc _ a2) ->
    withA @Monoid a2 $
      pure
        . UPLC.UnrestrictedProgram
        . UPLC.Program mempty PLC.latestVersion
        . UPLC.Constant mempty
        . someValue
  -- uplc to ?
  (SUplc _ _, SPlc _ _) -> throwingPIR "Cannot compile uplc to tplc"
  (SUplc _ _, SPir SName _) -> throwingPIR "Cannot compile uplc to pir"

embedProgram :: PLC.Program tyname name uni fun ann -> PIR.Program tyname name uni fun ann
embedProgram (PLC.Program a v t) = PIR.Program a v $ embedTerm t

toOutAnn
  :: (Functor f, MonadError (PIR.Error uni fun a) m)
  => SAnn s1
  -> SAnn s2
  -> f (FromAnn s1)
  -> m (f (FromAnn s2))
toOutAnn sng1 ((sng1 %~) -> Proved Refl) = pure
toOutAnn _ SUnit = pure . void
toOutAnn _ _ = throwingPIR "cannot convert annotation"

-- MAYBE: All of the following could be unified under a ProgramLike typeclass.
-- or by some singletons type-level programming

pirTypecheck
  :: MonadError (PIR.Error DefaultUni DefaultFun (FromAnn a)) m
  => SAnn a
  -> PIR.Program PLC.TyName PLC.Name DefaultUni DefaultFun (FromAnn a)
  -> m ()
pirTypecheck sngA p = PLC.runQuoteT $ do
  tcConfig <- withA @Monoid sngA $ modifyError (PIR.PLCError . PLC.TypeErrorE) $ PIR.getDefTypeCheckConfig mempty
  void $ PIR.inferTypeOfProgram tcConfig p

plcToUplcViaName
  :: (PLC.MonadQuote m, MonadError (PIR.Error uni fun ann) m)
  => SNaming n
  -> (PLC.Program PLC.TyName PLC.Name uni fun a -> m (UPLC.Program PLC.Name uni fun a))
  -> PLC.Program (FromNameTy n) (FromName n) uni fun a
  -> m (UPLC.Program (FromName n) uni fun a)
plcToUplcViaName sngN act = case sngN of
  SName -> act
  SNamedDeBruijn ->
    plcToName sngN act
      >=> UPLC.progTerm (modifyError (PIR.PLCError . PLC.FreeVariableErrorE) . UPLC.deBruijnTerm)
  SDeBruijn ->
    plcToName sngN act
      >=> UPLC.progTerm (modifyError (PIR.PLCError . PLC.FreeVariableErrorE) . UPLC.deBruijnTerm)
      >=> pure
      . UPLC.programMapNames PLC.unNameDeBruijn

plcToName
  :: (PLC.MonadQuote m, MonadError (PIR.Error uni fun ann) m)
  => SNaming n
  -> (PLC.Program PLC.TyName PLC.Name uni fun a -> m x)
  -> (PLC.Program (FromNameTy n) (FromName n) uni fun a -> m x)
plcToName sngN act = case sngN of
  SName -> act
  SNamedDeBruijn ->
    PLC.progTerm (modifyError (PIR.PLCError . PLC.FreeVariableErrorE) . PLC.unDeBruijnTerm)
      >=> act
  SDeBruijn ->
    pure
      . PLC.programMapNames PLC.fakeTyNameDeBruijn PLC.fakeNameDeBruijn
      >=> plcToName SNamedDeBruijn act

uplcViaName
  :: (PLC.MonadQuote m, MonadError (PIR.Error uni fun ann) m)
  => (UPLC.Program PLC.Name uni fun a -> m (UPLC.Program PLC.Name uni fun a))
  -> SNaming n
  -> UPLC.Program (FromName n) uni fun a
  -> m (UPLC.Program (FromName n) uni fun a)
uplcViaName act sngN = case sngN of
  SName -> act
  SNamedDeBruijn ->
    UPLC.progTerm (modifyError (PIR.PLCError . PLC.FreeVariableErrorE) . UPLC.unDeBruijnTerm)
      >=> act
      >=> UPLC.progTerm (modifyError (PIR.PLCError . PLC.FreeVariableErrorE) . UPLC.deBruijnTerm)
  SDeBruijn ->
    pure
      . UPLC.programMapNames UPLC.fakeNameDeBruijn
      >=> uplcViaName act SNamedDeBruijn
      >=> pure
      . UPLC.programMapNames UPLC.unNameDeBruijn

plcTypecheck
  :: MonadError (PIR.Error DefaultUni DefaultFun (FromAnn a)) m
  => SNaming n
  -> SAnn a
  -> PLC.Program (FromNameTy n) (FromName n) DefaultUni DefaultFun (FromAnn a)
  -> m ()
plcTypecheck sngN sngA p = PLC.runQuoteT $ do
  tcConfig <-
    withA @Monoid sngA $
      modifyError (PIR.PLCError . PLC.TypeErrorE) $
        PLC.getDefTypeCheckConfig mempty
  void $ plcToName sngN (modifyError (PIR.PLCError . PLC.TypeErrorE) . PLC.inferTypeOfProgram tcConfig) p

uplcOptimise
  :: ( ?opts :: Opts
     , MonadError (PIR.Error DefaultUni DefaultFun a) m
     )
  => SNaming n1
  -> UPLC.UnrestrictedProgram (FromName n1) DefaultUni DefaultFun a
  -> m (UPLC.UnrestrictedProgram (FromName n1) DefaultUni DefaultFun a)
uplcOptimise =
  case _optimiseLvl ?opts of
    NoOptimise -> const pure -- short-circuit to avoid renaming
    safeOrUnsafe ->
      let sOpts =
            UPLC.defaultSimplifyOpts
              & case safeOrUnsafe of
                SafeOptimise -> set UPLC.soConservativeOpts True
                UnsafeOptimise -> id
       in fmap PLC.runQuoteT
            . _Wrapped
            . uplcViaName (UPLC.simplifyProgram sOpts def)

-- | We do not have a typechecker for uplc, but we could pretend that scopecheck is a "typechecker"
uplcTypecheck
  :: forall sN sA uni fun m
   . MonadError (PLC.Error uni fun (FromAnn sA)) m
  => SNaming sN
  -> SAnn sA
  -> UPLC.UnrestrictedProgram (FromName sN) uni fun (FromAnn sA)
  -> m ()
uplcTypecheck sngN sngA ast = case sngN of
  SName ->
    modifyError PLC.UniqueCoherencyErrorE $
      withA @Ord sngA $
        UPLC.checkProgram (const True) (ast ^. _Wrapped)
  -- TODO: deduplicate
  SDeBruijn -> modifyError PLC.FreeVariableErrorE $ UPLC.checkScope (ast ^. _Wrapped . UPLC.progTerm)
  SNamedDeBruijn -> modifyError PLC.FreeVariableErrorE $ UPLC.checkScope (ast ^. _Wrapped . UPLC.progTerm)

-- | Placed here just for uniformity, not really needed
pirToOutName
  :: MonadError (PIR.Error uni fun a) m
  => SNaming s1
  -> SNaming s2
  -> PIR.Program (FromNameTy s1) (FromName s1) uni fun ann
  -> m (PIR.Program (FromNameTy s2) (FromName s2) uni fun ann)
pirToOutName sng1 ((sng1 %~) -> Proved Refl) = pure
pirToOutName _ _ = throwingPIR "we do not support name conversion for PIR atm"

plcToOutName
  :: MonadError FreeVariableError m
  => SNaming s1
  -> SNaming s2
  -> PLC.Program (FromNameTy s1) (FromName s1) uni fun ann
  -> m (PLC.Program (FromNameTy s2) (FromName s2) uni fun ann)
plcToOutName sng1 ((sng1 %~) -> Proved Refl) = pure
plcToOutName SName SNamedDeBruijn = PLC.progTerm PLC.deBruijnTerm
plcToOutName SNamedDeBruijn SName = PLC.runQuoteT . PLC.progTerm PLC.unDeBruijnTerm
plcToOutName SDeBruijn SNamedDeBruijn =
  pure . PLC.programMapNames PLC.fakeTyNameDeBruijn PLC.fakeNameDeBruijn
plcToOutName SNamedDeBruijn SDeBruijn =
  pure . PLC.programMapNames PLC.unNameTyDeBruijn PLC.unNameDeBruijn
plcToOutName SName SDeBruijn =
  plcToOutName SName SNamedDeBruijn
    >=> plcToOutName SNamedDeBruijn SDeBruijn
plcToOutName SDeBruijn SName =
  plcToOutName SDeBruijn SNamedDeBruijn
    >=> plcToOutName SNamedDeBruijn SName
plcToOutName _ _ = error "this is complete, but i don't want to use -fno-warn-incomplete-patterns"

uplcToOutName
  :: MonadError FreeVariableError m
  => SNaming s1
  -> SNaming s2
  -> UPLC.UnrestrictedProgram (FromName s1) uni fun ann
  -> m (UPLC.UnrestrictedProgram (FromName s2) uni fun ann)
uplcToOutName = fmap _Wrapped . uplcToOutName'

uplcToOutName'
  :: MonadError FreeVariableError m
  => SNaming s1
  -> SNaming s2
  -> UPLC.Program (FromName s1) uni fun ann
  -> m (UPLC.Program (FromName s2) uni fun ann)
uplcToOutName' sng1 ((sng1 %~) -> Proved Refl) = pure
uplcToOutName' SName SNamedDeBruijn = UPLC.progTerm UPLC.deBruijnTerm
uplcToOutName' SNamedDeBruijn SName = PLC.runQuoteT . UPLC.progTerm UPLC.unDeBruijnTerm
uplcToOutName' SDeBruijn SNamedDeBruijn = pure . UPLC.programMapNames UPLC.fakeNameDeBruijn
uplcToOutName' SNamedDeBruijn SDeBruijn = pure . UPLC.programMapNames UPLC.unNameDeBruijn
uplcToOutName' SName SDeBruijn =
  uplcToOutName' SName SNamedDeBruijn
    >=> uplcToOutName' SNamedDeBruijn SDeBruijn
uplcToOutName' SDeBruijn SName =
  uplcToOutName' SDeBruijn SNamedDeBruijn
    >=> uplcToOutName' SNamedDeBruijn SName
uplcToOutName' _ _ = error "this is complete, but i don't want to use -fno-warn-incomplete-patterns"

-- TODO: use better, more detailed erroring
throwingPIR
  :: MonadError (PIR.Error uni fun a) m
  => Text -> b -> m c
throwingPIR = const . throwError . PIR.OptionsError

checkProgram
  :: ( e ~ PIR.Provenance (FromAnn (US_ann s))
     , MonadError (PIR.Error DefaultUni DefaultFun e) m
     )
  => SLang s
  -> FromLang s
  -> m ()
checkProgram sng p = modifyError (fmap PIR.Original) $ case sng of
  SPlc n a -> plcTypecheck n a p
  SUplc n a -> modifyError PIR.PLCError $ uplcTypecheck n a p
  SPir SName a -> pirTypecheck a p
  SData -> pure () -- data is type correct by construction
  SPir {} -> throwingPIR "PIR: Cannot typecheck non-names" ()

instance AnnInline SrcSpans where
  annAlwaysInline = mempty
  annSafeToInline = mempty
  annMayInline = mempty
