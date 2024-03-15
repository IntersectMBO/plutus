{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
-- wrongly complains, will decide later how to handle it
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
module AnyProgram.Compile
    ( compileProgram
    , toOutAnn
    ) where

import Types
import GetOpt
import AnyProgram.With

import PlutusCore.Default
import PlutusCore qualified as PLC
import PlutusCore.Error as PLC
import PlutusCore.MkPlc
import PlutusCore.DeBruijn qualified as PLC
import PlutusCore.Compiler qualified as PLC
import PlutusIR qualified as PIR
import PlutusIR.TypeCheck qualified as PIR
import PlutusIR.Error qualified as PIR
import PlutusIR.Compiler qualified as PIR
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Check.Uniques qualified as UPLC

import PlutusPrelude hiding ((%~))
import Data.Singletons.Decide
import Control.Monad.Reader
import Control.Lens hiding ((%~))
import Control.Monad.Except
import Control.Monad.Error.Lens

compileProgram :: (?opts :: Opts, e ~ (PIR.Provenance (FromAnn (US_ann s1))), -- Here we use the erroring of the original term's annotation
                  MonadError (PIR.Error DefaultUni DefaultFun e) m)
               => SLang s1
               -> SLang s2
               -> FromLang s1
               -> m (FromLang s2)
compileProgram = curry $ \case
    -- exclude all pir-debruijn input&output combinations
    ----------------------------------------
    (SPir SNamedDeBruijn _, _) -> const $ throwing PIR._Error $ PIR.OptionsError "pir input cannot be debruijn"
    (SPir SDeBruijn _, _ ) -> const $ throwing PIR._Error $ PIR.OptionsError "pir input cannot be nameddebruijn"
    (_, SPir SDeBruijn _) -> const $ throwing PIR._Error $ PIR.OptionsError "pir out cannot be debruijn"
    (_, SPir SNamedDeBruijn _) -> const $ throwing PIR._Error $ PIR.OptionsError "pir out cannot be nameddebruijn"

    -- pir to plc
    ----------------------------------------
    (SPir n1@SName a1, SPlc n2 SUnit) -> withOrdA a1 $ withPrettyA a1 $
        -- Note: PIR.compileProgram subsumes pir typechecking
        (PLC.runQuoteT . flip runReaderT (PIR.toDefaultCompilationCtx undefined) . PIR.compileProgram)
        >=> plcToOutName n1 n2
        -- completely drop annotations for now
        >=> pure . void

    -- note to self: this restriction is because of PIR.Provenance appearing in the output
    (SPir SName _, SPlc _ _) -> const $ throwing PIR._Error $ PIR.OptionsError "only support unit-ann output for now"

    -- plc to pir (a special case of embedding, since plc is subset of pir)
    ----------------------------------------
    (sng1@(SPlc _n1 a1), SPir n2 a2) ->
            -- first self-"compile" to plc (just for reusing code)
            compileProgram sng1 (SPlc n2 a1)
        >=> pure . embedProgram
        -- here we also run the pir typechecker, and pir optimiser
        >=> compileProgram (SPir n2 a1) (SPir n2 a2)

    -- pir to uplc
    ----------------------------------------
    (sng1@(SPir _n1 a1), sng2@(SUplc n2 _a2)) ->
        -- intermediate through plc==sng12
        let sng12 = SPlc n2 a1
        in       compileProgram sng1 sng12
             >=> compileProgram sng12 sng2

    -- plc to uplc
    ----------------------------------------
    (sng1@(SPlc _n1 _a1), SUplc n2 a2) ->
            -- first self-"compile" to plc (just for reusing code)
            compileProgram sng1 (SPlc n2 a2)
        -- PLC.compileProgram subsumes uplcOptimise
        >=> (PLC.runQuoteT . flip runReaderT PLC.defaultCompilationOpts . plcToUplcViaName n2 PLC.compileProgram)
        >=> pure . UPLC.UnrestrictedProgram

    -- self-lang to self-lang patterns
    ----------------------------------------
    (SPir n1@SName a1, SPir n2@SName a2) ->
        through (modifyError (fmap PIR.Original) . pirTypecheck a1)
        -- TODO: optimise
        >=> pirToOutName n1 n2
        >=> toOutAnn a1 a2
    (SPlc n1 a1, SPlc n2 a2) ->
        through (modifyError (fmap PIR.Original . PIR.PLCError) . plcTypecheck n1 a1)
        >=> plcToOutName n1 n2
        >=> toOutAnn a1 a2
    (SUplc n1 a1, SUplc n2 a2) ->
        through (modifyError (fmap PIR.Original) . uplcTypecheck n1 a1)
        >=> uplcOptimise n1
        >=> uplcToOutName n1 n2
        >=> toOutAnn a1 a2

    (_, _) -> const $ throwing PIR._Error $ PIR.OptionsError "not implemented yet"

embedProgram :: PLC.Program tyname name uni fun ann -> PIR.Program tyname name uni fun ann
embedProgram (PLC.Program a v t) = PIR.Program a v $ embed t

toOutAnn :: (Functor f, PIR.AsError e uni fun a, MonadError e m)
         => SAnn s1
         -> SAnn s2
         -> f (FromAnn s1)
         -> m (f (FromAnn s2))
toOutAnn sng1 ((sng1 %~) -> Proved Refl) = pure
toOutAnn _ SUnit = pure . void
toOutAnn _ _ = const $ throwing PIR._Error $ PIR.OptionsError "cannot convert annotation"

-- MAYBE: All of the following could be unified under a ProgramLike typeclass.
-- or by some singletons type-level programming

pirTypecheck :: (PIR.AsTypeErrorExt e DefaultUni (FromAnn a)
               ,PIR.AsTypeError e (PIR.Term UPLC.TyName UPLC.Name DefaultUni DefaultFun ()) DefaultUni DefaultFun (FromAnn a), MonadError e m)
             => SAnn a
             -> PIR.Program PLC.TyName PLC.Name DefaultUni DefaultFun (FromAnn a)
             -> m ()
pirTypecheck sngA p = PLC.runQuoteT $ do
    tcConfig <- withMonoidA sngA $ PIR.getDefTypeCheckConfig mempty
    void $ PIR.inferTypeOfProgram tcConfig p

plcToUplcViaName :: (PLC.MonadQuote m, PLC.AsFreeVariableError e, MonadError e m)
            => SNaming n
            -> (PLC.Program PLC.TyName PLC.Name uni fun a -> m (UPLC.Program PLC.Name uni fun a))
            -> PLC.Program (FromNameTy n) (FromName n) uni fun a
            -> m (UPLC.Program (FromName n) uni fun a)
plcToUplcViaName sngN act = case sngN of
    SName -> act
    SNamedDeBruijn -> plcToName sngN act
                     >=> UPLC.progTerm UPLC.deBruijnTerm
    SDeBruijn -> plcToName sngN act
                >=> UPLC.progTerm UPLC.deBruijnTerm
                >=> pure . UPLC.programMapNames PLC.unNameDeBruijn

plcToName :: (PLC.MonadQuote m, PLC.AsFreeVariableError e, MonadError e m)
          => SNaming n
          -> (PLC.Program PLC.TyName PLC.Name uni fun a -> m x)
          -> (PLC.Program (FromNameTy n) (FromName n) uni fun a -> m x)
plcToName sngN act = case sngN of
    SName -> act
    SNamedDeBruijn -> PLC.progTerm PLC.unDeBruijnTerm
                      >=> act
    SDeBruijn -> pure . PLC.programMapNames PLC.fakeTyNameDeBruijn PLC.fakeNameDeBruijn
                >=> plcToName SNamedDeBruijn act

uplcViaName :: (PLC.MonadQuote m, PLC.AsFreeVariableError e, MonadError e m)
            => (UPLC.Program PLC.Name uni fun a -> m (UPLC.Program PLC.Name uni fun a))
            -> SNaming n
            -> UPLC.Program (FromName n) uni fun a
            -> m (UPLC.Program (FromName n) uni fun a)
uplcViaName act sngN = case sngN of
    SName -> act
    SNamedDeBruijn -> UPLC.progTerm UPLC.unDeBruijnTerm
                    >=> act
                    >=> UPLC.progTerm UPLC.deBruijnTerm
    SDeBruijn -> pure . UPLC.programMapNames UPLC.fakeNameDeBruijn
                >=> uplcViaName act SNamedDeBruijn
                >=> pure . UPLC.programMapNames UPLC.unNameDeBruijn

plcTypecheck :: (PLC.AsTypeError
                          e
                          -- errors remain with names
                          (PLC.Term PLC.TyName PLC.Name DefaultUni DefaultFun ())
                          DefaultUni
                          DefaultFun
                          (FromAnn a)
               , PLC.AsFreeVariableError e
               , MonadError e m
               )
             => SNaming n
             -> SAnn a
             -> PLC.Program (FromNameTy n) (FromName n) DefaultUni DefaultFun (FromAnn a)
             -> m ()
plcTypecheck sngN sngA p = PLC.runQuoteT $ do
    tcConfig <- withMonoidA sngA $ PLC.getDefTypeCheckConfig mempty
    void $ plcToName sngN (PLC.inferTypeOfProgram tcConfig) p

uplcOptimise :: (?opts :: Opts, PLC.AsFreeVariableError e, MonadError e m)
             => SNaming n1
             -> UPLC.UnrestrictedProgram (FromName n1) DefaultUni DefaultFun a
             -> m (UPLC.UnrestrictedProgram (FromName n1) DefaultUni DefaultFun a)
uplcOptimise =
    case _optimiseLvl ?opts of
        NoOptimise -> const pure -- short-circuit to avoid renaming
        safeOrUnsafe ->
                let sOpts = UPLC.defaultSimplifyOpts &
                                case safeOrUnsafe of
                                  SafeOptimise -> set UPLC.soConservativeOpts True
                                  UnsafeOptimise -> id
                in fmap PLC.runQuoteT
                   . _Wrapped
                   . uplcViaName (UPLC.simplifyProgram sOpts)


-- | We do not have a typechecker for uplc, but we could pretend that scopecheck is a "typechecker"
uplcTypecheck :: forall sN sA uni fun e m
              . (PLC.AsFreeVariableError e, PLC.AsUniqueError e (FromAnn sA), MonadError e m)
              => SNaming sN
              -> SAnn sA
              -> UPLC.UnrestrictedProgram (FromName sN) uni fun (FromAnn sA)
              -> m ()
uplcTypecheck sngN sngA ast = case sngN of
    SName -> withOrdA sngA $ UPLC.checkProgram (const True) (ast ^. _Wrapped)
    -- TODO: deduplicate
    SDeBruijn -> UPLC.checkScope (ast ^. _Wrapped. UPLC.progTerm)
    -- TODO: deduplicate
    SNamedDeBruijn -> UPLC.checkScope (ast ^. _Wrapped. UPLC.progTerm)


-- | Placed here just for uniformity, not really needed
pirToOutName :: (PIR.AsError e uni fun a, MonadError e m)
             => SNaming s1
             -> SNaming s2
             -> PIR.Program (FromNameTy s1) (FromName s1) uni fun ann
             -> m (PIR.Program (FromNameTy s2) (FromName s2) uni fun ann)
pirToOutName sng1 ((sng1 %~) -> Proved Refl) = pure
pirToOutName _ _ = const $
    throwing PIR._Error $ PIR.OptionsError "we do not support name conversion for PIR atm"

plcToOutName :: (PLC.AsFreeVariableError e, MonadError e m)
             => SNaming s1
             -> SNaming s2
             -> PLC.Program (FromNameTy s1) (FromName s1) uni fun ann
             -> m (PLC.Program (FromNameTy s2) (FromName s2) uni fun ann)
plcToOutName sng1 ((sng1 %~) -> Proved Refl) = pure
plcToOutName SName SNamedDeBruijn = PLC.progTerm PLC.deBruijnTerm
plcToOutName SNamedDeBruijn SName = PLC.runQuoteT . PLC.progTerm PLC.unDeBruijnTerm
plcToOutName SDeBruijn SNamedDeBruijn = pure . PLC.programMapNames PLC.fakeTyNameDeBruijn PLC.fakeNameDeBruijn
plcToOutName SNamedDeBruijn SDeBruijn = pure . PLC.programMapNames PLC.unNameTyDeBruijn PLC.unNameDeBruijn
plcToOutName SName SDeBruijn = plcToOutName SName SNamedDeBruijn
                             >=> plcToOutName SNamedDeBruijn SDeBruijn
plcToOutName SDeBruijn SName = plcToOutName SDeBruijn SNamedDeBruijn
                           >=> plcToOutName SNamedDeBruijn SName

uplcToOutName :: (PLC.AsFreeVariableError e, MonadError e m)
              => SNaming s1
              -> SNaming s2
              -> UPLC.UnrestrictedProgram (FromName s1) uni fun ann
              -> m (UPLC.UnrestrictedProgram (FromName s2) uni fun ann)
uplcToOutName = fmap _Wrapped . uplcToOutName'

uplcToOutName' :: (PLC.AsFreeVariableError e, MonadError e m)
               => SNaming s1
               -> SNaming s2
               -> UPLC.Program (FromName s1) uni fun ann
               -> m (UPLC.Program (FromName s2) uni fun ann)
uplcToOutName' sng1 ((sng1 %~) -> Proved Refl) = pure
uplcToOutName' SName SNamedDeBruijn = UPLC.progTerm UPLC.deBruijnTerm
uplcToOutName' SNamedDeBruijn SName = PLC.runQuoteT . UPLC.progTerm UPLC.unDeBruijnTerm
uplcToOutName' SDeBruijn SNamedDeBruijn = pure . UPLC.programMapNames UPLC.fakeNameDeBruijn
uplcToOutName' SNamedDeBruijn SDeBruijn = pure . UPLC.programMapNames UPLC.unNameDeBruijn
uplcToOutName' SName SDeBruijn = uplcToOutName' SName SNamedDeBruijn
                             >=> uplcToOutName' SNamedDeBruijn SDeBruijn
uplcToOutName' SDeBruijn SName = uplcToOutName' SDeBruijn SNamedDeBruijn
                           >=> uplcToOutName' SNamedDeBruijn SName
