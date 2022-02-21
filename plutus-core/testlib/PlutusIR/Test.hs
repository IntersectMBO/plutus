{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
module PlutusIR.Test where

import PlutusPrelude
import Test.Tasty.Extras

import Control.Exception
import Control.Lens hiding (op, transform)
import Control.Monad.Except
import Control.Monad.Morph
import Control.Monad.Reader as Reader

import PlutusCore qualified as PLC
import PlutusCore.Name
import PlutusCore.Pretty
import PlutusCore.Pretty qualified as PLC
import PlutusCore.Quote
import PlutusCore.Test
import PlutusIR as PIR
import PlutusIR.Compiler as PIR
import PlutusIR.Parser as Parser
import PlutusIR.TypeCheck
import System.FilePath (joinPath, (</>))
import UntypedPlutusCore qualified as UPLC

import Data.Text qualified as T
import Data.Text.IO qualified as T

import Text.Megaparsec.Error qualified as MP


instance ( PLC.GShow uni, PLC.GEq uni, PLC.Typecheckable uni fun
         , PLC.Closed uni, uni `PLC.Everywhere` PrettyConst, Pretty fun, Pretty a
         , Typeable a, Typeable uni, Typeable fun, Ord a
         ) => ToTPlc (PIR.Term TyName Name uni fun a) uni fun where
    toTPlc = asIfThrown . fmap (PLC.Program () (PLC.defaultVersion ()) . void) . compileAndMaybeTypecheck True

instance ( PLC.GShow uni, PLC.GEq uni, PLC.Typecheckable uni fun
         , PLC.Closed uni, uni `PLC.Everywhere` PrettyConst, Pretty fun, Pretty a
         , Typeable a, Typeable uni, Typeable fun, Ord a
         ) => ToUPlc (PIR.Term TyName Name uni fun a) uni fun where
    toUPlc t = do
        p' <- toTPlc t
        pure $ UPLC.eraseProgram p'

-- | Adapt an computation that keeps its errors in an 'Except' into one that looks as if it caught them in 'IO'.
asIfThrown
    :: Exception e
    => Except e a
    -> ExceptT SomeException IO a
asIfThrown = withExceptT SomeException . hoist (pure . runIdentity)

compileAndMaybeTypecheck
    :: (PLC.GEq uni, PLC.Typecheckable uni fun, Ord a, PLC.Pretty fun, PLC.Closed uni, PLC.GShow uni, uni `PLC.Everywhere` PLC.PrettyConst, PLC.Pretty a)
    => Bool
    -> Term TyName Name uni fun a
    -> Except (PIR.Error uni fun (PIR.Provenance a)) (PLC.Term TyName Name uni fun (PIR.Provenance a))
compileAndMaybeTypecheck doTypecheck pir = do
    tcConfig <- PLC.getDefTypeCheckConfig noProvenance
    let pirCtx = toDefaultCompilationCtx tcConfig & if doTypecheck
                                                    then id
                                                    else set ccTypeCheckConfig Nothing
    flip runReaderT pirCtx $ runQuoteT $ do
        compiled <- compileTerm pir
        when doTypecheck $ do
            -- PLC errors are parameterized over PLC.Terms, whereas PIR errors over PIR.Terms and as such, these prism errors cannot be unified.
            -- We instead run the ExceptT, collect any PLC error and explicitly lift into a PIR error by wrapping with PIR._PLCError
            plcConcrete <- runExceptT $ void $ PLC.inferType tcConfig compiled
            liftEither $ first (view (re _PLCError)) plcConcrete
        pure compiled

withGoldenFileM :: String -> (T.Text -> IO T.Text) -> TestNested
withGoldenFileM name op = do
    dir <- currentDir
    let testFile = dir </> name
        goldenFile = dir </> name ++ ".golden"
    return $ goldenVsTextM name goldenFile (op =<< T.readFile testFile)
    where currentDir = joinPath <$> ask

goldenPir :: Pretty b => (a -> b) -> Parser a -> String -> TestNested
goldenPir op = goldenPirM (return . op)

goldenPirM :: Pretty b => (a -> IO b) -> Parser a -> String -> TestNested
goldenPirM op parser name = withGoldenFileM name parseOrError
    where parseOrError = either (return . T.pack . MP.errorBundlePretty) (fmap display . op)
                         . parse parser name

ppThrow :: PrettyPlc a => ExceptT SomeException IO a -> IO T.Text
ppThrow = fmap render . rethrow . fmap prettyPlcClassicDebug

ppCatch :: PrettyPlc a => ExceptT SomeException IO a -> IO T.Text
ppCatch value = render <$> (either (pretty . show) prettyPlcClassicDebug <$> runExceptT value)

goldenPlcFromPir ::
    ToTPlc a PLC.DefaultUni PLC.DefaultFun =>
    Parser a -> String -> TestNested
goldenPlcFromPir = goldenPirM (\ast -> ppThrow $ do
                                p <- toTPlc ast
                                withExceptT @_ @PLC.FreeVariableError toException $ traverseOf PLC.progTerm PLC.deBruijnTerm p)

goldenPlcFromPirCatch ::
    ToTPlc a PLC.DefaultUni PLC.DefaultFun =>
    Parser a -> String -> TestNested
goldenPlcFromPirCatch = goldenPirM (\ast -> ppCatch $ do
                                           p <- toTPlc ast
                                           withExceptT @_ @PLC.FreeVariableError toException $ traverseOf PLC.progTerm PLC.deBruijnTerm p)

goldenEvalPir ::
    ToUPlc a PLC.DefaultUni PLC.DefaultFun =>
    Parser a -> String -> TestNested
goldenEvalPir = goldenPirM (\ast -> ppThrow $ runUPlc [ast])

goldenTypeFromPir ::
    forall a. (Pretty a, Typeable a) =>
    a ->
    Parser (Term TyName Name PLC.DefaultUni PLC.DefaultFun a) ->
    String ->
    TestNested
goldenTypeFromPir x =
    goldenPirM $ \ast -> ppThrow $
        withExceptT (toException :: PIR.Error PLC.DefaultUni PLC.DefaultFun a -> SomeException) $
            runQuoteT $ do
                tcConfig <- getDefTypeCheckConfig x
                inferType tcConfig ast

goldenTypeFromPirCatch ::
    forall a. (Pretty a, Typeable a) =>
    a ->
    Parser (Term TyName Name PLC.DefaultUni PLC.DefaultFun a) ->
    String ->
    TestNested
goldenTypeFromPirCatch x =
    goldenPirM $ \ast -> ppCatch $
        withExceptT (toException :: PIR.Error PLC.DefaultUni PLC.DefaultFun a -> SomeException) $
            runQuoteT $ do
                tcConfig <- getDefTypeCheckConfig x
                inferType tcConfig ast
