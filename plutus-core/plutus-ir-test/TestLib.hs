{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators          #-}
module TestLib where

import           Common
import           PlcTestUtils
import           PlutusPrelude

import           Control.Exception
import           Control.Monad.Except
import           Control.Monad.Reader         as Reader
import           Control.Monad.Morph
import Control.Lens hiding (transform, op)

import qualified Language.PlutusCore as PLC
import qualified Language.PlutusCore.DeBruijn as PLC
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import           Language.PlutusIR            as PIR
import           Language.PlutusIR.Compiler   as PIR
import           Language.PlutusIR.Parser     as Parser
import           Language.PlutusIR.TypeCheck
import qualified Language.UntypedPlutusCore as UPLC
import           System.FilePath              (joinPath, (</>))
import           Text.Megaparsec.Pos

import qualified Data.Text                    as T
import qualified Data.Text.IO                 as T


instance ( PLC.GShow uni, PLC.GEq uni, PLC.DefaultUni PLC.<: uni
         , PLC.Closed uni, uni `PLC.Everywhere` PrettyConst, Pretty a, Typeable a, Typeable uni, Ord a
         ) => ToTPlc (PIR.Term TyName Name uni a) uni where
    toTPlc = asIfThrown . fmap (PLC.Program () (PLC.defaultVersion ()) . void) . compileAndMaybeTypecheck True

instance ( PLC.GShow uni, PLC.GEq uni, PLC.DefaultUni PLC.<: uni , PLC.Closed uni, uni `PLC.Everywhere` PrettyConst, Pretty a, Typeable a, Typeable uni, Ord a
         ) => ToUPlc (PIR.Term TyName Name uni a) uni where
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
    :: (PLC.GShow uni, PLC.GEq uni, PLC.DefaultUni PLC.<: uni, Ord a)
    => Bool
    -> Term TyName Name uni a
    -> Except (PIR.Error uni (PIR.Provenance a)) (PLC.Term TyName Name uni (PIR.Provenance a))
compileAndMaybeTypecheck doTypecheck pir = flip runReaderT defaultCompilationCtx $ runQuoteT $ do
    compiled <- compileTerm doTypecheck pir
    when doTypecheck $ do
        -- PLC errors are parameterized over PLC.Terms, whereas PIR errors over PIR.Terms and as such, these prism errors cannot be unified.
        -- We instead run the ExceptT, collect any PLC error and explicitly lift into a PIR error by wrapping with PIR._PLCError
        plcConcrete <- runExceptT $ void $ PLC.inferType PLC.defConfig compiled
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
    where parseOrError = either (return . T.pack . show) (fmap display . op)
                         . parse parser name

ppThrow :: PrettyBy PrettyConfigPlc a => ExceptT SomeException IO a -> IO T.Text
ppThrow = fmap render . rethrow . fmap prettyPlcClassicDebug

ppCatch :: PrettyPlc a => ExceptT SomeException IO a -> IO T.Text
ppCatch value = render <$> (either (pretty . show) prettyPlcClassicDebug <$> runExceptT value)

goldenPlcFromPir :: ToTPlc a PLC.DefaultUni => Parser a -> String -> TestNested
goldenPlcFromPir = goldenPirM (\ast -> ppThrow $ do
                                p <- toTPlc ast
                                withExceptT toException $ PLC.deBruijnProgram p)

goldenPlcFromPirCatch :: ToTPlc a PLC.DefaultUni => Parser a -> String -> TestNested
goldenPlcFromPirCatch = goldenPirM (\ast -> ppCatch $ do
                                           p <- toTPlc ast
                                           withExceptT toException $ PLC.deBruijnProgram p)

goldenEvalPir :: (ToUPlc a PLC.DefaultUni) => Parser a -> String -> TestNested
goldenEvalPir = goldenPirM (\ast -> ppThrow $ runUPlc [ast])

goldenTypeFromPir :: forall a. (Pretty a, Typeable a)
                  => Parser (Term TyName Name PLC.DefaultUni a) -> String -> TestNested
goldenTypeFromPir = goldenPirM (\ast -> ppThrow $
                                withExceptT (toException :: PIR.Error PLC.DefaultUni a -> SomeException) $ runQuoteT $ inferType defConfig ast)

goldenTypeFromPirCatch :: forall a. (Pretty a, Typeable a)
                  => Parser (Term TyName Name PLC.DefaultUni a) -> String -> TestNested
goldenTypeFromPirCatch = goldenPirM (\ast -> ppCatch $
                                withExceptT (toException :: PIR.Error PLC.DefaultUni a -> SomeException) $ runQuoteT $ inferType defConfig ast)

-- TODO: perhaps move to Common.hs
instance Pretty SourcePos where
    pretty = pretty . sourcePosPretty
