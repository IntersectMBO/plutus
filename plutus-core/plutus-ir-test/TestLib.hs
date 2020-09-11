{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
module TestLib where

import           Common
import           PlcTestUtils
import           PlutusPrelude

import           Control.Exception
import           Control.Monad.Except
import           Control.Monad.Reader         as Reader

import qualified Language.PlutusCore.DeBruijn as PLC
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.Universe as PLC
import           Language.PlutusIR            as PIR
import           Language.PlutusIR.Error      as PIR
import           Language.PlutusIR.Parser     as Parser
import           Language.PlutusIR.TypeCheck
import           System.FilePath              (joinPath, (</>))
import           Text.Megaparsec.Pos

import qualified Data.Text                    as T
import qualified Data.Text.IO                 as T

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

goldenPlcFromPir :: GetProgram a PLC.DefaultUni => Parser a -> String -> TestNested
goldenPlcFromPir = goldenPirM (\ast -> ppThrow $ do
                                p <- getProgram ast
                                withExceptT toException $ PLC.deBruijnProgram p)

goldenPlcFromPirCatch :: GetProgram a PLC.DefaultUni => Parser a -> String -> TestNested
goldenPlcFromPirCatch = goldenPirM (\ast -> ppCatch $ do
                                           p <- getProgram ast
                                           withExceptT toException $ PLC.deBruijnProgram p)

goldenEvalPir :: (GetProgram a PLC.DefaultUni) => Parser a -> String -> TestNested
goldenEvalPir = goldenPirM (\ast -> ppThrow $ runPlc [ast])


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
