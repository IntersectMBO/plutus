{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module TestLib where

import           Common
import           PlcTestUtils
import           PlutusPrelude                hiding ((</>))

import           Control.Exception
import           Control.Monad.Except
import           Control.Monad.Reader         as Reader

import qualified Language.PlutusCore.DeBruijn as PLC
import           Language.PlutusCore.Pretty
import           Language.PlutusIR.Parser     as Parser

import           System.FilePath              (joinPath, (</>))

import           Text.Megaparsec.Error        as Megaparsec

import qualified Data.Text                    as T
import qualified Data.Text.IO                 as T

withGoldenFileM :: String -> (T.Text -> IO T.Text) -> TestNested
withGoldenFileM name op = do
    filename <- (</> (name ++ ".plc")) <$> currentDir
    nestedGoldenVsTextM name (op =<< T.readFile filename)
    where currentDir = joinPath <$> ask

goldenPir :: Pretty b => (a -> b) -> Parser a -> String -> TestNested
goldenPir op = goldenPirM (return . op)

goldenPirM :: Pretty b => (a -> IO b) -> Parser a -> String -> TestNested
goldenPirM op parser name = withGoldenFileM name parseOrError
    where parseOrError = either (return . T.pack . parseErrorPretty) (fmap prettyText . op)
                         . parse parser name

ppThrow :: PrettyBy PrettyConfigPlc a => ExceptT SomeException IO a -> IO T.Text
ppThrow = fmap docText . rethrow . fmap prettyPlcClassicDebug

ppCatch :: PrettyPlc a => ExceptT SomeException IO a -> IO T.Text
ppCatch value = docText <$> (either (pretty . show) prettyPlcClassicDebug <$> runExceptT value)

goldenPlcFromPir :: GetProgram a => Parser a -> String -> TestNested
goldenPlcFromPir = goldenPirM (\ast -> ppThrow $ do
                                p <- getProgram ast
                                withExceptT toException $ PLC.deBruijnProgram p)

goldenPlcFromPirCatch :: GetProgram a => Parser a -> String -> TestNested
goldenPlcFromPirCatch = goldenPirM (\ast -> ppCatch $ do
                                           p <- getProgram ast
                                           withExceptT toException $ PLC.deBruijnProgram p)

goldenEvalPir :: (GetProgram a) => Parser a -> String -> TestNested
goldenEvalPir = goldenPirM (\ast -> ppThrow $ runPlc [ast])
