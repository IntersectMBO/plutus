{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

module Interpreter where

import           Control.Monad.Catch          (MonadMask)
import           Control.Monad.Error.Class    (MonadError)
import           Control.Monad.IO.Class       (MonadIO, liftIO)
import qualified Control.Newtype.Generics     as Newtype
import           Data.Text                    (Text)
import qualified Data.Text.IO                 as Text
import           Data.Time.Units              (Second, TimeUnit)
import           Language.Haskell.Interpreter (InterpreterError, InterpreterResult, SourceCode, avoidUnsafe, runghc)
import           System.FilePath              ((</>))
import           System.IO                    (Handle, IOMode (ReadWriteMode), hFlush)
import           System.IO.Extras             (withFile)
import           System.IO.Temp               (withSystemTempDirectory)

maxInterpretationTime :: Second
maxInterpretationTime = 80

runscript ::
  ( Show t,
    TimeUnit t,
    MonadMask m,
    MonadIO m,
    MonadError InterpreterError m
  ) =>
  Handle ->
  FilePath ->
  t ->
  Bool ->
  Text ->
  m (InterpreterResult String)
runscript handle file timeout implicitPrelude script = do
  liftIO $ Text.hPutStr handle script
  liftIO $ hFlush handle
  runghc timeout (runghcOpts implicitPrelude) file

compile ::
  ( Show t,
    TimeUnit t,
    MonadMask m,
    MonadIO m,
    MonadError InterpreterError m
  ) =>
  t ->
  Bool ->
  SourceCode ->
  m (InterpreterResult String)
compile timeout implicitPrelude source =
  do
    avoidUnsafe source
    withSystemTempDirectory "web-ghc-work" $ \dir -> do
      let file = dir </> "Main.hs"
      withFile file ReadWriteMode $ \handle -> runscript handle file timeout implicitPrelude . Newtype.unpack $ source

runghcOpts :: Bool -> [String]
runghcOpts implicitPrelude =
  [ "-XDataKinds",
    "-XDeriveAnyClass",
    "-XDeriveGeneric",
    "-XDerivingStrategies",
    "-XExplicitNamespaces",
    "-XFlexibleContexts",
    "-XGeneralizedNewtypeDeriving",
    "-XMultiParamTypeClasses",
    "-XNamedFieldPuns",
    "-XNumericUnderscores",
    "-XOverloadedStrings",
    "-XRecordWildCards",
    "-XScopedTypeVariables",
    "-XTemplateHaskell",
    "-XTypeApplications",
    "-XTypeFamilies",
    "-XTypeOperators",
    -- See Plutus Tx readme
    -- runghc is interpreting our code
    "-fno-ignore-interface-pragmas",
    "-fobject-code"
  ]
    <> if implicitPrelude then [] else ["-XNoImplicitPrelude"]
