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
  Text ->
  m (InterpreterResult String)
runscript handle file timeout script = do
  liftIO $ Text.hPutStr handle script
  liftIO $ hFlush handle
  runghc timeout runghcOpts file

compile ::
  ( Show t,
    TimeUnit t,
    MonadMask m,
    MonadIO m,
    MonadError InterpreterError m
  ) =>
  t ->
  SourceCode ->
  m (InterpreterResult String)
compile timeout source =
  do
    avoidUnsafe source
    withSystemTempDirectory "web-ghc-work" $ \dir -> do
      let file = dir </> "Main.hs"
      withFile file ReadWriteMode $ \handle -> runscript handle file timeout . Newtype.unpack $ source

runghcOpts :: [String]
runghcOpts =
  [ "-XDataKinds",
    "-XDeriveAnyClass",
    "-XDeriveGeneric",
    "-XDerivingStrategies",
    "-XExplicitNamespaces",
    "-XFlexibleContexts",
    "-XGeneralizedNewtypeDeriving",
    "-XMultiParamTypeClasses",
    "-XNamedFieldPuns",
    "-XNoImplicitPrelude",
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
