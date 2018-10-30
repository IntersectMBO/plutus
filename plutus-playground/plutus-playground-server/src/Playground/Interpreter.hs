module Playground.Interpreter where

import           Control.Monad.Catch          (finally)
import           Control.Monad.IO.Class       (liftIO)
import           Data.Maybe                   (catMaybes)
import           Data.Text                    (unpack)
import qualified Data.Text                    as Text
import           Language.Haskell.Interpreter (Extension (..), GhcError, ModuleElem (Fun), MonadInterpreter,
                                               OptionVal ((:=)), getModuleExports, languageExtensions, loadModules,
                                               runInterpreter, set, setTopLevelModules, typeChecksWithDetails, typeOf)
import           Playground.API               (SourceCode (SourceCode))
import           System.Directory             (removeFile)
import           System.IO                    (readFile)
import           System.IO.Temp               (writeTempFile)

defaultExtensions =
  [ ExplicitForAll
  , ScopedTypeVariables
  , DeriveGeneric
  , StandaloneDeriving
  , DeriveLift
  , GeneralizedNewtypeDeriving
  , DeriveFunctor
  , DeriveFoldable
  , DeriveTraversable
  ]

compile :: (MonadInterpreter m) => SourceCode -> m ()
compile (SourceCode s) = do
  fileName <- liftIO $ writeTempFile "." "Contract.hs" (unpack s)
  flip finally (liftIO (removeFile fileName)) $ do
    set [languageExtensions := defaultExtensions]
    loadModules [fileName]

runFunction :: (MonadInterpreter m) => SourceCode -> m ()
runFunction (SourceCode s) = do
  fileName <- liftIO $ writeTempFile "." "Contract.hs" (unpack s)
  flip finally (liftIO (removeFile fileName)) $ do
    set [languageExtensions := defaultExtensions]
    loadModules [fileName]
    setTopLevelModules ["Contract"]
    exports <- getModuleExports "Contract"
    walletFunctions <- catMaybes <$> traverse isWalletFunction exports
    liftIO $ print walletFunctions

-- TODO: this is just a placeholder, really we want to work out how to find the
--       correct function types (or force user to declare them)
isWalletFunction :: (MonadInterpreter m) => ModuleElem -> m (Maybe ModuleElem)
isWalletFunction f@(Fun s) = do
  t <- typeOf s
  pure $
    if t == "Int -> Int"
      then Just f
      else Nothing
isWalletFunction _ = pure Nothing
