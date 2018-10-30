module Playground.Interpreter where

import           Control.Monad.Catch          (finally)
import           Control.Monad.IO.Class       (liftIO)
import           Data.Maybe                   (catMaybes)
import           Data.Text                    (unpack)
import qualified Data.Text                    as Text
import           Language.Haskell.Interpreter (GhcError, ModuleElem (Fun), MonadInterpreter, getModuleExports,
                                               loadModules, runInterpreter, setTopLevelModules, typeChecksWithDetails,
                                               typeOf)
import           Playground.API               (SourceCode (SourceCode))
import           System.Directory             (removeFile)
import           System.IO                    (readFile)
import           System.IO.Temp               (writeTempFile)

compile :: (MonadInterpreter m) => SourceCode -> m ()
compile (SourceCode s) = do
  fileName <- liftIO $ writeTempFile "." "Contract.hs" (unpack s)
  flip finally (liftIO (removeFile fileName)) $ do
    loadModules [fileName]
    setTopLevelModules ["Contract"]
    exports <- getModuleExports "Contract"
    let functionNames = catMaybes . fmap functionName $ exports
    types <- traverse typeOf functionNames
    liftIO $ print types

functionName :: ModuleElem -> Maybe String
functionName (Fun s) = Just s
functionName _       = Nothing
