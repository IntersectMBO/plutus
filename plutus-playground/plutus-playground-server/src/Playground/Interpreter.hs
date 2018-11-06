{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

module Playground.Interpreter where

import           Control.Monad.Catch          (finally, throwM)
import           Control.Monad.IO.Class       (liftIO)
import           Control.Monad.Trans.Class    (lift)
import           Control.Monad.Trans.State    (StateT, evalStateT, get, put)
import qualified Control.Newtype.Generics     as Newtype
import           Data.Aeson                   (FromJSON, Result (Success), ToJSON, Value, fromJSON)
import qualified Data.Aeson                   as JSON
import           Data.Bifunctor               (second)
import qualified Data.ByteString.Lazy.Char8   as BSL
import           Data.List                    (intercalate)
import           Data.Maybe                   (catMaybes, fromJust)
import           Data.Monoid                  ((<>))
import           Data.Swagger                 (Schema)
import           Data.Swagger.Schema          (ToSchema, declareNamedSchema, toSchema)
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import           Data.Typeable                (TypeRep, Typeable, typeRepArgs)
import qualified Data.Typeable                as DT
import           GHC.Generics                 (Generic)
import           Language.Haskell.Interpreter (Extension (..), GhcError, InterpreterError (UnknownError),
                                               ModuleElem (Fun), ModuleName, MonadInterpreter, OptionVal ((:=)), as,
                                               getLoadedModules, getModuleExports, interpret, languageExtensions,
                                               loadModules, runInterpreter, set, setImportsQ, setTopLevelModules,
                                               typeChecksWithDetails, typeOf)
import qualified Language.Haskell.TH          as TH
import           Playground.API               (Evaluation (program, sourceCode), Expression (Expression), Fn (Fn),
                                               FunctionSchema (FunctionSchema), Program, SourceCode, blockchain)
import qualified Playground.TH                as TH
import           System.Directory             (removeFile)
import           System.IO                    (readFile)
import           System.IO.Temp               (writeTempFile)
import           Text.Read                    (readMaybe)
import qualified Type.Reflection              as TR
import           Wallet.API                   (WalletAPI)
import           Wallet.Emulator.Types        (AssertionError, EmulatedWalletApi, EmulatorState (emChain), Trace,
                                               Wallet (Wallet, getWallet), runTraceChain, runTraceTxPool, walletAction)
import           Wallet.UTXO                  (Blockchain)

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

loadSource :: (MonadInterpreter m) => FilePath -> (ModuleName -> m a) -> m a
loadSource fileName action =
  flip finally (liftIO (removeFile fileName)) $ do
    set [languageExtensions := defaultExtensions]
    loadModules [fileName]
    (m:_) <- getLoadedModules
    setTopLevelModules [m]
    action m

compile :: (MonadInterpreter m) => SourceCode -> m [FunctionSchema]
compile s = do
  fileName <-
    liftIO $ writeTempFile "." "Contract.hs" (Text.unpack . Newtype.unpack $ s)
  loadSource fileName $ \moduleName -> do
    exports <- getModuleExports moduleName
    walletFunctions <- catMaybes <$> traverse isWalletFunction exports
    traverse getSchema walletFunctions

{-# ANN getSchema ("HLint: ignore" :: String) #-}

getSchema :: (MonadInterpreter m) => ModuleElem -> m FunctionSchema
getSchema (Fun m) = interpret m (as :: FunctionSchema)
getSchema _ =
  error "Trying to get a schema by calling something other than a function"

runFunction :: (MonadInterpreter m) => Evaluation -> m Blockchain
runFunction evaluation = do
  fileName <-
    liftIO $
    writeTempFile
      "."
      "Contract.hs"
      (Text.unpack . Newtype.unpack . sourceCode $ evaluation)
  loadSource fileName $ \_ -> do
    setImportsQ
      [("Playground.Interpreter", Nothing), ("Wallet.Emulator", Nothing)]
    res <-
      interpret (mkExpr evaluation) (as :: Either AssertionError Blockchain)
    case res of
      Left e           -> throwM . UnknownError $ show e
      Right blockchain -> pure blockchain

runTrace ::
     Blockchain -> Trace EmulatedWalletApi a -> Either AssertionError Blockchain
runTrace blockchain action =
  let (eRes, newState) = runTraceChain blockchain action
   in case eRes of
        Right _ -> Right . emChain $ newState
        Left e  -> Left e

mkExpr :: Evaluation -> String
mkExpr evaluation =
  "runTrace (decode " <> jsonToString (blockchain evaluation) <> ") (" <>
  (intercalate " >> " $
   fmap (\expression -> walletActionExpr expression) (program evaluation)) <>
  ")"

walletActionExpr :: Expression -> String
walletActionExpr (Expression (Fn f) wallet args) =
  "(walletAction (" <> show wallet <> ") (" <>
  mkApplyExpr (Text.unpack f) (fmap jsonToString args) <>
  "))"

mkApplyExpr :: String -> [String] -> String
mkApplyExpr functionName [] = functionName
mkApplyExpr functionName [a] = "apply1 " <> functionName <> " " <> a
mkApplyExpr functionName [a, b] = "apply2" <+> functionName <+> a <+> b
mkApplyExpr functionName [a, b, c] = "apply3" <+> functionName <+> a <+> b <+> c
mkApplyExpr functionName [a, b, c, d] =
  "apply4" <+> functionName <+> a <+> b <+> c <+> d
mkApplyExpr functionName [a, b, c, d, e] =
  "apply5" <+> functionName <+> a <+> b <+> c <+> d <+> e
mkApplyExpr functionName [a, b, c, d, e, f] =
  "apply6" <+> functionName <+> a <+> b <+> c <+> d <+> e <+> f
mkApplyExpr functionName [a, b, c, d, e, f, g] =
  "apply7" <+> functionName <+> a <+> b <+> c <+> d <+> e <+> f <+> g

(<+>) :: String -> String -> String
a <+> b = a <> " " <> b

jsonToString :: ToJSON a => a -> String
jsonToString = show . JSON.encode

-- | This will throw an exception if it cannot decode the json however it should
--   never do this as long as it is only called in places where we have already
--   decoded and encoded the value since it came from an HTTP API call
{-# ANN decode ("HLint: ignore" :: String) #-}

decode :: FromJSON a => String -> a
decode = fromJust . JSON.decode . BSL.pack

apply1 :: FromJSON a => (a -> b) -> String -> b
apply1 fun v = fun (decode v)

apply2 :: (FromJSON a, FromJSON b) => (a -> b -> c) -> String -> String -> c
apply2 fun a b = fun (decode a) (decode b)

apply3 ::
     (FromJSON a, FromJSON b, FromJSON c)
  => (a -> b -> c -> d)
  -> (String, String, String)
  -> d
apply3 fun (a, b, c) = fun (decode a) (decode b) (decode c)

apply4 ::
     (FromJSON a, FromJSON b, FromJSON c, FromJSON d)
  => (a -> b -> c -> d -> e)
  -> (String, String, String, String)
  -> e
apply4 fun (a, b, c, d) = fun (decode a) (decode b) (decode c) (decode d)

apply5 ::
     (FromJSON a, FromJSON b, FromJSON c, FromJSON d, FromJSON e)
  => (a -> b -> c -> d -> e -> f)
  -> (String, String, String, String, String)
  -> f
apply5 fun (a, b, c, d, e) =
  fun (decode a) (decode b) (decode c) (decode d) (decode e)

apply6 ::
     (FromJSON a, FromJSON b, FromJSON c, FromJSON d, FromJSON e, FromJSON f)
  => (a -> b -> c -> d -> e -> f -> g)
  -> (String, String, String, String, String, String)
  -> g
apply6 fun (a, b, c, d, e, f) =
  fun (decode a) (decode b) (decode c) (decode d) (decode e) (decode f)

apply7 ::
     ( FromJSON a
     , FromJSON b
     , FromJSON c
     , FromJSON d
     , FromJSON e
     , FromJSON f
     , FromJSON g
     )
  => (a -> b -> c -> d -> e -> f -> g -> h)
  -> (String, String, String, String, String, String, String)
  -> h
apply7 fun (a, b, c, d, e, f, g) =
  fun
    (decode a)
    (decode b)
    (decode c)
    (decode d)
    (decode e)
    (decode f)
    (decode g)

isWalletFunction :: (MonadInterpreter m) => ModuleElem -> m (Maybe ModuleElem)
isWalletFunction f@(Fun s) = do
  t <- typeOf s
  pure $
    if t == "FunctionSchema"
      then Just f
      else Nothing
isWalletFunction _ = pure Nothing

------------------------------------------------------------
data CompilationError = CompilationError
  { filename :: !Text
  , row      :: !Int
  , column   :: !Int
  , text     :: ![Text]
  } deriving (Show, Eq, Generic)

parseErrorText :: Text -> Maybe CompilationError
parseErrorText =
  evalStateT $ do
    filename <- consumeTo ":"
    rowStr <- consumeTo ":"
    columnStr <- consumeTo ":"
    text <- Text.lines <$> consume
  --
    row <- lift $ readMaybe $ Text.unpack rowStr
    column <- lift $ readMaybe $ Text.unpack columnStr
    pure CompilationError {..}

consumeTo :: Monad m => Text -> StateT Text m Text
consumeTo needle = do
  (before, after) <- breakWith needle <$> get
  put after
  pure before

consume :: (Monad m, Monoid s) => StateT s m s
consume = get <* put mempty

-- | Light `Data.Text.breakOn`, but consumes the breakpoint text (the 'needle').
breakWith :: Text -> Text -> (Text, Text)
breakWith needle = second (Text.drop 1) . Text.breakOn needle
