{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
module Playground.Interpreter where

import           Control.Monad.Catch          (finally, throwM)
import           Control.Monad.IO.Class       (liftIO)
import           Data.Aeson                   (FromJSON, Result (Success), ToJSON, Value, fromJSON)
import qualified Data.Aeson                   as JSON
import qualified Data.ByteString.Lazy.Char8   as BSL
import           Data.List                    (intercalate)
import           Data.Maybe                   (catMaybes, fromJust)
import           Data.Monoid                  ((<>))
import           Data.Swagger                 (Schema)
import           Data.Swagger.Schema          (ToSchema, toSchema, declareNamedSchema)
import           Data.Text                    (unpack)
import qualified Data.Text                    as Text
import           Data.Typeable                (TypeRep, Typeable, typeRepArgs)
import qualified Data.Typeable                as DT
import           Language.Haskell.Interpreter (Extension (..), GhcError, InterpreterError (UnknownError),
                                               ModuleElem (Fun), MonadInterpreter, OptionVal ((:=)), as,
                                               getModuleExports, interpret, languageExtensions, loadModules,
                                               runInterpreter, set, setImportsQ, setTopLevelModules,
                                               typeChecksWithDetails, typeOf)
import           Playground.API               (Evaluation (program, sourceCode), Expression (Expression), Fn (Fn),
                                               FunctionSchema (FunctionSchema), Program, SourceCode (getSourceCode),
                                               blockchain)
import           System.Directory             (removeFile)
import           System.IO                    (readFile)
import           System.IO.Temp               (writeTempFile)
import qualified Type.Reflection              as TR
import           Wallet.API                   (WalletAPI)
import           Wallet.Emulator.Types        (AssertionError, EmulatedWalletApi, EmulatorState (emChain), Trace,
                                               Wallet (Wallet, getWallet), runTraceChain, runTraceTxPool, walletAction)
import           Wallet.UTXO                  (Blockchain)
import qualified Language.Haskell.TH as TH
import qualified Playground.TH as TH

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

loadSource :: (MonadInterpreter m) => FilePath -> m a -> m a
loadSource fileName action =
  flip finally (liftIO (removeFile fileName)) $ do
    set [languageExtensions := defaultExtensions]
    loadModules [fileName]
    setTopLevelModules ["Main"]
    action

-- TODO: this needs to return a schema of the function names and types
--       http://hackage.haskell.org/package/swagger2-2.3.0.1/docs/Data-Swagger-Internal-Schema.html#t:ToSchema
compile :: (MonadInterpreter m) => SourceCode -> m [FunctionSchema]
compile s = do
  fileName <- liftIO $ writeTempFile "." "Main.hs" (unpack . getSourceCode $ s)
  loadSource fileName $ do
    exports <- getModuleExports "Main"
    liftIO $ print exports
    walletFunctions <- catMaybes <$> traverse isWalletFunction exports
    liftIO $ print walletFunctions
    traverse getSchema walletFunctions

getSchema :: (MonadInterpreter m) => ModuleElem -> m FunctionSchema
getSchema (Fun m) = interpret m (as :: FunctionSchema)
getSchema _ = error "Trying to get a schema by calling something other than a function"

runFunction :: (MonadInterpreter m) => Evaluation -> m Blockchain
runFunction evaluation = do
  fileName <-
    liftIO $
    writeTempFile
      "."
      "Main.hs"
      (unpack . getSourceCode . sourceCode $ evaluation)
  loadSource fileName $ do
    setImportsQ
      [("Playground.Interpreter", Nothing), ("Wallet.Emulator", Nothing)]
    liftIO . putStrLn $ mkExpr evaluation
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

{-# ANN module ("HLint: ignore" :: String) #-}

-- | This will throw an exception if it cannot decode the json however it should
--   never do this as long as it is only called in places where we have already
--   decoded and encode the value since it came from an HTTP API call
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

-- TODO: this is just a placeholder, really we want to work out how to find the
--       correct function types (or force user to declare them)
isWalletFunction :: (MonadInterpreter m) => ModuleElem -> m (Maybe ModuleElem)
isWalletFunction f@(Fun s) = do
  t <- typeOf s
  liftIO . print $ t
  pure $
    if t == "FunctionSchema"
      then Just f
      else Nothing
isWalletFunction _ = pure Nothing

testFun :: Int -> Int -> Int
testFun x y = x + y

$(TH.mkFunction 'testFun)

-- notes: Schemas don't have a way of representing functions so we will create
-- our own representation, a name and a list of schemas. We can convert this
-- to json

typesOf :: Typeable a => a -> [TypeRep]
typesOf f = splitFunType [DT.typeOf f]

splitFunType :: [TypeRep] -> [TypeRep]
splitFunType [] = []
splitFunType (t1:ts) =
  case typeRepArgs t1 of
    []       -> t1 : splitFunType ts
    (t2:t2s) -> t2 : splitFunType t2s
