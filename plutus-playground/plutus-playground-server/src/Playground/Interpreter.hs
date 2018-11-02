module Playground.Interpreter where

import           Control.Monad.Catch          (finally)
import           Control.Monad.IO.Class       (liftIO)
import           Data.Aeson                   (FromJSON, Result (Success), Value, fromJSON)
import qualified Data.Aeson                   as JSON
import qualified Data.ByteString.Lazy.Char8   as BSL
import           Data.List                    (intercalate)
import           Data.Maybe                   (catMaybes, fromJust)
import           Data.Monoid                  ((<>))
import           Data.Text                    (unpack)
import qualified Data.Text                    as Text
import           Data.Typeable                (TypeRep, Typeable, typeRepArgs)
import qualified Data.Typeable                as DT
import           Language.Haskell.Interpreter (Extension (..), GhcError, ModuleElem (Fun), MonadInterpreter,
                                               OptionVal ((:=)), as, getModuleExports, interpret, languageExtensions,
                                               loadModules, runInterpreter, set, setImportsQ, setTopLevelModules,
                                               typeChecksWithDetails, typeOf)
import           Playground.API               (Fn (Fn), SourceCode (SourceCode))
import           System.Directory             (removeFile)
import           System.IO                    (readFile)
import           System.IO.Temp               (writeTempFile)
import           Wallet.API                   (WalletAPI)
import           Wallet.Emulator.Types        (Trace, AssertionError, EmulatedWalletApi, EmulatorState,
                                               Wallet (Wallet, getWallet), runTraceTxPool, walletAction)

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

loadSource :: (MonadInterpreter m) => FilePath -> m () -> m ()
loadSource fileName action =
  flip finally (liftIO (removeFile fileName)) $ do
    set [languageExtensions := defaultExtensions]
    loadModules [fileName]
    setTopLevelModules ["Main"]
    action

-- TODO: this needs to return a schema of the function names and types
--       http://hackage.haskell.org/package/swagger2-2.3.0.1/docs/Data-Swagger-Internal-Schema.html#t:ToSchema
compile :: (MonadInterpreter m) => SourceCode -> m ()
compile (SourceCode s) = do
  fileName <- liftIO $ writeTempFile "." "Main.hs" (unpack s)
  loadSource fileName $ do
    exports <- getModuleExports "Main"
    walletFunctions <- catMaybes <$> traverse isWalletFunction exports
    liftIO $ print walletFunctions

runFunction :: (MonadInterpreter m) => SourceCode -> [(Fn, [Value])] -> m ()
runFunction (SourceCode s) fs = do
  fileName <- liftIO $ writeTempFile "." "Main.hs" (unpack s)
  loadSource fileName $ do
    setImportsQ
      [("Playground.Interpreter", Nothing), ("Wallet.Emulator", Nothing)]
    liftIO . putStrLn $ mkExpr (fmap (\(f, vs) -> (f, (Wallet 1), vs)) fs)
    res <- interpret (mkExpr (fmap (\(f, vs) -> (f, (Wallet 1), vs)) fs)) (as :: Bool)
    liftIO . print $ res

runTrace :: Trace EmulatedWalletApi a -> Bool
runTrace action =
  let (eRes, newState) = runTraceTxPool [] action
   in case eRes of
        Right _ -> True
        Left _  -> False

mkExpr :: [(Fn, Wallet, [Value])] -> String
mkExpr fs =
  "runTrace (" <>
  (intercalate " >> " $
   fmap
     (\(f, wallet, args) -> walletActionExpr f wallet args)
     fs) <>
  ")"

walletActionExpr :: Fn -> Wallet -> [Value] -> String
walletActionExpr (Fn f) wallet args =
  "(walletAction (" <> show wallet <> ") (" <>
  mkApplyExpr (Text.unpack f) (fmap jsonToString args) <> "))"

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

jsonToString :: Value -> String
jsonToString = show . JSON.encode

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
  pure $
    if t == "Int -> Int"
      then Just f
      else Nothing
isWalletFunction _ = pure Nothing

data Function =
  Function String
           [TypeRep]

registerFunction :: Typeable a => String -> a -> Function
registerFunction name fn = Function name $ typesOf fn

typesOf :: Typeable a => a -> [TypeRep]
typesOf f = splitFunType [DT.typeOf f]

splitFunType :: [TypeRep] -> [TypeRep]
splitFunType [] = []
splitFunType (t1:ts) =
  case typeRepArgs t1 of
    []       -> t1 : splitFunType ts
    (t2:t2s) -> t2 : splitFunType t2s
