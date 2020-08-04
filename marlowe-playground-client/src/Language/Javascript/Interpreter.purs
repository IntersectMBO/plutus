module Language.Javascript.Interpreter where

import Prelude
import Control.Monad.Except (runExcept)
import Data.Either (Either(..))
import Data.Function.Uncurried (Fn3, runFn3)
import Foreign (Foreign)
import Foreign.Generic (decode)
import Marlowe.Semantics (Contract)

data CompilationError
  = RawError String
  | CompilationError
    { filename :: String
    , row :: Int
    , column :: Int
    , text :: Array String
    }

newtype Warning
  = Warning String

newtype InterpreterResult a
  = InterpreterResult
  { warnings :: Array Warning
  , result :: a
  }

foreign import eval_ :: forall a b. Fn3 (String -> Either a b) (String -> Either a b) String (Either String Foreign)

eval :: String -> Either CompilationError (InterpreterResult Contract)
eval js = case runFn3 eval_ Left Right js of
  Left err -> Left (RawError err)
  Right result -> case runExcept (decode result) of
    Left err -> Left (RawError (show err))
    Right contract -> Right (InterpreterResult { warnings: [], result: contract })
