module Language.Javascript.Interpreter where

import Data.Either (Either(..))
import Data.Function.Uncurried (Fn3, runFn3)

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

foreign import eval_ :: forall a b. Fn3 (String -> Either a b) (String -> Either a b) String (Either String String)

eval :: String -> Either CompilationError (InterpreterResult String)
eval js = case runFn3 eval_ Left Right js of
  Left err -> Left (RawError err)
  Right result -> Right (InterpreterResult { warnings: [], result })
