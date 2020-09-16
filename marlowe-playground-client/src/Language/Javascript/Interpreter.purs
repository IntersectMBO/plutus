module Language.Javascript.Interpreter where

import Prelude

import Control.Monad.Except (runExcept)
import Control.Promise (Promise, toAffE)
import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Uncurried (EffectFn3, runEffectFn3)
import Foreign.Generic (decodeJSON)
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

foreign import eval_ :: forall a b. EffectFn3 (String -> Either a b) (String -> Either a b) String (Promise (Either a b))

eval :: String -> Aff (Either CompilationError (InterpreterResult Contract))
eval js = do res <- toAffE (runEffectFn3 eval_ Left Right js)
             pure (case res of
                     Left err -> Left (RawError err)
                     Right result -> case runExcept (decodeJSON result) of
                       Left err -> Left (RawError (show err))
                       Right contract -> Right (InterpreterResult { warnings: [], result: contract }))
