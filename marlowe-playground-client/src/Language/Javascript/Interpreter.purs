module Language.Javascript.Interpreter where

import Prelude
import Control.Monad.Except (runExcept)
import Control.Promise (Promise, toAffE)
import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Uncurried (EffectFn3, runEffectFn3)
import Foreign.Generic (decodeJSON)
import Marlowe.Semantics (Contract)
import Monaco (ITextModel)

data CompilationError
  = RawError String
  | JSONParsingError String
  | CompilationError
    { row :: Int
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

foreign import eval_ :: forall a b. EffectFn3 (String -> Either a b) (String -> Either a b) ITextModel (Promise (Either a b))

eval :: ITextModel -> Aff (Either CompilationError (InterpreterResult Contract))
eval model = do
  res <- toAffE (runEffectFn3 eval_ Left Right model)
  pure
    ( case res of
        Left err -> Left (RawError err)
        Right result -> case runExcept (decodeJSON result) of
          Left err -> Left (JSONParsingError (show err))
          Right contract -> Right (InterpreterResult { warnings: [], result: contract })
    )
