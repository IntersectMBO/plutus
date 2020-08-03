module Language.Javascript.Interpreter where

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
