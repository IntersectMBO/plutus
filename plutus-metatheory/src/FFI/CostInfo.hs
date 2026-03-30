module FFI.CostInfo where

import Data.Text (Text)

type EvalError = Text

data EvalResult
  = EvalSuccess Integer Integer
  | EvalFailure EvalError Integer Integer
