module JavascriptEditor.Types where

import Language.Javascript.Interpreter as JS
import Marlowe.Semantics (Contract)

data JSCompilationState
  = JSNotCompiled
  | JSCompiling
  | JSCompilationError JS.CompilationError
  | JSCompiledSuccessfully (JS.InterpreterResult Contract)
