module Z3 where

import Debug.Trace (trace)
import Effect (Effect)
import Global (readInt)
import Prelude (bind, discard, pure, (=<<))
import Z3.Monad (assert, astToString, check, eq, getAstFromModel, mkIntVar, not, pop, push, runZ3, withModel)

run :: Effect Boolean
run =
  runZ3 do
    x <- mkIntVar "x"
    y <- mkIntVar "y"
    ast <- not =<< eq x.ast y.ast
    assert ast
    push
    res <- check
    _ <-
      if res then do
        modelX <- withModel \model -> getAstFromModel model x.decl
        modelXString <- astToString modelX
        let
          n = readInt 10 modelXString
        trace n \_ -> pure res
      else
        pure res
    pop
    ast2 <- eq x.ast y.ast
    assert ast2
    check
