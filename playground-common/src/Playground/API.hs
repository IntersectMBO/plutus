{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators         #-}

module Playground.API
    ( API
    ) where

import           Language.Haskell.Interpreter (InterpreterResult, SourceCode)
import qualified Language.Haskell.Interpreter as HI
import           Playground.Types             (CompilationResult, Evaluation, EvaluationResult, PlaygroundError)
import           Servant.API                  (Get, JSON, Post, ReqBody, (:<|>), (:>))

type API
     = "contract" :> ReqBody '[ JSON] SourceCode :> Post '[ JSON] (Either HI.InterpreterError (InterpreterResult CompilationResult))
       :<|> "evaluate" :> ReqBody '[ JSON] Evaluation :> Post '[ JSON] (Either PlaygroundError EvaluationResult)
       :<|> "health" :> Get '[ JSON] ()
