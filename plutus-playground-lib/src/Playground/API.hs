{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeOperators         #-}

module Playground.API where

import           Control.Monad.Trans.Class    (lift)
import           Control.Monad.Trans.State    (StateT, evalStateT, get, put)
import           Data.Bifunctor               (second)
import           Data.Maybe                   (fromMaybe)
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import           Language.Haskell.Interpreter (CompilationError (CompilationError, RawError), InterpreterResult,
                                               SourceCode, column, filename, row, text)
import qualified Language.Haskell.Interpreter as HI
import           Playground.Rollup            ()
import           Playground.Types             (CompilationResult, Evaluation, EvaluationResult, PlaygroundError)
import           Servant.API                  ((:<|>), (:>), Get, JSON, Post, ReqBody)
import           Text.Read                    (readMaybe)

type API
     = "contract" :> ReqBody '[ JSON] SourceCode :> Post '[ JSON] (Either HI.InterpreterError (InterpreterResult CompilationResult))
       :<|> "evaluate" :> ReqBody '[ JSON] Evaluation :> Post '[ JSON] (Either PlaygroundError EvaluationResult)
       :<|> "health" :> Get '[ JSON] ()

parseErrorsText :: Text -> [CompilationError]
parseErrorsText input = parseErrorText <$> Text.splitOn "\n\n" input

parseErrorText :: Text -> CompilationError
parseErrorText input =
    fromMaybe (RawError input) $
    flip evalStateT input $ do
        filename <- consumeTo ":"
        rowStr <- consumeTo ":"
        columnStr <- consumeTo ":"
        text <- Text.lines <$> consume
  --
        row <- lift $ readMaybe $ Text.unpack rowStr
        column <- lift $ readMaybe $ Text.unpack columnStr
        pure CompilationError {..}

consumeTo :: Monad m => Text -> StateT Text m Text
consumeTo needle = do
    (before, after) <- breakWith needle <$> get
    put after
    pure before

consume :: (Monad m, Monoid s) => StateT s m s
consume = get <* put mempty

-- | Like `Data.Text.breakOn`, but consumes the breakpoint text (the 'needle').
breakWith :: Text -> Text -> (Text, Text)
breakWith needle = second (Text.drop 1) . Text.breakOn needle
