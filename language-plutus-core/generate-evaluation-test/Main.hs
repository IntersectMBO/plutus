{-# LANGUAGE OverloadedStrings #-}
module Main where

import           PlutusPrelude
import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.CkMachine
import           Language.PlutusCore.TestSupport

import           Data.Foldable
import           Control.Monad.Morph
import qualified Data.Text.IO as Text
import qualified Hedgehog.Gen   as Gen

ckEvalResultToMaybe :: CkEvalResult -> Maybe (Value TyName Name ())
ckEvalResultToMaybe (CkEvalSuccess res) = Just res
ckEvalResultToMaybe CkEvalFailure       = Nothing

generateTerm :: IO (TermOf (Value TyName Name ()))
generateTerm
    = Gen.sample
    . Gen.just
    . hoist (pure . unsafeRunFresh)
    $ withAnyTermLoose
    $ \(TermOf term (TypedBuiltinValue tb x)) -> pure $ do
          _ <- ckEvalResultToMaybe $ evaluateCk term
          case unsafeMakeConstant tb x of
              Nothing  -> error "generateTerm: Nothing"
              Just res -> Just $ TermOf term res

main :: IO ()
main = do
    TermOf term value <- generateTerm
    traverse_ Text.putStrLn
        [ prettyText term
        , ""
        , prettyText value
        ]
