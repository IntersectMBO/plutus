{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import           Language.PlutusCore
import           Language.PlutusCore.Generators
import           Language.PlutusCore.Pretty

import           Data.Foldable
import           Data.Text                      (Text)
import qualified Data.Text                      as Text
import qualified Data.Text.IO                   as Text

-- | Generate a test sample: a term of arbitrary type and what it computes to.
-- Uses 'genTermLoose' under the hood.
generateTerm :: IO (TermOf (Value TyName Name ()))
generateTerm = runSampleSucceed $ withAnyTermLoose $ pure . unsafeTypeEvalCheck

oneline :: Text -> Text
oneline = Text.unwords . Text.words

main :: IO ()
main = do
    TermOf term value <- generateTerm
    traverse_ Text.putStrLn
        [ oneline . prettyPlcDefText $ Program () (Version () 0 1 0) term
        , ""
        , oneline . prettyPlcDefText $ value
        ]
