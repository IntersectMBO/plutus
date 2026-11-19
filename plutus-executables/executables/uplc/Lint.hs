module Lint (runLint) where

import Control.Lens ((^..))
import Prettyprinter (indent)

import PlutusCore qualified as PLC
import PlutusCore.Executable.Common
import PlutusPrelude
import UntypedPlutusCore (Program (..), Term (..), termSubtermsDeep)

data Suggestion a = SuggestTerm (UplcTerm a) | SuggestText String

data Rule a = Rule
  { ruleSummary :: String
  , ruleNotes :: [String]
  , ruleMatch :: UplcTerm a -> Maybe (Suggestion a)
  }

rules :: [Rule a]
rules = [ifToCase]

ifToCase :: Rule a
ifToCase =
  Rule
    { ruleSummary = "Use casing on Boolean instead of ifThenElse."
    , ruleNotes =
        [ "Casing on the Boolean requires PLC version 1.1.0 or above."
        , "This may change the program's behavior unless the condition evaluates to a Boolean."
        , "ifThenElse is strict in both branches. Casing on Boolean evaluates only the selected branch."
        ]
    , ruleMatch = \case
        Builtin _ PLC.IfThenElse ->
          Just
            ( SuggestText
                "Use casing on the Boolean. The False branch comes first, and the optional True branch comes second."
            )
        _ -> Nothing
    }

runLint :: Input -> Format -> IO ()
runLint inp fmt = do
  Program _ _ body <- readProgram fmt inp
  let findings =
        [ (term, rule, suggestion)
        | term <- body ^.. termSubtermsDeep
        , rule <- rules
        , Just suggestion <- [ruleMatch rule term]
        ]
  for_ findings $ \(found, rule, suggestion) -> do
    let location = if fmt == Textual then show (getAnn found) else show inp
    putStrLn $ location <> ": " <> ruleSummary rule
    putStrLn "Found:"
    print $ indent 2 (prettyPrintByMode Simple found)
    putStrLn "Perhaps:"
    print $ indent 2 $ case suggestion of
      SuggestText message -> pretty message
      SuggestTerm term -> prettyPrintByMode Simple term
    for_ (ruleNotes rule) $ \note -> putStrLn ("Note: " <> note)
