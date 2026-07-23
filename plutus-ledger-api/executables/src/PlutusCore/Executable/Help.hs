-- | Helpers for the @Examples@ footer in @--help@ output.
module PlutusCore.Executable.Help
  ( Example (..)
  , eg
  , examplesDoc
  , examplesFooter
  ) where

import Options.Applicative (InfoMod, footerDoc)
import Options.Applicative.Help.Pretty (Doc, concatWith, hardline, pretty)

data Example = Example
  { exampleDescription :: String
  , exampleCommand :: String
  }
  deriving stock (Eq, Show)

eg :: String -> String -> Example
eg = Example

examplesDoc :: [Example] -> Maybe Doc
examplesDoc [] = Nothing
examplesDoc examples = Just (joinLines (pretty "Examples:" : concatMap render examples))
  where
    render (Example desc cmd) =
      [ mempty
      , pretty ("  # " <> desc)
      , pretty ("  " <> cmd)
      ]
    joinLines = concatWith (\x y -> x <> hardline <> y)

examplesFooter :: [Example] -> InfoMod a
examplesFooter = footerDoc . examplesDoc
