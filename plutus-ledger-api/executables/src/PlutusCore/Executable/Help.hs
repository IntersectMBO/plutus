-- | Helpers for building richer @--help@ output for the plutus executables.
module PlutusCore.Executable.Help
  ( Example (..)
  , eg
  , examplesDoc
  , examplesFooter
  ) where

import Options.Applicative (InfoMod, footerDoc)
import Options.Applicative.Help.Pretty (Doc, concatWith, hardline, pretty)

{-| A single usage example shown in the @Examples@ section of @--help@ output. -}
data Example = Example
  { exampleDescription :: String
  -- ^ A short, one-line description of what the command does.
  , exampleCommand :: String
  -- ^ The example command line, shown verbatim (no wrapping).
  }
  deriving stock (Eq, Show)

-- | Convenience constructor for an 'Example' (description, then command line).
eg :: String -> String -> Example
eg = Example

{-| Render an @Examples@ section as a 'Doc', or 'Nothing' if there are no
examples.

Unlike 'Options.Applicative.footer', which reflows its text to the terminal
width, each example is rendered verbatim so that command lines keep their exact
formatting. Each example is shown as a commented description followed by the
command, separated by blank lines. For a single @'eg' "Evaluate a program"
"uplc evaluate -i program.uplc"@ the result renders as:

@
Examples:

  # Evaluate a program
  uplc evaluate -i program.uplc
@
-}
examplesDoc :: [Example] -> Maybe Doc
examplesDoc [] = Nothing
examplesDoc examples = Just (joinLines (pretty "Examples:" : concatMap render examples))
  where
    render (Example desc cmd) =
      [ mempty -- blank line separating this example from the previous block
      , pretty ("  # " <> desc)
      , pretty ("  " <> cmd)
      ]
    joinLines = concatWith (\x y -> x <> hardline <> y)

{-| Build an @Examples@ section suitable for use as the footer of a
'Options.Applicative.ParserInfo' (see 'footerDoc'). An empty list produces an
empty (no-op) footer. -}
examplesFooter :: [Example] -> InfoMod a
examplesFooter = footerDoc . examplesDoc
