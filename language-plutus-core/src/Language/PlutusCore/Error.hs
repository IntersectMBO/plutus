module Language.PlutusCore.Error ( Error (..)
                                 ) where

import           Data.Text.Prettyprint.Doc
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Parser
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.TypeSynthesis

data Error = ParseError ParseError
           | RenameError (RenameError AlexPosn)
           | TypeError (TypeError AlexPosn)

instance Pretty Error where
    pretty (ParseError e)  = pretty e
    pretty (RenameError e) = pretty e
    pretty (TypeError e)   = pretty e
