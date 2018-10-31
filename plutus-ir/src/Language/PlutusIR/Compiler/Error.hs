{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusIR.Compiler.Error (CompError (..)) where

import qualified Data.Text                 as T
import qualified Data.Text.Prettyprint.Doc as PP

data CompError = CompilationError T.Text
               | UnsupportedError T.Text

instance PP.Pretty CompError where
    pretty = \case
        CompilationError e -> "Error during compilation:" PP.<+> PP.pretty e
        UnsupportedError e -> "Unsupported:" PP.<+> PP.pretty e
