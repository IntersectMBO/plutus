{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Plutus.CoreToPLC.Error (Error (..), errorText, mustBeReplaced) where

import qualified Language.PlutusCore as PC

import           Data.Semigroup
import qualified Data.Text           as T

data Error a = PCError (PC.Error a)
             | ConversionError T.Text
             | UnsupportedError T.Text
             | FreeVariableError T.Text

errorText :: (PC.PrettyCfg a) => Error a -> T.Text
errorText = \case
    PCError e -> PC.debugText e
    ConversionError e -> "Error during conversion: " <> e
    UnsupportedError e -> "Unsupported: " <> e
    FreeVariableError e -> "Free variable: " <> e

mustBeReplaced :: a
mustBeReplaced = error "This must be replaced by the core-to-plc plugin during compilation"
