{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Plutus.CoreToPLC.Error (Error (..), mustBeReplaced) where

import qualified Language.PlutusCore       as PLC

import qualified Data.Text                 as T
import qualified Data.Text.Prettyprint.Doc as PP
import           Data.Typeable
import           GHC.Exception

data Error a = PLCError (PLC.Error a)
             | ConversionError T.Text
             | UnsupportedError T.Text
             | FreeVariableError T.Text
             | Context T.Text (Error a)
             deriving Typeable

instance (PLC.PrettyCfg a) => Show (Error a) where
    show e = T.unpack $ PLC.debugText e

instance (Typeable a, PLC.PrettyCfg a) => Exception (Error a)

instance (PLC.PrettyCfg a) => PLC.PrettyCfg (Error a) where
    prettyCfg cfg = \case
        PLCError e -> PLC.prettyCfg cfg e
        ConversionError e -> "Error during conversion:" PP.<+> PP.pretty e
        UnsupportedError e -> "Unsupported:" PP.<+> PP.pretty e
        FreeVariableError e -> "Free variable:" PP.<+> PP.pretty e
        Context ctx e -> PP.vsep [ "Context:" PP.<+> PP.pretty ctx , PLC.prettyCfg cfg e ]

mustBeReplaced :: a
mustBeReplaced = error "This must be replaced by the core-to-plc plugin during compilation"
