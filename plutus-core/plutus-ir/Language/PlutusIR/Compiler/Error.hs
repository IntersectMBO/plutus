{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
module Language.PlutusIR.Compiler.Error (Error (..), AsError (..)) where

import qualified Language.PlutusCore        as PLC
import qualified Language.PlutusCore.Pretty as PLC

import           Control.Exception
import           Control.Lens

import qualified Data.Text                  as T
import           Data.Text.Prettyprint.Doc  ((<+>))
import qualified Data.Text.Prettyprint.Doc  as PP
import           Data.Typeable

data Error uni fun a = CompilationError a T.Text -- ^ A generic compilation error.
                     | UnsupportedError a T.Text -- ^ An error relating specifically to an unsupported feature.
                     | PLCError (PLC.Error uni fun a) -- ^ An error from running some PLC function, lifted into this error type for convenience.
               deriving (Typeable)
makeClassyPrisms ''Error

instance PLC.AsTypeError (Error uni fun a) (PLC.Term PLC.TyName PLC.Name uni fun ()) uni a where
    _TypeError = _PLCError . PLC._TypeError

instance (PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst, PP.Pretty a) =>
            Show (Error uni fun a) where
    show e = show $ PLC.prettyPlcClassicDebug e

instance (PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst, PP.Pretty a) =>
            PLC.PrettyBy PLC.PrettyConfigPlc (Error uni fun a) where
    prettyBy config = \case
        CompilationError x e -> "Error during compilation:" <+> PP.pretty e <> "(" <> PP.pretty x <> ")"
        UnsupportedError x e -> "Unsupported construct:" <+> PP.pretty e <+> "(" <> PP.pretty x <> ")"
        PLCError e -> PP.vsep [ "Error from the PLC compiler:", PLC.prettyBy config e ]

instance ( PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst, PP.Pretty a
         , Typeable uni, Typeable fun, Typeable a
         ) => Exception (Error uni fun a)
