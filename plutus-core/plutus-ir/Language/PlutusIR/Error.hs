{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
module Language.PlutusIR.Error
    ( Error (..)
    , PLC.AsTypeError (..)
    , PLC.TypeError
    , AsTypeErrorExt (..)
    , AsError (..)
    , TypeErrorExt (..)
    , PLC.Normalized (..)
    , PLC.UnknownDynamicBuiltinNameError (..)
    ) where

import qualified Language.PlutusCore        as PLC
import qualified Language.PlutusCore.Pretty as PLC
import           PlutusPrelude

import qualified Language.PlutusIR          as PIR

import           Control.Lens

import qualified Data.Text                  as T
import           Data.Text.Prettyprint.Doc  as PP


data TypeErrorExt uni ann =
      MalformedDataConstrResType
         ann
         -- the expected constructor's type
         (PLC.Type PLC.TyName uni ann)
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''TypeErrorExt


data Error uni a = CompilationError a T.Text -- ^ A generic compilation error.
                 | UnsupportedError a T.Text -- ^ An error relating specifically to an unsupported feature.
                 | PLCError (PLC.Error uni a) -- ^ An error from running some PLC function, lifted into this error type for convenience.
                 | PLCTypeError (PLC.TypeError (PIR.Term PIR.TyName PIR.Name uni ()) uni a)
                 | PIRTypeError (TypeErrorExt uni a)
               deriving (Typeable)
makeClassyPrisms ''Error

instance PLC.AsTypeError (Error uni a) (PIR.Term PIR.TyName PIR.Name uni ()) uni a where
    _TypeError = _PLCTypeError

instance AsTypeErrorExt (Error uni a) uni a where
    _TypeErrorExt = _PIRTypeError


-- Pretty-printing
------------------

type PrettyUni uni ann =
    (PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst, PP.Pretty ann)

instance (PrettyUni uni ann) => PrettyBy PLC.PrettyConfigPlc (TypeErrorExt uni ann) where
    prettyBy config (MalformedDataConstrResType ann expType) =
        vsep ["The result-type of a dataconstructor is malformed at location" <+> PP.pretty ann
             , "The expected result-type is:" <+> prettyBy config expType]

-- show via pretty, for printing as SomeExceptions
instance (PrettyUni uni ann) => Show (Error uni ann) where
    show = show . PP.pretty

instance (PrettyUni uni ann, Typeable uni, Typeable ann) => Exception (Error uni ann)

instance
        (Pretty ann,
        PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst
        ) => Pretty (Error uni ann) where
    pretty = PLC.prettyPlcClassicDef


instance (PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` PLC.PrettyConst, Pretty ann) =>
            PrettyBy PLC.PrettyConfigPlc (Error uni ann) where
     prettyBy config = \case
        CompilationError x e -> "Error during compilation:" <+> PP.pretty e <> "(" <> PP.pretty x <> ")"
        UnsupportedError x e -> "Unsupported construct:" <+> PP.pretty e <+> "(" <> PP.pretty x <> ")"
        PLCError e -> PP.vsep [ "Error from the PLC compiler:", PLC.prettyBy config e ]
        PLCTypeError e -> PP.vsep ["Error during PIR typechecking:" , PLC.prettyBy config e ]
        PIRTypeError e -> PP.vsep ["Error during PIR typechecking:" , PLC.prettyBy config e ]
