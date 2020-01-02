-- | A "readable" Agda-like way to pretty-print PLC entities.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Erasure.Untyped.Instance.Pretty.Readable () where

import           PlutusPrelude

import           Language.PlutusCore.Erasure.Untyped.Instance.Pretty.Common ()
import           Language.PlutusCore.Erasure.Untyped.Term
import           Language.PlutusCore.Pretty.Readable
import           Language.PlutusCore.Pretty.Utils

instance PrettyBy (PrettyConfigReadable configName) (Constant a) where
    prettyBy config = unitaryDoc config . \case
        BuiltinInt _ int -> pretty int
        BuiltinBS _ bs   -> prettyBytes bs
        BuiltinStr _ str -> pretty str

instance PrettyBy (PrettyConfigReadable configName) (Builtin a) where
    prettyBy config = unitaryDoc config . \case
        BuiltinName    _ name -> pretty name
        DynBuiltinName _ name -> pretty name

instance PrettyReadableBy configName (name a) =>
        PrettyBy (PrettyConfigReadable configName) (Term name a) where
    prettyBy config = \case
        Constant _ con         -> prettyBy config con
        Builtin _ bi           -> prettyBy config bi
        Apply _ fun arg        -> applicationDoc config fun arg
        Var _ name             -> unit $ prettyName name
        LamAbs _ name body     -> bind $ \bindBody ->
            "\\" <> parens (prettyName name) <+> "->" <+> bindBody body
        Error _                -> "error"
        Prune _ _              -> "<pruned>"
      where
        prettyName = prettyBy config
        unit = unitaryDoc  config
        bind = binderDoc   config
--        rayL = rayDoc      config Backward
--        rayR = rayDoc      config Forward
--        comp = compoundDoc config

instance PrettyReadableBy configName (Term name a) =>
        PrettyBy (PrettyConfigReadable configName) (Program name a) where
    prettyBy config (Program _ version term) =
        rayDoc config Forward juxtApp $ \juxt -> "program" <+> pretty version <+> juxt term
