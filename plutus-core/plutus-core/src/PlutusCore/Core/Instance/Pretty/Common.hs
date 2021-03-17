{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Core.Instance.Pretty.Common () where

import           PlutusPrelude

import           PlutusCore.Core.Type

instance Pretty (Version ann) where
    pretty (Version _ i j k) = pretty i <> "." <> pretty j <> "." <> pretty k
