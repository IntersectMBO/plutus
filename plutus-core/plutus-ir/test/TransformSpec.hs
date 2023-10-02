{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module TransformSpec where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Quote

import PlutusCore qualified as PLC
import PlutusCore.Name
import PlutusCore.Pretty qualified as PLC
import PlutusPrelude

import Control.Monad.Except
import PlutusIR.Analysis.RetainedSize qualified as RetainedSize
import PlutusIR.Core.Instance.Pretty.Readable
import PlutusIR.Core.Type
import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.Rename ()

test_transform :: TestTree
test_transform = runTestNestedIn ["plutus-ir/test"] transform

transform :: TestNested
transform =
    testNested
        "transform"
        [
        ]

instance Semigroup PLC.SrcSpan where
    sp1 <> _ = sp1

instance Monoid PLC.SrcSpan where
    mempty = initialSrcSpan ""


