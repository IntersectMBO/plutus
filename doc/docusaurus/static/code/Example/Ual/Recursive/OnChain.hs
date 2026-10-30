{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas -fno-omit-interface-pragmas #-}

module Example.Ual.Recursive.OnChain where

import GHC.Generics (Generic)
import PlutusTx.Blueprint
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)
import PlutusTx.Prelude

data Tree = Leaf Integer | Branch Tree Tree
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)
$(makeIsDataSchemaIndexed ''Tree [('Leaf, 0), ('Branch, 1)])

{-# INLINEABLE treeSum #-}
treeSum :: Tree -> Integer
treeSum (Leaf n) = n
treeSum (Branch l r) = treeSum l + treeSum r

{-# INLINEABLE treeMirror #-}
treeMirror :: Tree -> Tree
treeMirror (Leaf n) = Leaf n
treeMirror (Branch l r) = Branch (treeMirror r) (treeMirror l)

{-# INLINEABLE treeValidator #-}
treeValidator :: BuiltinData -> BuiltinData -> BuiltinUnit
treeValidator d _ = check (treeSum (unsafeFromBuiltinData d) == 7)

{-# INLINEABLE mirrorData #-}
mirrorData :: BuiltinData -> BuiltinData
mirrorData d = toBuiltinData (treeMirror (unsafeFromBuiltinData d))
