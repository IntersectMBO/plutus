{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
-- CSE is very unstable and produces different output, likely depending on the version of either
-- @unordered-containers@ or @hashable@.
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}

module AssocMap.Properties2 where

import Hedgehog (Property, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Code
import PlutusTx.Data.AssocMap qualified as Data.AssocMap
import PlutusTx.Data.List qualified as Data.List
import PlutusTx.IsData ()
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.List qualified as PlutusTx
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Test.Util.Compiled (cekResultMatchesHaskellValue, compiledCodeToTerm)
import PlutusTx.TH (compile)

import AssocMap.Semantics

keysProgram
  :: CompiledCode
       ( AssocMap.Map Integer Integer
         -> [Integer]
       )
keysProgram =
  $$(compile [||AssocMap.keys||])

dataKeysProgram
  :: CompiledCode
       ( Data.AssocMap.Map Integer Integer
         -> [Integer]
       )
dataKeysProgram =
  $$(compile [||Data.List.toSOP . Data.AssocMap.keys||])

elemsProgram
  :: CompiledCode
       ( AssocMap.Map Integer Integer
         -> [Integer]
       )
elemsProgram =
  $$(compile [||AssocMap.elems||])

dataElemsProgram
  :: CompiledCode
       ( Data.AssocMap.Map Integer Integer
         -> [Integer]
       )
dataElemsProgram =
  $$(compile [||Data.List.toSOP . Data.AssocMap.elems||])

filterProgram
  :: CompiledCode
       ( Integer
         -> AssocMap.Map Integer Integer
         -> [(Integer, Integer)]
       )
filterProgram =
  $$( compile
        [||
        \num m ->
          PlutusTx.sort $
            AssocMap.toList $
              AssocMap.filter (\x -> x PlutusTx.< num) m
        ||]
    )

dataFilterProgram
  :: CompiledCode
       ( Integer
         -> Data.AssocMap.Map Integer Integer
         -> [(Integer, Integer)]
       )
dataFilterProgram =
  $$( compile
        [||
        \num m ->
          PlutusTx.sort $
            Data.AssocMap.toSOPList $
              Data.AssocMap.filter (\x -> x PlutusTx.< num) m
        ||]
    )

mapWithKeyProgram
  :: CompiledCode
       ( AssocMap.Map Integer Integer
         -> [(Integer, Integer)]
       )
mapWithKeyProgram =
  $$( compile
        [||
        \m ->
          PlutusTx.sort $
            AssocMap.toList $
              AssocMap.mapWithKey (\k v -> k PlutusTx.+ v) m
        ||]
    )

dataMapWithKeyProgram
  :: CompiledCode
       ( Data.AssocMap.Map Integer Integer
         -> [(Integer, Integer)]
       )
dataMapWithKeyProgram =
  $$( compile
        [||
        \m ->
          PlutusTx.sort $
            Data.AssocMap.toSOPList $
              Data.AssocMap.mapWithKey (\k v -> k PlutusTx.+ v) m
        ||]
    )

mapMaybeProgram
  :: CompiledCode
       ( Integer
         -> AssocMap.Map Integer Integer
         -> [(Integer, Integer)]
       )
mapMaybeProgram =
  $$( compile
        [||
        \num m ->
          PlutusTx.sort $
            AssocMap.toList $
              AssocMap.mapMaybe
                (\x -> if x PlutusTx.< num then Just x else Nothing)
                m
        ||]
    )

dataMapMaybeProgram
  :: CompiledCode
       ( Integer
         -> Data.AssocMap.Map Integer Integer
         -> [(Integer, Integer)]
       )
dataMapMaybeProgram =
  $$( compile
        [||
        \num m ->
          PlutusTx.sort $
            Data.AssocMap.toSOPList $
              Data.AssocMap.mapMaybe
                (\x -> if x PlutusTx.< num then Just x else Nothing)
                m
        ||]
    )

mapMaybeWithKeyProgram
  :: CompiledCode
       ( AssocMap.Map Integer Integer
         -> [(Integer, Integer)]
       )
mapMaybeWithKeyProgram =
  $$( compile
        [||
        \m ->
          PlutusTx.sort $
            AssocMap.toList $
              AssocMap.mapMaybeWithKey
                (\k v -> if v PlutusTx.< k then Just v else Nothing)
                m
        ||]
    )

dataMapMaybeWithKeyProgram
  :: CompiledCode
       ( Data.AssocMap.Map Integer Integer
         -> [(Integer, Integer)]
       )
dataMapMaybeWithKeyProgram =
  $$( compile
        [||
        \m ->
          PlutusTx.sort $
            Data.AssocMap.toSOPList $
              Data.AssocMap.mapMaybeWithKey
                (\k v -> if v PlutusTx.< k then Just v else Nothing)
                m
        ||]
    )

dataNoDuplicateKeysProgram
  :: CompiledCode
       ( Data.AssocMap.Map Integer Integer
         -> Bool
       )
dataNoDuplicateKeysProgram =
  $$(compile [||Data.AssocMap.noDuplicateKeys||])

keysSpec :: Property
keysSpec = property $ do
  assocMapS <- forAll genAssocMapS
  let assocMap = semanticsToAssocMap assocMapS
      expected = keysS assocMapS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        keysProgram
          `unsafeApplyCode` (liftCodeDef assocMap)
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        dataKeysProgram
          `unsafeApplyCode` (liftCodeDef (semanticsToDataAssocMap assocMapS))
    )
    (===)
    expected

elemsSpec :: Property
elemsSpec = property $ do
  assocMapS <- forAll genAssocMapS
  let assocMap = semanticsToAssocMap assocMapS
      expected = elemsS assocMapS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        elemsProgram
          `unsafeApplyCode` (liftCodeDef assocMap)
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        dataElemsProgram
          `unsafeApplyCode` (liftCodeDef (semanticsToDataAssocMap assocMapS))
    )
    (===)
    expected

filterSpec :: Property
filterSpec = property $ do
  assocMapS <- forAll genAssocMapS
  num <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
      expected = sortS $ filterS (< num) assocMapS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        filterProgram
          `unsafeApplyCode` (liftCodeDef num)
          `unsafeApplyCode` (liftCodeDef assocMap)
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        dataFilterProgram
          `unsafeApplyCode` (liftCodeDef num)
          `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    (===)
    expected

mapWithKeySpec :: Property
mapWithKeySpec = property $ do
  assocMapS <- forAll genAssocMapS
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
      expected = sortS $ mapWithKeyS (+) assocMapS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        mapWithKeyProgram
          `unsafeApplyCode` (liftCodeDef assocMap)
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        dataMapWithKeyProgram
          `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    (===)
    expected

mapMaybeSpec :: Property
mapMaybeSpec = property $ do
  assocMapS <- forAll genAssocMapS
  num <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
      expected = sortS $ mapMaybeS (\x -> if x < num then Just x else Nothing) assocMapS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        mapMaybeProgram
          `unsafeApplyCode` (liftCodeDef num)
          `unsafeApplyCode` (liftCodeDef assocMap)
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        dataMapMaybeProgram
          `unsafeApplyCode` (liftCodeDef num)
          `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    (===)
    expected

mapMaybeWithKeySpec :: Property
mapMaybeWithKeySpec = property $ do
  assocMapS <- forAll genAssocMapS
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
      expected = sortS $ mapMaybeWithKeyS (\k v -> if v < k then Just v else Nothing) assocMapS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        mapMaybeWithKeyProgram
          `unsafeApplyCode` (liftCodeDef assocMap)
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        dataMapMaybeWithKeyProgram
          `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    (===)
    expected

noDuplicateKeysSpec :: Property
noDuplicateKeysSpec = property $ do
  assocMapS <- forAll genAssocMapS
  let dataAssocMap = semanticsToDataAssocMap assocMapS
      expected = noDuplicateKeysS assocMapS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        dataNoDuplicateKeysProgram
          `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    (===)
    expected
