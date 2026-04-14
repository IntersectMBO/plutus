{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
-- CSE is very unstable and produces different output, likely depending on the version of either
-- @unordered-containers@ or @hashable@.
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}

module AssocMap.Properties1 where

import Hedgehog (Property, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Code (CompiledCode, unsafeApplyCode)
import PlutusTx.Data.AssocMap qualified as Data.AssocMap
import PlutusTx.IsData ()
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.List qualified as PlutusTx
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.TH (compile)
import PlutusTx.Test.Run.Code (evaluationResultMatchesHaskell)

import AssocMap.Semantics

lookupProgram :: CompiledCode (Integer -> AssocMap.Map Integer Integer -> Maybe Integer)
lookupProgram = $$(compile [||AssocMap.lookup||])

dataLookupProgram :: CompiledCode (Integer -> Data.AssocMap.Map Integer Integer -> Maybe Integer)
dataLookupProgram = $$(compile [||Data.AssocMap.lookup||])

memberProgram :: CompiledCode (Integer -> AssocMap.Map Integer Integer -> Bool)
memberProgram = $$(compile [||AssocMap.member||])

dataMemberProgram :: CompiledCode (Integer -> Data.AssocMap.Map Integer Integer -> Bool)
dataMemberProgram = $$(compile [||Data.AssocMap.member||])

insertProgram
  :: CompiledCode
       ( Integer
         -> Integer
         -> AssocMap.Map Integer Integer
         -> [(Integer, Integer)]
       )
insertProgram =
  $$( compile
        [||
        \k v m ->
          PlutusTx.sort $ AssocMap.toList $ AssocMap.insert k v m
        ||]
    )

dataInsertProgram
  :: CompiledCode
       ( Integer
         -> Integer
         -> Data.AssocMap.Map Integer Integer
         -> [(Integer, Integer)]
       )
dataInsertProgram =
  $$( compile
        [||
        \k v m ->
          PlutusTx.sort $ Data.AssocMap.toSOPList $ Data.AssocMap.insert k v m
        ||]
    )

deleteProgram
  :: CompiledCode
       ( Integer
         -> AssocMap.Map Integer Integer
         -> [(Integer, Integer)]
       )
deleteProgram =
  $$( compile
        [||
        \k m ->
          PlutusTx.sort $ AssocMap.toList $ AssocMap.delete k m
        ||]
    )

dataDeleteProgram
  :: CompiledCode
       ( Integer
         -> Data.AssocMap.Map Integer Integer
         -> [(Integer, Integer)]
       )
dataDeleteProgram =
  $$( compile
        [||
        \k m ->
          PlutusTx.sort $ Data.AssocMap.toSOPList $ Data.AssocMap.delete k m
        ||]
    )

allProgram
  :: CompiledCode
       ( Integer
         -> AssocMap.Map Integer Integer
         -> Bool
       )
allProgram =
  $$(compile [||\num m -> AssocMap.all (\x -> x PlutusTx.< num) m||])

dataAllProgram
  :: CompiledCode
       ( Integer
         -> Data.AssocMap.Map Integer Integer
         -> Bool
       )
dataAllProgram =
  $$(compile [||\num m -> Data.AssocMap.all (\x -> x PlutusTx.< num) m||])

dataAnyProgram
  :: CompiledCode
       ( Integer
         -> Data.AssocMap.Map Integer Integer
         -> Bool
       )
dataAnyProgram =
  $$(compile [||\num m -> Data.AssocMap.any (\x -> x PlutusTx.< num) m||])

lookupSpec :: Property
lookupSpec = property $ do
  assocMapS <- forAll genAssocMapS
  key <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
      expected = lookupS key assocMapS
  evaluationResultMatchesHaskell
    ( lookupProgram
        `unsafeApplyCode` liftCodeDef key
        `unsafeApplyCode` liftCodeDef assocMap
    )
    (===)
    expected
  evaluationResultMatchesHaskell
    ( dataLookupProgram
        `unsafeApplyCode` liftCodeDef key
        `unsafeApplyCode` liftCodeDef dataAssocMap
    )
    (===)
    expected

memberSpec :: Property
memberSpec = property $ do
  assocMapS <- forAll genAssocMapS
  key <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
      expected = memberS key assocMapS

  evaluationResultMatchesHaskell
    ( memberProgram
        `unsafeApplyCode` liftCodeDef key
        `unsafeApplyCode` liftCodeDef assocMap
    )
    (===)
    expected
  evaluationResultMatchesHaskell
    ( dataMemberProgram
        `unsafeApplyCode` liftCodeDef key
        `unsafeApplyCode` liftCodeDef dataAssocMap
    )
    (===)
    expected

insertSpec :: Property
insertSpec = property $ do
  assocMapS <- forAll genAssocMapS
  key <- forAll $ Gen.integral rangeElem
  value <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
      expected = sortS $ insertS key value assocMapS
  evaluationResultMatchesHaskell
    ( insertProgram
        `unsafeApplyCode` liftCodeDef key
        `unsafeApplyCode` liftCodeDef value
        `unsafeApplyCode` liftCodeDef assocMap
    )
    (===)
    expected
  evaluationResultMatchesHaskell
    ( dataInsertProgram
        `unsafeApplyCode` liftCodeDef key
        `unsafeApplyCode` liftCodeDef value
        `unsafeApplyCode` liftCodeDef dataAssocMap
    )
    (===)
    expected

deleteSpec :: Property
deleteSpec = property $ do
  assocMapS <- forAll genAssocMapS
  key <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
      expected = sortS $ deleteS key assocMapS
  evaluationResultMatchesHaskell
    ( deleteProgram
        `unsafeApplyCode` liftCodeDef key
        `unsafeApplyCode` liftCodeDef assocMap
    )
    (===)
    expected
  evaluationResultMatchesHaskell
    ( dataDeleteProgram
        `unsafeApplyCode` liftCodeDef key
        `unsafeApplyCode` liftCodeDef dataAssocMap
    )
    (===)
    expected

allSpec :: Property
allSpec = property $ do
  assocMapS <- forAll genAssocMapS
  num <- forAll $ Gen.integral rangeElem
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
      expected = allS (< num) assocMapS
  evaluationResultMatchesHaskell
    ( allProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef assocMap
    )
    (===)
    expected
  evaluationResultMatchesHaskell
    ( dataAllProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataAssocMap
    )
    (===)
    expected

anySpec :: Property
anySpec = property $ do
  assocMapS <- forAll genAssocMapS
  num <- forAll $ Gen.integral rangeElem
  let dataAssocMap = semanticsToDataAssocMap assocMapS
      expected = anyS (< num) assocMapS
  evaluationResultMatchesHaskell
    ( dataAnyProgram
        `unsafeApplyCode` liftCodeDef num
        `unsafeApplyCode` liftCodeDef dataAssocMap
    )
    (===)
    expected
