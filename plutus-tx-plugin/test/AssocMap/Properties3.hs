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

module AssocMap.Properties3 where

import Hedgehog (Property, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Builtins qualified as PlutusTx
import PlutusTx.Code
import PlutusTx.Data.AssocMap qualified as Data.AssocMap
import PlutusTx.IsData ()
import PlutusTx.IsData qualified as P
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.List qualified as PlutusTx
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Test.Util.Compiled (cekResultMatchesHaskellValue, compiledCodeToTerm,
                                    unsafeRunTermCek)
import PlutusTx.TH (compile)
import PlutusTx.These (These (..))

import AssocMap.Semantics

unionProgram
  :: CompiledCode
       ( AssocMap.Map Integer Integer
         -> AssocMap.Map Integer Integer
         -> [(Integer, These Integer Integer)]
       )
unionProgram =
  $$( compile
        [||
        \m1 m2 ->
          PlutusTx.sort $ AssocMap.toList $ AssocMap.union m1 m2
        ||]
    )

dataUnionProgram
  :: CompiledCode
       ( Data.AssocMap.Map Integer Integer
         -> Data.AssocMap.Map Integer Integer
         -> [(Integer, These Integer Integer)]
       )
dataUnionProgram =
  $$( compile
        [||
        \m1 m2 ->
          PlutusTx.sort $ Data.AssocMap.toSOPList $ Data.AssocMap.union m1 m2
        ||]
    )

unionWithProgram
  :: CompiledCode
       ( AssocMap.Map Integer Integer
         -> AssocMap.Map Integer Integer
         -> [(Integer, Integer)]
       )
unionWithProgram =
  $$( compile
        [||
        \m1 m2 ->
          PlutusTx.sort $ AssocMap.toList $ AssocMap.unionWith (\x _ -> x) m1 m2
        ||]
    )

dataUnionWithProgram
  :: CompiledCode
       ( Data.AssocMap.Map Integer Integer
         -> Data.AssocMap.Map Integer Integer
         -> [(Integer, Integer)]
       )
dataUnionWithProgram =
  $$( compile
        [||
        \m1 m2 ->
          PlutusTx.sort $ Data.AssocMap.toSOPList $ Data.AssocMap.unionWith (\x _ -> x) m1 m2
        ||]
    )

encodedDataAssocMap
  :: CompiledCode
       ( Data.AssocMap.Map Integer Integer
         -> PlutusTx.BuiltinData
       )
encodedDataAssocMap = $$(compile [||P.toBuiltinData||])

encodedAssocMap
  :: CompiledCode
       ( AssocMap.Map Integer Integer
         -> PlutusTx.BuiltinData
       )
encodedAssocMap = $$(compile [||P.toBuiltinData||])

mDecodedDataAssocMap
  :: CompiledCode
       ( Data.AssocMap.Map Integer Integer
         -> PlutusTx.Maybe [(Integer, Integer)]
       )
mDecodedDataAssocMap =
  $$( compile
        [||
        fmap (PlutusTx.sort . Data.AssocMap.toSOPList) . P.fromBuiltinData . P.toBuiltinData
        ||]
    )

mDecodedAssocMap
  :: CompiledCode
       ( AssocMap.Map Integer Integer
         -> PlutusTx.Maybe [(Integer, Integer)]
       )
mDecodedAssocMap =
  $$( compile
        [||
        fmap (PlutusTx.sort . AssocMap.toList) . P.fromBuiltinData . P.toBuiltinData
        ||]
    )

decodedDataAssocMap
  :: CompiledCode
       ( Data.AssocMap.Map Integer Integer
         -> [(Integer, Integer)]
       )
decodedDataAssocMap =
  $$( compile
        [||
        PlutusTx.sort . Data.AssocMap.toSOPList . P.unsafeFromBuiltinData . P.toBuiltinData
        ||]
    )

decodedAssocMap
  :: CompiledCode
       ( AssocMap.Map Integer Integer
         -> [(Integer, Integer)]
       )
decodedAssocMap =
  $$( compile
        [||
        PlutusTx.sort . AssocMap.toList . P.unsafeFromBuiltinData . P.toBuiltinData
        ||]
    )

unionSpec :: Property
unionSpec = property $ do
  -- resizing the generator for performance
  assocMapS1 <- forAll (Gen.resize 20 genAssocMapS)
  assocMapS2 <- forAll (Gen.resize 20 genAssocMapS)
  let assocMap1 = semanticsToAssocMap assocMapS1
      assocMap2 = semanticsToAssocMap assocMapS2
      dataAssocMap1 = semanticsToDataAssocMap assocMapS1
      dataAssocMap2 = semanticsToDataAssocMap assocMapS2
      expected = mapS haskellToPlutusThese $ sortS $ unionS assocMapS1 assocMapS2
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        unionProgram
          `unsafeApplyCode` (liftCodeDef assocMap1)
          `unsafeApplyCode` (liftCodeDef assocMap2)
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        dataUnionProgram
          `unsafeApplyCode` (liftCodeDef dataAssocMap1)
          `unsafeApplyCode` (liftCodeDef dataAssocMap2)
    )
    (===)
    expected

unionWithSpec :: Property
unionWithSpec = property $ do
  -- resizing the generator for performance
  assocMapS1 <- forAll (Gen.resize 20 genAssocMapS)
  assocMapS2 <- forAll (Gen.resize 20 genAssocMapS)
  let assocMap1 = semanticsToAssocMap assocMapS1
      assocMap2 = semanticsToAssocMap assocMapS2
      dataAssocMap1 = semanticsToDataAssocMap assocMapS1
      dataAssocMap2 = semanticsToDataAssocMap assocMapS2
      merge i1 _ = i1
      expected = unionWithS merge assocMapS1 assocMapS2
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        unionWithProgram
          `unsafeApplyCode` (liftCodeDef assocMap1)
          `unsafeApplyCode` (liftCodeDef assocMap2)
    )
    (===)
    expected
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        dataUnionWithProgram
          `unsafeApplyCode` (liftCodeDef dataAssocMap1)
          `unsafeApplyCode` (liftCodeDef dataAssocMap2)
    )
    (===)
    expected

builtinDataEncodingSpec :: Property
builtinDataEncodingSpec = property $ do
  assocMapS <- forAll genAssocMapS
  let assocMap = semanticsToAssocMap assocMapS
      dataAssocMap = semanticsToDataAssocMap assocMapS
  unsafeRunTermCek
    ( compiledCodeToTerm $
        encodedDataAssocMap `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    === unsafeRunTermCek
      ( compiledCodeToTerm $
          encodedAssocMap `unsafeApplyCode` (liftCodeDef assocMap)
      )
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        mDecodedAssocMap
          `unsafeApplyCode` (liftCodeDef assocMap)
    )
    (===)
    (Just assocMapS)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        mDecodedDataAssocMap
          `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    (===)
    (Just assocMapS)
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        decodedAssocMap
          `unsafeApplyCode` (liftCodeDef assocMap)
    )
    (===)
    assocMapS
  cekResultMatchesHaskellValue
    ( compiledCodeToTerm $
        decodedDataAssocMap
          `unsafeApplyCode` (liftCodeDef dataAssocMap)
    )
    (===)
    assocMapS
