---
title: Builtins
layout: page
---

This module contains an enumeration of builtins.

```
module Builtin where

open import Data.Nat
open import Data.Bool
open import Agda.Builtin.Int
open import Agda.Builtin.String
open import Utils

data Builtin : Set where
  -- Integers
  addInteger               : Builtin
  subtractInteger          : Builtin
  multiplyInteger          : Builtin
  divideInteger            : Builtin
  quotientInteger          : Builtin
  remainderInteger         : Builtin
  modInteger               : Builtin
  equalsInteger            : Builtin
  lessThanInteger          : Builtin
  lessThanEqualsInteger    : Builtin
  -- Bytestrings
  appendByteString         : Builtin
  consByteString           : Builtin
  sliceByteString          : Builtin
  lengthOfByteString       : Builtin
  indexByteString          : Builtin
  equalsByteString         : Builtin
  lessThanByteString       : Builtin
  lessThanEqualsByteString : Builtin
  -- Cryptography and hashes
  sha2-256                 : Builtin
  sha3-256                 : Builtin
  blake2b-256              : Builtin
  verifySignature          : Builtin
  -- String
  appendString             : Builtin
  equalsString             : Builtin
  encodeUtf8               : Builtin
  decodeUtf8               : Builtin  
  -- Bool
  ifThenElse               : Builtin
  -- Tracing
  trace                    : Builtin
  -- Unit
  chooseUnit               : Builtin
  -- Pairs
  fstPair                  : Builtin
  sndPair                  : Builtin
  -- Lists
  chooseList               : Builtin
  mkCons                   : Builtin
  headList                 : Builtin
  tailList                 : Builtin
  nullList                 : Builtin
  -- Data
  chooseData               : Builtin
  constrData               : Builtin
  mapData                  : Builtin
  listData                 : Builtin
  iData                    : Builtin
  bData                    : Builtin
  unConstrData             : Builtin
  unMapData                : Builtin
  unListData               : Builtin
  unIData                  : Builtin
  unBData                  : Builtin
  equalsData               : Builtin
  -- Misc constructors
  mkPairData               : Builtin
  mkNilData                : Builtin
  mkNilPairData            : Builtin

{-# FOREIGN GHC import PlutusCore.Default #-}
{-# COMPILE GHC Builtin = data DefaultFun ( AddInteger
                                          | SubtractInteger
                                          | MultiplyInteger
                                          | DivideInteger
                                          | QuotientInteger
                                          | RemainderInteger
                                          | ModInteger
                                          | EqualsInteger
                                          | LessThanInteger
                                          | LessThanEqualsInteger
                                          | AppendByteString
                                          | ConsByteString
                                          | SliceByteString
                                          | LengthOfByteString
                                          | IndexByteString
                                          | EqualsByteString
                                          | LessThanByteString
                                          | LessThanEqualsByteString
                                          | Sha2_256
                                          | Sha3_256
                                          | Blake2b_256
                                          | VerifySignature
                                          | AppendString
                                          | EqualsString
                                          | EncodeUtf8
                                          | DecodeUtf8
                                          | IfThenElse
                                          | ChooseUnit
                                          | Trace
                                          | FstPair
                                          | SndPair
                                          | ChooseList
                                          | MkCons
                                          | HeadList
                                          | TailList
                                          | NullList
                                          | ChooseData
                                          | ConstrData
                                          | MapData
                                          | ListData
                                          | IData
                                          | BData
                                          | UnConstrData
                                          | UnMapData
                                          | UnListData
                                          | UnIData
                                          | UnBData
                                          | EqualsData
                                          | MkPairData
                                          | MkNilData
                                          | MkNilPairData
                                          ) #-}
```

## Abstract semantics of builtins

```
postulate
  length     : ByteString → Int
  index      : ByteString → Int → Int
  div            : Int → Int → Int
  quot           : Int → Int → Int
  rem            : Int → Int → Int
  mod            : Int → Int → Int

  concat    : ByteString → ByteString → ByteString
  cons  : Int → ByteString → ByteString
  slice     : Int → Int → ByteString → ByteString
  B<        : ByteString -> ByteString -> Bool
  B>        : ByteString -> ByteString -> Bool
  SHA2-256  : ByteString → ByteString
  SHA3-256  : ByteString → ByteString
  BLAKE2B-256  : ByteString → ByteString
  verifySig : ByteString → ByteString → ByteString → Maybe Bool
  equals    : ByteString → ByteString → Bool
  ENCODEUTF8 : String → ByteString
  DECODEUTF8 : ByteString → Maybe String
```

# What builtin operations should be compiled to if we compile to Haskell

```
{-# FOREIGN GHC {-# LANGUAGE TypeApplications #-} #-}
{-# FOREIGN GHC import qualified Data.ByteString as BS #-}
{-# FOREIGN GHC import qualified Data.ByteArray as B #-}
{-# FOREIGN GHC import Debug.Trace (trace) #-}
{-# FOREIGN GHC import Data.ByteString.Hash as Hash #-}
{-# FOREIGN GHC import Data.Text.Encoding #-}
{-# FOREIGN GHC import Data.Either.Extra #-}
{-# COMPILE GHC length = toInteger . BS.length #-}

-- no binding needed for addition
-- no binding needed for subtract
-- no binding needed for multiply

{-# COMPILE GHC div  = div  #-}
{-# COMPILE GHC quot = quot #-}
{-# COMPILE GHC rem  = rem  #-}
{-# COMPILE GHC mod  = mod  #-}

-- no binding needed for lessthan
-- no binding needed for lessthaneq
-- no binding needed for equals

{-# COMPILE GHC concat = BS.append #-}
{-# COMPILE GHC SHA2-256 = B.convert . Hash.sha2 #-}
{-# COMPILE GHC SHA3-256 = B.convert . Hash.sha3 #-}
{-# COMPILE GHC BLAKE2B-256 = B.convert . Hash.blake2b #-}
{-# COMPILE GHC equals = (==) #-}
{-# COMPILE GHC B< = (<) #-}
{-# COMPILE GHC B> = (>) #-}
{-# COMPILE GHC cons = \n xs -> BS.cons (fromIntegral @Integer n) xs #-}
{-# COMPILE GHC slice = \start n xs -> BS.take (fromIntegral n) (BS.drop (fromIntegral start) xs) #-}
{-# COMPILE GHC index = \xs n -> fromIntegral (BS.index xs (fromIntegral n)) #-}
{-# FOREIGN GHC import Crypto #-}
{-# COMPILE GHC verifySig = verifySignature #-}
{-# COMPILE GHC ENCODEUTF8 = encodeUtf8 #-}
{-# COMPILE GHC DECODEUTF8 = eitherToMaybe . decodeUtf8' #-}

-- no binding needed for appendStr
-- no binding needed for traceStr

```
