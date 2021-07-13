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
open import Utils

data Builtin : Set where
  addInteger               : Builtin
  subtractInteger          : Builtin
  multiplyInteger          : Builtin
  divideInteger            : Builtin
  quotientInteger          : Builtin
  remainderInteger         : Builtin
  modInteger               : Builtin
  lessThanInteger          : Builtin
  lessThanEqualsInteger    : Builtin
  greaterThanInteger       : Builtin
  greaterThanEqualsInteger : Builtin
  equalsInteger            : Builtin
  concatenate              : Builtin
  takeByteString           : Builtin
  dropByteString           : Builtin
  lessThanByteString       : Builtin
  greaterThanByteString    : Builtin
  sha2-256                 : Builtin
  sha3-256                 : Builtin
  verifySignature          : Builtin
  equalsByteString         : Builtin
  ifThenElse               : Builtin
  charToString             : Builtin
  append                   : Builtin
  trace                    : Builtin

{-# FOREIGN GHC import PlutusCore.Default #-}
{-# COMPILE GHC Builtin = data DefaultFun (AddInteger
                                          | SubtractInteger
                                          | MultiplyInteger
                                          | DivideInteger
                                          | QuotientInteger
                                          | RemainderInteger
                                          | ModInteger
                                          | LessThanInteger
                                          | LessThanEqualsInteger
                                          | GreaterThanInteger
                                          | GreaterThanEqualsInteger
                                          | EqualsInteger
                                          | Concatenate
                                          | TakeByteString
                                          | DropByteString
                                          | LessThanByteString
                                          | GreaterThanByteString
                                          | Sha2_256
                                          | Sha3_256
                                          | VerifySignature
                                          | EqualsByteString
                                          | IfThenElse
                                          | CharToString
                                          | Append
                                          | Trace
                                          ) #-}
```

## Abstract semantics of builtins

```
postulate
  ByteString : Set
  length     : ByteString → ℕ

  div            : Int → Int → Int
  quot           : Int → Int → Int
  rem            : Int → Int → Int
  mod            : Int → Int → Int

  concat    : ByteString → ByteString → ByteString
  take      : Int → ByteString → ByteString
  drop      : Int → ByteString → ByteString
  B<        : ByteString -> ByteString -> Bool
  B>        : ByteString -> ByteString -> Bool
  SHA2-256  : ByteString → ByteString
  SHA3-256  : ByteString → ByteString
  verifySig : ByteString → ByteString → ByteString → Maybe Bool
  equals    : ByteString → ByteString → Bool

  empty : ByteString
```

# What builtin operations should be compiled to if we compile to Haskell

```
{-# FOREIGN GHC {-# LANGUAGE TypeApplications #-} #-}
{-# FOREIGN GHC import qualified Data.ByteString as BS #-}
{-# FOREIGN GHC import qualified Data.ByteArray as B #-}
{-# FOREIGN GHC import Debug.Trace (trace) #-}
{-# FOREIGN GHC import Crypto.Hash (SHA256, SHA3_256, hash) #-}
{-# COMPILE GHC ByteString = type BS.ByteString #-}
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
-- no binding needed for greaterthan
-- no binding needed for greaterthaneq
-- no binding needed for equals

{-# COMPILE GHC concat = BS.append #-}
{-# COMPILE GHC take = BS.take . fromIntegral #-}
{-# COMPILE GHC drop = BS.drop . fromIntegral #-}
{-# COMPILE GHC SHA2-256 = B.convert . hash @BS.ByteString @SHA256 #-}
{-# COMPILE GHC SHA3-256 = B.convert . hash @BS.ByteString @SHA3_256 #-}
{-# COMPILE GHC equals = (==) #-}
{-# COMPILE GHC B< = (<) #-}
{-# COMPILE GHC B> = (>) #-}

{-# FOREIGN GHC import Crypto #-}
{-# COMPILE GHC verifySig = verifySignature #-}

-- no binding needed for equalsByteString
{-# COMPILE GHC empty = BS.empty #-}

-- no binding needed for charToStr
-- no binding needed for appendStr
-- no binding needed for traceStr

```
