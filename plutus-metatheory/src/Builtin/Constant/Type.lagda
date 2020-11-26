\begin{code}
module Builtin.Constant.Type where
\end{code}

## Imports

\begin{code}
open import Agda.Builtin.Char
open import Agda.Builtin.Int
open import Agda.Builtin.String
open import Data.Integer using (ℤ;-_;+≤+;-≤+;-≤-;_<_;_>_;_≤?_;_<?_;_≥_;_≤_)
open import Data.Unit using (⊤)
open import Data.Bool using (Bool)
open import Data.Product
open import Relation.Binary
open import Data.Nat using (ℕ;_*_;z≤n;s≤s;zero;suc)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Function

open import Utils
\end{code}

## Abstract semantics of builtins

\begin{code}
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
  SHA2-256  : ByteString → ByteString
  SHA3-256  : ByteString → ByteString
  verifySig : ByteString → ByteString → ByteString → Maybe Bool
  equals    : ByteString → ByteString → Bool

  empty : ByteString
\end{code}

# What builtin operations should be compiled to if we compile to Haskell

\begin{code}
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

{-# FOREIGN GHC import Crypto #-}
{-# COMPILE GHC verifySig = verifySignature #-}

-- no binding needed for equalsByteString
{-# COMPILE GHC empty = BS.empty #-}

-- no binding needed for charToStr
-- no binding needed for appendStr
-- no binding needed for traceStr

\end{code}

# Some integer operations missing from the standard library


\begin{code}
_>?_ : Decidable _>_
i >? j = j <? i

_≥?_ : Decidable _≥_
i ≥? j = j ≤? i
\end{code}

## Type constants

We have six base types referred to as type constants:

\begin{code}
data TyCon : Set where
  integer    : TyCon
  bytestring : TyCon
  string     : TyCon
  char       : TyCon
  unit       : TyCon
  bool       : TyCon

{-# FOREIGN GHC {-# LANGUAGE GADTs, PatternSynonyms #-}                   #-}
{-# FOREIGN GHC import Language.PlutusCore                                #-}
{-# FOREIGN GHC type TypeBuiltin = Some (TypeIn DefaultUni)               #-}
{-# FOREIGN GHC pattern TyInteger    = Some (TypeIn DefaultUniInteger)    #-}
{-# FOREIGN GHC pattern TyByteString = Some (TypeIn DefaultUniByteString) #-}
{-# FOREIGN GHC pattern TyString     = Some (TypeIn DefaultUniString)     #-}
{-# FOREIGN GHC pattern TyChar       = Some (TypeIn DefaultUniChar)       #-}
{-# FOREIGN GHC pattern TyUnit       = Some (TypeIn DefaultUniUnit)       #-}
{-# FOREIGN GHC pattern TyBool       = Some (TypeIn DefaultUniBool)       #-}
{-# COMPILE GHC TyCon = data TypeBuiltin (TyInteger | TyByteString | TyString | TyChar | TyUnit | TyBool) #-}
\end{code}
