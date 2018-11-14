\begin{code}
module Builtin.Constant.Term where
\end{code}

## Imports

\begin{code}
open import Data.Nat hiding (_^_; _≤_; _<_; _>_; _≥_)
open import Agda.Builtin.Int
open import Data.Integer renaming (_*_ to _**_)
open import Data.Bool
open import Data.Product
open import Relation.Binary

open import Type
open import Builtin.Constant.Type
\end{code}

## Term Constants
\begin{code}
postulate
  ByteString : Set
  length     : ByteString → ℕ

  div            : Int → Int → Int
  quot           : Int → Int → Int
  rem            : Int → Int → Int
  mod            : Int → Int → Int
  int2ByteString : Int → ByteString

  append    : ByteString → ByteString → ByteString
  take      : Int → ByteString → ByteString
  drop      : Int → ByteString → ByteString
  SHA2-256  : ByteString → ByteString
  SHA3-256  : ByteString → ByteString
  verifySig : ByteString → ByteString → ByteString → Bool
  equals    : ByteString → ByteString → Bool

  txhash : ByteString
  bnum   : Int


{-# FOREIGN GHC import qualified Data.ByteString as BS #-}
{-# COMPILE GHC ByteString = type BS.ByteString #-}
{-# COMPILE GHC length = type BS.length #-}

{-# COMPILE GHC div  = type div  #-}
{-# COMPILE GHC quot = type quot #-}
{-# COMPILE GHC rem  = type rem  #-}
{-# COMPILE GHC mod  = type mod  #-}

{-# COMPILE GHC append = BS.append #-}
{-# COMPILE GHC take = BS.take #-}
{-# COMPILE GHC drop = BS.drop #-}


-- cut-off exponentiation
_^_ : Int → Int → Int
x ^ negsuc n      = pos 1
x ^ pos ℕ.zero    = pos 1
x ^ pos (ℕ.suc n) = x ** (x ^ pos n)


BoundedI : ∀ s i → Set
BoundedI s i =
  (negsuc 1 ^ (pos 8 ** (s ⊖ 1))) ≤ i × i < (pos 2 ^ (pos 8 ** (s ⊖ 1)))

BoundedN : ∀ s i → Set
BoundedN s i = pos 0 ≤ i × i < (pos 2 ^ (pos 8 ** (s ⊖ 1)))

BoundedB : ∀ s b → Set
BoundedB s b = length b Data.Nat.< s

-- TODO
postulate
  boundedI? : Decidable BoundedI
  boundedB? : Decidable BoundedB
  boundedN? : Decidable BoundedN

  _<?_ : Decidable _<_
  _>?_ : Decidable _>_
  _≥?_ : Decidable _≥_

  bN2I : ∀ s i → BoundedN s i → BoundedI s i 

data TermCon {Φ} : Φ ⊢⋆ * → Set where
  integer    : ∀ s
    → (i : Int)
    → BoundedI s i
    → TermCon (con integer (size⋆ s))
  bytestring : ∀ s
    → (b : ByteString)
    → BoundedB s b
    → TermCon (con bytestring (size⋆ s))
  size       : ∀ s → TermCon (con size (size⋆ s)) 
\end{code}
