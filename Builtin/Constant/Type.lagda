\begin{code}
module Builtin.Constant.Type where
\end{code}

## Imports

\begin{code}
open import Agda.Builtin.Int
open import Data.Integer hiding (_*_)
open import Data.Bool
open import Data.Product
open import Relation.Binary
open import Data.Nat hiding (_^_; _≤_; _<_; _>_; _≥_; _≤?_) renaming (_*_ to _**_)
open import Relation.Nullary
open import Function
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

  empty : ByteString
\end{code}

# What builtin operations should be compiled to if we compile to Haskell

\begin{code}
{-# FOREIGN GHC import qualified Data.ByteString as BS #-}
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
-- no binding needed for resize
-- no binding needed for sizeOf
-- TODO: intToByteString

{-# COMPILE GHC append = BS.append #-}
{-# COMPILE GHC take = BS.take . fromIntegral #-}
{-# COMPILE GHC drop = BS.drop . fromIntegral #-}
-- TODO: sha2-256
-- TODO: sha3-256
-- TODO: verifySig
-- TODO: resizeByteString
-- no binding needed for equalsByteString
{-# COMPILE GHC empty = BS.empty #-}
\end{code}

# Some integer operations missing from the standard library


\begin{code}
-- cut-off exponentiation
_^_ : ℕ → ℕ → ℕ
x ^ ℕ.zero  = 1
x ^ ℕ.suc n = x ** (x ^ n)

-≤0 : forall x -> - pos x ≤ pos 0
-≤0 ℕ.zero = +≤+ z≤n
-≤0 (ℕ.suc n) = -≤+

_<?_ : Decidable _<_
i <? j = Data.Integer.suc i ≤? j 

_>?_ : Decidable _>_
i >? j = j <? i

_≥?_ : Decidable _≥_
i ≥? j = j ≤? i 

trans≤Nat : ∀{i j k} → i Data.Nat.≤ j → j Data.Nat.≤ k → i Data.Nat.≤ k
trans≤Nat z≤n q = z≤n
trans≤Nat (s≤s p) (s≤s q) = s≤s (trans≤Nat p q)

trans≤Int : ∀{i j k} → i ≤ j → j ≤ k → i ≤ k
trans≤Int -≤+ (+≤+ q) = -≤+
trans≤Int (-≤- p) -≤+ = -≤+
trans≤Int (-≤- p) (-≤- q) = -≤- (trans≤Nat q p)
trans≤Int (+≤+ p) (+≤+ q) = +≤+ (trans≤Nat p q)
\end{code}

# Bounded integers and bytestrings

\begin{code}
open import Data.Unit hiding (_≤_;_≤?_)
BoundedI : (s : ℕ)(i : Int)  → Set
BoundedI s i = - (pos (2 ^ (8 ** (s ∸ 1)))) ≤ i × i < pos (2 ^ (8 ** (s ∸ 1)))

BoundedN : (s : ℕ)(i : ℤ) → Set
BoundedN s i =
  pos 0 ≤ i × i < pos (2 ^ (8 ** (s ∸ 1)))

BoundedB : (s : ℕ)(b : ByteString) → Set
BoundedB s b = length b Data.Nat.≤ s

boundedI? : Decidable BoundedI

boundedI? s i
  with (- pos (2 ^ (8 ** (s ∸ 1)))) ≤? i
  | i <? pos (2 ^ (8 ** (s ∸ 1)))
boundedI? s i | yes p | yes q = yes (p , q)
boundedI? s i | yes p | no ¬q = no (¬q ∘ proj₂)
boundedI? s i | no ¬p | _     = no (¬p ∘ proj₁)

boundedB? : Decidable BoundedB
boundedB? s b = length b Data.Nat.≤? s

boundedN? : Decidable BoundedN
boundedN? s i
  with pos 0 ≤? i
  | i <? pos (2 ^ (8 ** (s ∸ 1)))
boundedN? s i | yes p | yes q = yes (p , q)
boundedN? s i | yes p | no ¬q = no (¬q ∘ proj₂)
boundedN? s i | no ¬p | _     = no (¬p ∘ proj₁)

bN2I : ∀ s i → BoundedN s i → BoundedI s i 
bN2I s i (p , p') = trans≤Int (-≤0 (2 ^ (8 ** (s ∸ 1)))) p , p'
\end{code}

## Type constants

We have three base types referred to as type constants, integer,
bytestring, and size, size is used to limit the size of integers and
bytestrings

\begin{code}
data TyCon : Set where
  integer    : TyCon
  bytestring : TyCon
  size       : TyCon
\end{code}
