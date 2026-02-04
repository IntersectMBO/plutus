---
title: Builtins
layout: page
---

This module contains the formalisation of builtins.

```
module Builtin where
```


## TODO: add the rest of the builtins

After the metatheory is synced with the rest of the codebase, remove the following pragma:

```
{-# FOREIGN GHC {-# OPTIONS_GHC -Wno-incomplete-patterns #-} #-}
```

## Imports

```
open import Data.Bool using (Bool;true;false)
open import Data.List using (List)
open import Data.Nat using (ℕ;suc)
open import Data.Fin using (Fin) renaming (zero to Z; suc to S)
open import Data.List.NonEmpty using (List⁺;_∷⁺_;[_];reverse;length)
open import Data.Product using (Σ;proj₁;proj₂)
open import Relation.Binary using (DecidableEquality)

open import Data.Bool using (Bool)
open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.String using (String)
open import Utils using (ByteString;Maybe;DATA;Bls12-381-G1-Element;Bls12-381-G2-Element;Bls12-381-MlResult;♯)
import Utils as U
open import Builtin.Signature using (Sig;sig;_⊢♯;_/_⊢⋆;Args)
                 using (integer;string;bytestring;unit;bool;pdata;bls12-381-g1-element;bls12-381-g2-element;bls12-381-mlresult)
open _⊢♯ renaming (pair to bpair; list to blist; array to barray)
open _/_⊢⋆
open import Builtin.Constant.AtomicType

open import Utils.Reflection using (defDec;defShow;defListConstructors)
```

## Built-in functions

The type `Builtin` contains an enumeration of the built-in functions.

```
data Builtin : Set where
  -- Integers
  addInteger                      : Builtin
  subtractInteger                 : Builtin
  multiplyInteger                 : Builtin
  divideInteger                   : Builtin
  quotientInteger                 : Builtin
  remainderInteger                : Builtin
  modInteger                      : Builtin
  equalsInteger                   : Builtin
  lessThanInteger                 : Builtin
  lessThanEqualsInteger           : Builtin
  -- Bytestrings
  appendByteString                : Builtin
  consByteString                  : Builtin
  sliceByteString                 : Builtin
  lengthOfByteString              : Builtin
  indexByteString                 : Builtin
  equalsByteString                : Builtin
  lessThanByteString              : Builtin
  lessThanEqualsByteString        : Builtin
  -- Cryptography and hashes
  sha2-256                        : Builtin
  sha3-256                        : Builtin
  blake2b-256                     : Builtin
  verifyEd25519Signature          : Builtin
  verifyEcdsaSecp256k1Signature   : Builtin
  verifySchnorrSecp256k1Signature : Builtin
  -- String
  appendString                    : Builtin
  equalsString                    : Builtin
  encodeUtf8                      : Builtin
  decodeUtf8                      : Builtin
  -- Bool
  ifThenElse                      : Builtin
  -- Unit
  chooseUnit                      : Builtin
  -- Tracing
  trace                           : Builtin
  -- Pairs
  fstPair                         : Builtin
  sndPair                         : Builtin
  -- Lists
  chooseList                      : Builtin
  mkCons                          : Builtin
  headList                        : Builtin
  tailList                        : Builtin
  nullList                        : Builtin
  -- Arrays
  lengthOfArray             : Builtin
  listToArray                  : Builtin
  indexArray                  : Builtin
  -- Data
  chooseData                      : Builtin
  constrData                      : Builtin
  mapData                         : Builtin
  listData                        : Builtin
  iData                           : Builtin
  bData                           : Builtin
  unConstrData                    : Builtin
  unMapData                       : Builtin
  unListData                      : Builtin
  unIData                         : Builtin
  unBData                         : Builtin
  equalsData                      : Builtin
  serialiseData                   : Builtin
  -- Misc constructors
  mkPairData                      : Builtin
  mkNilData                       : Builtin
  mkNilPairData                   : Builtin
  -- Initial BLS12-381 operations
  -- G1
  bls12-381-G1-add                : Builtin
  bls12-381-G1-neg                : Builtin
  bls12-381-G1-scalarMul          : Builtin
  bls12-381-G1-equal              : Builtin
  bls12-381-G1-hashToGroup        : Builtin
  bls12-381-G1-compress           : Builtin
  bls12-381-G1-uncompress         : Builtin
  -- G2
  bls12-381-G2-add                : Builtin
  bls12-381-G2-neg                : Builtin
  bls12-381-G2-scalarMul          : Builtin
  bls12-381-G2-equal              : Builtin
  bls12-381-G2-hashToGroup        : Builtin
  bls12-381-G2-compress           : Builtin
  bls12-381-G2-uncompress         : Builtin
  -- Pairing
  bls12-381-millerLoop            : Builtin
  bls12-381-mulMlResult           : Builtin
  bls12-381-finalVerify           : Builtin
  -- Keccak-256, Blake2b-224
  keccak-256                      : Builtin
  blake2b-224                     : Builtin
  -- Bitwise operations
  byteStringToInteger             : Builtin
  integerToByteString             : Builtin
  andByteString                   : Builtin
  orByteString                    : Builtin
  xorByteString                   : Builtin
  complementByteString            : Builtin
  readBit                         : Builtin
  writeBits                       : Builtin
  replicateByte                   : Builtin
  shiftByteString                 : Builtin
  rotateByteString                : Builtin
  countSetBits                    : Builtin
  findFirstSetBit                 : Builtin
  -- Ripemd-160
  ripemd-160                      : Builtin
  -- Modular Exponentiation
  expModInteger                   : Builtin
  -- DropList
  dropList                        : Builtin
  -- BLS12-381 multi-scalar-multiplication
  bls12-381-G1-multiScalarMul     : Builtin
  bls12-381-G2-multiScalarMul     : Builtin

```

## Signatures

The following module defines a `signature` function assigning to each builtin an abstract type.

```
private module SugaredSignature where
```
Syntactic sugar for writing the signature of built-ins.
This is defined in its own module so that these definitions are not exported.

Signature types can have two kinds of polymorphic variables: variables that
range over arbitrary types (of kind *) and variables that range over builtin
types (of kind ♯). In order to distinguish them in the sugares syntax we write
with an uppercase variables of kind *, and with lowercase variables of kind ♯.

The arguments of signature types (argument types) are of type `n⋆ / n♯ ⊢⋆`, for
n⋆ free variables of kind *, and n♯ free variables of kind ♯. However,
shorthands for types, such  as `integer`, `bool`, etc are of type `n♯ ⊢♯`, and
hence need to be embedded into `n⋆ / n♯ ⊢⋆` using the postfix constructor `↑`.

```
    open import Data.Product using (_×_) renaming (_,_ to _,,_)

    -- number of different type variables
    ∙ ∀a ∀b,a ∀A ∀A,a : ℕ × ℕ
    ∙    = (0 ,, 0)
    ∀a   = (0 ,, 1)
    ∀b,a = (0 ,, 2)
    ∀A   = (1 ,, 0)
    ∀A,a = (1 ,, 1)

    -- names for type variables of kind ⋆
    A :  ∀{n⋆ n♯} → suc n⋆ / n♯ ⊢⋆
    A = ` Z

    B :  ∀{n⋆ n♯} → suc (suc n⋆) / n♯ ⊢⋆
    B = ` (S Z)

    -- names for type variables of kind ♯
    a : ∀{n♯} → suc n♯ ⊢♯
    a = ` Z

    b : ∀{n♯} → suc (suc n♯) ⊢♯
    b = ` (S Z)

    pair : ∀{n⋆ n♯} → n♯ ⊢♯ → n♯ ⊢♯ → n⋆ / n♯ ⊢⋆
    pair a b = (bpair a b) ↑

    list :  ∀{n⋆ n♯} → n♯ ⊢♯ → n⋆ / n♯ ⊢⋆
    list a = (blist a) ↑

    array :  ∀{n⋆ n♯} → n♯ ⊢♯ → n⋆ / n♯ ⊢⋆
    array a = (barray a) ↑
```

### Operators for constructing signatures

The following operators are used to express signatures in a familiar way,
but ultimately, they construct a Sig

An expression
  n⋆×n♯ [ t₁ , t₂ , t₃ ]⟶ tᵣ

is actually parsed as
  (((n⋆×n♯ [ t₁) , t₂) , t₃) ]⟶ tᵣ

and constructs a signature

sig n⋆ n♯ (t₃ ∷ t₂ ∷ t₁) tᵣ

```
    ArgSet : Set
    ArgSet = Σ (ℕ × ℕ) (λ { (n⋆ ,, n♯) → Args n⋆ n♯})

    ArgTy : ArgSet → Set
    ArgTy ((n⋆ ,, n♯) ,, _) = n⋆ / n♯ ⊢⋆

    infix 12 _[_
    _[_ : (nn : ℕ × ℕ)  → proj₁ nn / proj₂ nn ⊢⋆ → ArgSet
    _[_ (n⋆ ,, n♯) x = (n⋆ ,, n♯) ,, [ x ]

    infixl 10 _,_
    _,_ : (p : ArgSet) → ArgTy p → ArgSet
    _,_ ((n⋆ ,, n♯) ,, args) arg = (n⋆ ,, n♯) ,, arg  ∷⁺ args

    infix 8 _]⟶_
    _]⟶_ : (p : ArgSet) → ArgTy p → Sig
    _]⟶_ ((n⋆ ,, n♯) ,, as) res = sig n⋆ n♯ as res
```

    The signature of each builtin

```
    signature : Builtin → Sig
    signature addInteger                      = ∙ [ integer ↑ , integer ↑ ]⟶ integer ↑
    signature subtractInteger                 = ∙ [ integer ↑ , integer ↑ ]⟶ integer ↑
    signature multiplyInteger                 = ∙ [ integer ↑ , integer ↑ ]⟶ integer ↑
    signature divideInteger                   = ∙ [ integer ↑ , integer ↑ ]⟶ integer ↑
    signature quotientInteger                 = ∙ [ integer ↑ , integer ↑ ]⟶ integer ↑
    signature remainderInteger                = ∙ [ integer ↑ , integer ↑ ]⟶ integer ↑
    signature modInteger                      = ∙ [ integer ↑ , integer ↑ ]⟶ integer ↑
    signature equalsInteger                   = ∙ [ integer ↑ , integer ↑ ]⟶ bool ↑
    signature lessThanInteger                 = ∙ [ integer ↑ , integer ↑ ]⟶ bool ↑
    signature lessThanEqualsInteger           = ∙ [ integer ↑ , integer ↑ ]⟶ bool ↑
    signature appendByteString                = ∙ [ bytestring ↑ , bytestring ↑ ]⟶ bytestring ↑
    signature consByteString                  = ∙ [ integer ↑ , bytestring ↑ ]⟶ bytestring ↑
    signature sliceByteString                 = ∙ [ integer ↑ , integer ↑ , bytestring ↑ ]⟶ bytestring ↑
    signature lengthOfByteString              = ∙ [ bytestring ↑ ]⟶ integer ↑
    signature indexByteString                 = ∙ [ bytestring ↑ , integer ↑ ]⟶ integer ↑
    signature equalsByteString                = ∙ [ bytestring ↑ , bytestring ↑ ]⟶ bool ↑
    signature lessThanByteString              = ∙ [ bytestring ↑ , bytestring ↑ ]⟶ bool ↑
    signature lessThanEqualsByteString        = ∙ [ bytestring ↑ , bytestring ↑ ]⟶ bool ↑
    signature sha2-256                        = ∙ [ bytestring ↑ ]⟶ bytestring ↑
    signature sha3-256                        = ∙ [ bytestring ↑ ]⟶ bytestring ↑
    signature blake2b-224                     = ∙ [ bytestring ↑ ]⟶ bytestring ↑
    signature blake2b-256                     = ∙ [ bytestring ↑ ]⟶ bytestring ↑
    signature keccak-256                      = ∙ [ bytestring ↑ ]⟶ bytestring ↑
    signature ripemd-160                      = ∙ [ bytestring ↑ ]⟶ bytestring ↑
    signature verifyEd25519Signature          = ∙ [ bytestring ↑ , bytestring ↑ , bytestring ↑ ]⟶ bool ↑
    signature verifyEcdsaSecp256k1Signature   = ∙ [ bytestring ↑ , bytestring ↑ , bytestring ↑ ]⟶ bool ↑
    signature verifySchnorrSecp256k1Signature = ∙ [ bytestring ↑ , bytestring ↑ , bytestring ↑ ]⟶ bool ↑
    signature appendString                    = ∙ [ string ↑ , string ↑ ]⟶ string ↑
    signature equalsString                    = ∙ [ string ↑ , string ↑ ]⟶ bool ↑
    signature encodeUtf8                      = ∙ [ string ↑ ]⟶ bytestring ↑
    signature decodeUtf8                      = ∙ [ bytestring ↑ ]⟶ string ↑
    signature ifThenElse                      = ∀A [ bool ↑ , A , A ]⟶ A
    signature chooseUnit                      = ∀A [ A , unit ↑ ]⟶ A
    signature trace                           = ∀A [ string ↑ , A ]⟶ A
    signature fstPair                         = ∀b,a [ pair b a ]⟶ b ↑
    signature sndPair                         = ∀b,a [ pair b a ]⟶ a ↑
    signature chooseList                      = ∀A,a [ list a , A , A ]⟶ A
    signature mkCons                          = ∀a [ a ↑ , list a ]⟶ list a
    signature headList                        = ∀a [ list a ]⟶ a ↑
    signature tailList                        = ∀a [ list a ]⟶ list a
    signature nullList                        = ∀a [ list a ]⟶ bool ↑
    signature lengthOfArray              = ∀a [ array a ]⟶ integer ↑
    signature listToArray                   = ∀a [ list a ]⟶ array a
    signature indexArray                    = ∀a [ array a , integer ↑ ]⟶ a ↑
    signature chooseData                      = ∀A [ pdata ↑ , A , A , A , A , A ]⟶ A
    signature constrData                      = ∙ [ integer ↑ , list pdata ]⟶ pdata ↑
    signature mapData                         = ∙ [ list (bpair pdata pdata) ]⟶ pdata ↑
    signature listData                        = ∙ [ list pdata ]⟶ pdata ↑
    signature iData                           = ∙ [ integer ↑ ]⟶ pdata ↑
    signature bData                           = ∙ [ bytestring ↑ ]⟶ pdata ↑
    signature unConstrData                    = ∙ [ pdata ↑ ]⟶ pair integer (blist pdata)
    signature unMapData                       = ∙ [ pdata ↑ ]⟶ list (bpair pdata pdata)
    signature unListData                      = ∙ [ pdata ↑ ]⟶ list pdata
    signature unIData                         = ∙ [ pdata ↑ ]⟶ integer ↑
    signature unBData                         = ∙ [ pdata ↑ ]⟶ bytestring ↑
    signature equalsData                      = ∙ [ pdata ↑ , pdata ↑ ]⟶ bool ↑
    signature serialiseData                   = ∙ [ pdata ↑ ]⟶ bytestring ↑
    signature mkPairData                      = ∙ [ pdata ↑ , pdata ↑ ]⟶ pair pdata pdata
    signature mkNilData                       = ∙ [ unit ↑ ]⟶ list pdata
    signature mkNilPairData                   = ∙ [ unit ↑ ]⟶ list (bpair pdata pdata)
    signature bls12-381-G1-add                = ∙ [ bls12-381-g1-element ↑ , bls12-381-g1-element ↑ ]⟶ bls12-381-g1-element ↑
    signature bls12-381-G1-neg                = ∙ [ bls12-381-g1-element ↑ ]⟶ bls12-381-g1-element ↑
    signature bls12-381-G1-scalarMul          = ∙ [ integer ↑ , bls12-381-g1-element ↑ ]⟶ bls12-381-g1-element ↑
    signature bls12-381-G1-equal              = ∙ [ bls12-381-g1-element ↑ , bls12-381-g1-element ↑ ]⟶ bool ↑
    signature bls12-381-G1-hashToGroup        = ∙ [ bytestring ↑ , bytestring ↑ ]⟶ bls12-381-g1-element ↑
    signature bls12-381-G1-compress           = ∙ [ bls12-381-g1-element ↑ ]⟶ bytestring ↑
    signature bls12-381-G1-uncompress         = ∙ [ bytestring ↑ ]⟶ bls12-381-g1-element ↑
    signature bls12-381-G2-add                = ∙ [ bls12-381-g2-element ↑ , bls12-381-g2-element ↑ ]⟶ bls12-381-g2-element ↑
    signature bls12-381-G2-neg                = ∙ [ bls12-381-g2-element ↑ ]⟶ bls12-381-g2-element ↑
    signature bls12-381-G2-scalarMul          = ∙ [ integer ↑ , bls12-381-g2-element ↑ ]⟶ bls12-381-g2-element ↑
    signature bls12-381-G2-equal              = ∙ [ bls12-381-g2-element ↑ , bls12-381-g2-element ↑ ]⟶ bool ↑
    signature bls12-381-G2-hashToGroup        = ∙ [ bytestring ↑ , bytestring ↑ ]⟶ bls12-381-g2-element ↑
    signature bls12-381-G2-compress           = ∙ [ bls12-381-g2-element ↑ ]⟶ bytestring ↑
    signature bls12-381-G2-uncompress         = ∙ [ bytestring ↑ ]⟶ bls12-381-g2-element ↑
    signature bls12-381-millerLoop            = ∙ [ bls12-381-g1-element ↑ , bls12-381-g2-element ↑ ]⟶ bls12-381-mlresult ↑
    signature bls12-381-mulMlResult           = ∙ [ bls12-381-mlresult ↑ , bls12-381-mlresult ↑ ]⟶ bls12-381-mlresult ↑
    signature bls12-381-finalVerify           = ∙ [ bls12-381-mlresult ↑ , bls12-381-mlresult ↑ ]⟶ bool ↑
    signature byteStringToInteger             = ∙ [ bool ↑ , bytestring ↑ ]⟶ integer ↑
    signature integerToByteString             = ∙ [ bool ↑ , integer ↑ , integer ↑ ]⟶  bytestring ↑
    signature andByteString                   = ∙ [ bool ↑ , bytestring ↑ , bytestring ↑ ]⟶  bytestring ↑
    signature orByteString                    = ∙ [ bool ↑ , bytestring ↑ , bytestring ↑ ]⟶  bytestring ↑
    signature xorByteString                   = ∙ [ bool ↑ , bytestring ↑ , bytestring ↑ ]⟶  bytestring ↑
    signature complementByteString            = ∙ [ bytestring ↑ ]⟶  bytestring ↑
    signature readBit                         = ∙ [ bytestring ↑ , integer ↑ ]⟶  bool ↑
    signature writeBits                       = ∙ [ bytestring ↑ , list integer , bool ↑ ]⟶  bytestring ↑
    signature replicateByte                   = ∙ [ integer ↑ , integer ↑ ]⟶  bytestring ↑
    signature shiftByteString                 = ∙ [ bytestring ↑ , integer ↑ ]⟶  bytestring ↑
    signature rotateByteString                = ∙ [ bytestring ↑ , integer ↑ ]⟶  bytestring ↑
    signature countSetBits                    = ∙ [ bytestring ↑ ]⟶  integer ↑
    signature findFirstSetBit                 = ∙ [ bytestring ↑ ]⟶  integer ↑
    signature expModInteger                   = ∙ [ integer ↑ , integer ↑ , integer ↑ ]⟶  integer ↑
    signature dropList                        = ∀a [ integer ↑ , list a ]⟶ list a
    signature bls12-381-G1-multiScalarMul     = ∙ [ list integer , list bls12-381-g1-element ]⟶ bls12-381-g1-element ↑
    signature bls12-381-G2-multiScalarMul     = ∙ [ list integer , list bls12-381-g2-element ]⟶ bls12-381-g2-element ↑

open SugaredSignature using (signature) public

-- The number of type arguments expected
arity₀ : Builtin → ℕ
arity₀ b = (Sig.fv⋆ (signature b)) Data.Nat.+ (Sig.fv♯ (signature b))

-- This should be arity₁ but is left as arity because it is used
-- elsewhere
arity : Builtin → ℕ
arity b = length (Sig.args (signature b))

```

## GHC Mappings

Each Agda built-in name must be mapped to a Haskell name.

```
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
                                          | VerifyEd25519Signature
                                          | VerifyEcdsaSecp256k1Signature
                                          | VerifySchnorrSecp256k1Signature
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
                                          | LengthOfArray
                                          | ListToArray
                                          | IndexArray
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
                                          | SerialiseData
                                          | MkPairData
                                          | MkNilData
                                          | MkNilPairData
                                          | Bls12_381_G1_add
                                          | Bls12_381_G1_neg
                                          | Bls12_381_G1_scalarMul
                                          | Bls12_381_G1_equal
                                          | Bls12_381_G1_hashToGroup
                                          | Bls12_381_G1_compress
                                          | Bls12_381_G1_uncompress
                                          | Bls12_381_G2_add
                                          | Bls12_381_G2_neg
                                          | Bls12_381_G2_scalarMul
                                          | Bls12_381_G2_equal
                                          | Bls12_381_G2_hashToGroup
                                          | Bls12_381_G2_compress
                                          | Bls12_381_G2_uncompress
                                          | Bls12_381_millerLoop
                                          | Bls12_381_mulMlResult
                                          | Bls12_381_finalVerify
                                          | Keccak_256
                                          | Blake2b_224
                                          | ByteStringToInteger
                                          | IntegerToByteString
                                          | AndByteString
                                          | OrByteString
                                          | XorByteString
                                          | ComplementByteString
                                          | ReadBit
                                          | WriteBits
                                          | ReplicateByte
                                          | ShiftByteString
                                          | RotateByteString
                                          | CountSetBits
                                          | FindFirstSetBit
                                          | Ripemd_160
                                          | ExpModInteger
                                          | DropList
                                          | Bls12_381_G1_multiScalarMul
                                          | Bls12_381_G2_multiScalarMul
                                          ) #-}
```

### Abstract semantics of builtins

We need to postulate the Agda type of built-in functions
whose semantics are provided by a Haskell function.

```
postulate
  lengthBS                    : ByteString → Int
  index                       : ByteString → Int → Int
  div                         : Int → Int → Int
  quot                        : Int → Int → Int
  rem                         : Int → Int → Int
  mod                         : Int → Int → Int

  TRACE                       : {a : Set} → String → a → a

  concat                      : ByteString → ByteString → ByteString
  cons                        : Int → ByteString → Maybe ByteString
  slice                       : Int → Int → ByteString → ByteString
  B<                          : ByteString → ByteString → Bool
  B<=                         : ByteString → ByteString → Bool
  SHA2-256                    : ByteString → ByteString
  SHA3-256                    : ByteString → ByteString
  BLAKE2B-256                 : ByteString → ByteString
  verifyEd25519Sig            : ByteString → ByteString → ByteString → Maybe Bool
  verifyEcdsaSecp256k1Sig     : ByteString → ByteString → ByteString → Maybe Bool
  verifySchnorrSecp256k1Sig   : ByteString → ByteString → ByteString → Maybe Bool
  equals                      : ByteString → ByteString → Bool
  ENCODEUTF8                  : String → ByteString
  DECODEUTF8                  : ByteString → Maybe String
  serialiseDATA               : DATA → ByteString
  BLS12-381-G1-add            : Bls12-381-G1-Element → Bls12-381-G1-Element → Bls12-381-G1-Element
  BLS12-381-G1-neg            : Bls12-381-G1-Element → Bls12-381-G1-Element
  BLS12-381-G1-scalarMul      : Int → Bls12-381-G1-Element → Bls12-381-G1-Element
  BLS12-381-G1-equal          : Bls12-381-G1-Element → Bls12-381-G1-Element → Bool
  BLS12-381-G1-hashToGroup    : ByteString → ByteString → Maybe Bls12-381-G1-Element
  BLS12-381-G1-compress       : Bls12-381-G1-Element → ByteString
  BLS12-381-G1-uncompress     : ByteString → Maybe Bls12-381-G1-Element -- FIXME: this really returns Either BLSTError Element
  BLS12-381-G2-add            : Bls12-381-G2-Element → Bls12-381-G2-Element → Bls12-381-G2-Element
  BLS12-381-G2-neg            : Bls12-381-G2-Element → Bls12-381-G2-Element
  BLS12-381-G2-scalarMul      : Int → Bls12-381-G2-Element → Bls12-381-G2-Element
  BLS12-381-G2-equal          : Bls12-381-G2-Element → Bls12-381-G2-Element → Bool
  BLS12-381-G2-hashToGroup    : ByteString → ByteString → Maybe Bls12-381-G2-Element
  BLS12-381-G2-compress       : Bls12-381-G2-Element → ByteString
  BLS12-381-G2-uncompress     : ByteString → Maybe Bls12-381-G2-Element -- FIXME: this really returns Either BLSTError Element
  BLS12-381-millerLoop        : Bls12-381-G1-Element → Bls12-381-G2-Element → Bls12-381-MlResult
  BLS12-381-mulMlResult       : Bls12-381-MlResult → Bls12-381-MlResult → Bls12-381-MlResult
  BLS12-381-finalVerify       : Bls12-381-MlResult → Bls12-381-MlResult → Bool
  KECCAK-256                  : ByteString → ByteString
  BLAKE2B-224                 : ByteString → ByteString
  BStoI                       : Bool -> ByteString -> Int
  ItoBS                       : Bool -> Int -> Int -> Maybe ByteString
  andBYTESTRING               : Bool -> ByteString -> ByteString -> ByteString
  orBYTESTRING                : Bool -> ByteString -> ByteString -> ByteString
  xorBYTESTRING               : Bool -> ByteString -> ByteString -> ByteString
  complementBYTESTRING        : ByteString -> ByteString
  readBIT                     : ByteString -> Int -> Maybe Bool
  writeBITS                   : ByteString -> List Int -> Bool -> Maybe ByteString
  replicateBYTE               : Int -> Int -> Maybe ByteString
  shiftBYTESTRING             : ByteString -> Int -> ByteString
  rotateBYTESTRING            : ByteString -> Int -> ByteString
  countSetBITS                : ByteString -> Int
  findFirstSetBIT             : ByteString -> Int
  RIPEMD-160                  : ByteString → ByteString
  expModINTEGER               : Int -> Int -> Int -> Maybe Int
  BLS12-381-G1-multiScalarMul : List Int → List Bls12-381-G1-Element → Maybe Bls12-381-G1-Element
  BLS12-381-G2-multiScalarMul : List Int → List Bls12-381-G2-Element → Maybe Bls12-381-G2-Element
```

### What builtin operations should be compiled to if we compile to Haskell

```
{- Note [Fixed-width integral types in builtins in Agda].  Many of the
   denotations in PlutusCore.Default.Builtins involve arguments which are of
   fixed-width integral types such as Int or Word8. These all appear as
   `integer` in Plutus Core, and the builtin machinery handles the conversion
   from Haskell's `Integer` (the underlying type of `integer`) to the
   appropriate type automatically.  If a argument of this kind doesn't fit into
   the bounds of the relevant type then *an error will occur* at run-time; this
   happens for example with `consByteString`, where the first argument must be
   in the range [0..255].  To preserve the semantics here, a bounds check must
   be performed on `Int` arguments to builtins which expect an argument of some
   fixed-width argument; this can be done using `toIntegralSized`, for example.
-}

{-# FOREIGN GHC {-# LANGUAGE TypeApplications #-} #-}
{-# FOREIGN GHC import Control.Composition ((.*)) #-}
{-# FOREIGN GHC import qualified Data.ByteString as BS #-}
{-# FOREIGN GHC import Debug.Trace (trace) #-}
{-# FOREIGN GHC import PlutusCore.Crypto.Hash as Hash #-}
{-# FOREIGN GHC import Data.Text.Encoding #-}
{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# FOREIGN GHC import Data.Either.Extra (eitherToMaybe) #-}
{-# FOREIGN GHC import Data.Word (Word8) #-}
{-# FOREIGN GHC import Data.Bits (toIntegralSized) #-}
{-# COMPILE GHC lengthBS = toInteger . BS.length #-}

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


{-# COMPILE GHC TRACE = \_ s -> trace (Text.unpack s) #-}
{-# COMPILE GHC concat = BS.append #-}
{-# COMPILE GHC SHA2-256 = Hash.sha2_256 #-}
{-# COMPILE GHC SHA3-256 = Hash.sha3_256 #-}
{-# COMPILE GHC BLAKE2B-256 = Hash.blake2b_256 #-}
{-# COMPILE GHC equals = (==) #-}
{-# COMPILE GHC B< = (<) #-}
{-# COMPILE GHC B<= = (<=) #-}
-- V1 of consByteString
-- {-# COMPILE GHC cons = \n xs -> BS.cons (fromIntegral @Integer n) xs #-}
-- Other versions of consByteString
{-# COMPILE GHC cons = \n xs -> fmap (\w8 -> BS.cons w8 xs) (toIntegralSized n) #-}
{-# COMPILE GHC slice = \start n xs -> BS.take (fromIntegral n) (BS.drop (fromIntegral start) xs) #-}
{-# COMPILE GHC index = \xs n -> fromIntegral (BS.index xs (fromIntegral n)) #-}
{-# FOREIGN GHC import PlutusCore.Crypto.Ed25519 #-}
{-# FOREIGN GHC import PlutusCore.Crypto.Secp256k1 #-}

-- Some builtins return results wrapped in BuiltinResult, which may perform a side-effect such as
-- writing some text to a log.  The code below provides an adaptor function which turns a
-- BuiltinResult r into Just r, where r is the real return type of the builtin.
-- TODO: deal directly with emitters in Agda?

{-# FOREIGN GHC import PlutusPrelude (reoption) #-}
{-# FOREIGN GHC import PlutusCore.Builtin (BuiltinResult) #-}
{-# FOREIGN GHC builtinResultToMaybe :: BuiltinResult a -> Maybe a #-}
{-# FOREIGN GHC builtinResultToMaybe = reoption #-}

{-# COMPILE GHC verifyEd25519Sig = \k m s -> builtinResultToMaybe $ verifyEd25519Signature k m s #-}
{-# COMPILE GHC verifyEcdsaSecp256k1Sig = \k m s -> builtinResultToMaybe $ verifyEcdsaSecp256k1Signature k m s #-}
{-# COMPILE GHC verifySchnorrSecp256k1Sig = \k m s -> builtinResultToMaybe $ verifySchnorrSecp256k1Signature k m s #-}

{-# COMPILE GHC ENCODEUTF8 = encodeUtf8 #-}
{-# COMPILE GHC DECODEUTF8 = eitherToMaybe . decodeUtf8' #-}

{-# FOREIGN GHC import PlutusCore.Crypto.BLS12_381.G1 qualified as G1 #-}
{-# COMPILE GHC BLS12-381-G1-add = G1.add #-}
{-# COMPILE GHC BLS12-381-G1-neg = G1.neg #-}
{-# COMPILE GHC BLS12-381-G1-scalarMul = G1.scalarMul #-}
{-# COMPILE GHC BLS12-381-G1-equal = (==) #-}
{-# COMPILE GHC BLS12-381-G1-hashToGroup = eitherToMaybe .* G1.hashToGroup #-}
{-# COMPILE GHC BLS12-381-G1-compress = G1.compress #-}
{-# COMPILE GHC BLS12-381-G1-uncompress = eitherToMaybe . G1.uncompress #-}
{-# FOREIGN GHC import PlutusCore.Crypto.BLS12_381.G2 qualified as G2 #-}
{-# COMPILE GHC BLS12-381-G2-add = G2.add #-}
{-# COMPILE GHC BLS12-381-G2-neg = G2.neg #-}
{-# COMPILE GHC BLS12-381-G2-scalarMul = G2.scalarMul #-}
{-# COMPILE GHC BLS12-381-G2-equal = (==) #-}
{-# COMPILE GHC BLS12-381-G2-hashToGroup = eitherToMaybe .* G2.hashToGroup #-}
{-# COMPILE GHC BLS12-381-G2-compress = G2.compress #-}
{-# COMPILE GHC BLS12-381-G2-uncompress = eitherToMaybe . G2.uncompress #-}
{-# FOREIGN GHC import PlutusCore.Crypto.BLS12_381.Pairing qualified as Pairing #-}
{-# COMPILE GHC BLS12-381-millerLoop = Pairing.millerLoop #-}
{-# COMPILE GHC BLS12-381-mulMlResult = Pairing.mulMlResult #-}
{-# COMPILE GHC BLS12-381-finalVerify = Pairing.finalVerify #-}

{-# COMPILE GHC KECCAK-256 = Hash.keccak_256 #-}
{-# COMPILE GHC BLAKE2B-224 = Hash.blake2b_224 #-}

{-# FOREIGN GHC import PlutusCore.Bitwise qualified as Bitwise #-}
{-# COMPILE GHC BStoI = Bitwise.byteStringToInteger #-}
{-# COMPILE GHC ItoBS = \e w n -> builtinResultToMaybe $ Bitwise.integerToByteString e w n #-}
{-# COMPILE GHC andBYTESTRING = Bitwise.andByteString #-}
{-# COMPILE GHC orBYTESTRING = Bitwise.orByteString #-}
{-# COMPILE GHC xorBYTESTRING = Bitwise.xorByteString #-}
{-# COMPILE GHC complementBYTESTRING = Bitwise.complementByteString #-}
{-# COMPILE GHC readBIT = \s n -> builtinResultToMaybe $ Bitwise.readBit s (fromIntegral n) #-}
{-# COMPILE GHC writeBITS = \s ps u -> builtinResultToMaybe $ Bitwise.writeBits s (fmap fromIntegral ps) u #-}
-- The Plutus Core version of `replicateByte n w` can fail in two ways: if n < 0 or n >= 8192 then
-- the implementation PlutusCore.Bitwise will return BuiltinFailure; if w < 0 or w >= 256 then the
-- denotation in `PlutusCore.Default.Builtins` will fail when the builtin machinery tries to convert
-- it to a Word8.  We have to replicate this behaviour here. -}
{-# COMPILE GHC replicateBYTE = \n w8 ->
        case toIntegralSized w8 of { Nothing -> Nothing; Just w -> builtinResultToMaybe $ Bitwise.replicateByte n w } #-}
{-# COMPILE GHC shiftBYTESTRING = Bitwise.shiftByteString #-}
{-# COMPILE GHC rotateBYTESTRING = Bitwise.rotateByteString #-}
{-# COMPILE GHC countSetBITS = \s -> fromIntegral $ Bitwise.countSetBits s #-}
{-# COMPILE GHC findFirstSetBIT = \s -> fromIntegral $ Bitwise.findFirstSetBit s #-}

{-# COMPILE GHC RIPEMD-160 = Hash.ripemd_160 #-}
{-# FOREIGN GHC import PlutusCore.Crypto.ExpMod qualified as ExpMod #-}
-- here we explicitly do a Natural-check on m; the builtin machinery in plutus does such a check usually implicitly
-- but we cannot use the builtin machinery here.
{-# COMPILE GHC expModINTEGER = \b e m ->
    if m < 0
    then Nothing
    else fmap fromIntegral $ builtinResultToMaybe $ ExpMod.expMod b e (fromIntegral m) #-}

{-# COMPILE GHC BLS12-381-G1-multiScalarMul s p = builtinResultToMaybe $ G1.multiScalarMul s p #-}
{-# COMPILE GHC BLS12-381-G2-multiScalarMul s p = builtinResultToMaybe $ G2.multiScalarMul s p #-}

-- no binding needed for appendStr
-- no binding needed for traceStr
-- See Utils.List for the implementation of dropList
```

Equality of Builtins is decidable.
The following function is used for testing, when
comparing expected with actual results.

```
decBuiltin : DecidableEquality Builtin
unquoteDef decBuiltin = defDec (quote Builtin) decBuiltin
```

We define a show function for Builtins

```
showBuiltin : Builtin → String
unquoteDef showBuiltin = defShow (quote Builtin) showBuiltin
```

`builtinList` is a list with all builtins.

```
builtinList : List Builtin
unquoteDef builtinList = defListConstructors (quote Builtin) builtinList
```
