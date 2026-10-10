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
open import Data.Maybe using (Maybe;just;nothing)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ;suc)
open import Agda.Builtin.Nat using (_==_)
open import Data.Fin using (Fin) renaming (zero to Z; suc to S)
open import Data.List.NonEmpty using (List⁺;_∷⁺_;[_];reverse;length)
open import Data.Product using (Σ;proj₁;proj₂)
open import Relation.Binary using (DecidableEquality)

open import Data.Bool using (Bool; _∧_; if_then_else_)
open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.String using (String)
open import Utils using (ByteString;Maybe;DATA;Value;Bls12-381-G1-Element;Bls12-381-G2-Element;Bls12-381-MlResult;♯;Byte)
import Utils as U
open import Builtin.Signature using (Sig;sig;_⊢♯;_/_⊢⋆;Args)
                 using (integer;string;bytestring;unit;bool;pdata;value;bls12-381-g1-element;bls12-381-g2-element;bls12-381-mlresult)
open _⊢♯ renaming (pair to bpair; list to blist; array to barray)
open _/_⊢⋆
open import Builtin.Constant.AtomicType

open import Utils.Reflection using (defDec;defShow;defEnum;defListConstructors)
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
  lengthOfArray                   : Builtin
  listToArray                     : Builtin
  indexArray                      : Builtin
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
  -- Value
  insertCoin                      : Builtin
  lookupCoin                      : Builtin
  unionValue                      : Builtin
  valueContains                   : Builtin
  scaleValue                      : Builtin
  valueData                       : Builtin
  unValueData                     : Builtin
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
    signature chooseUnit                      = ∀A [ unit ↑ , A ]⟶ A
    signature trace                           = ∀A [ string ↑ , A ]⟶ A
    signature fstPair                         = ∀b,a [ pair b a ]⟶ b ↑
    signature sndPair                         = ∀b,a [ pair b a ]⟶ a ↑
    signature chooseList                      = ∀A,a [ list a , A , A ]⟶ A
    signature mkCons                          = ∀a [ a ↑ , list a ]⟶ list a
    signature headList                        = ∀a [ list a ]⟶ a ↑
    signature tailList                        = ∀a [ list a ]⟶ list a
    signature nullList                        = ∀a [ list a ]⟶ bool ↑
    signature lengthOfArray                   = ∀a [ array a ]⟶ integer ↑
    signature listToArray                     = ∀a [ list a ]⟶ array a
    signature indexArray                      = ∀a [ array a , integer ↑ ]⟶ a ↑
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
    signature insertCoin                      = ∙ [ bytestring ↑ , bytestring ↑ , integer ↑ , value ↑ ]⟶ value ↑
    signature lookupCoin                      = ∙ [ bytestring ↑ , bytestring ↑ , value ↑ ]⟶ integer ↑
    signature unionValue                      = ∙ [ value ↑ , value ↑ ]⟶ value ↑
    signature valueContains                   = ∙ [ value ↑ , value ↑ ]⟶ bool ↑
    signature scaleValue                      = ∙ [ integer ↑ , value ↑ ]⟶ value ↑
    signature valueData                       = ∙ [ value ↑ ]⟶ pdata ↑
    signature unValueData                     = ∙ [ pdata ↑ ]⟶ value ↑
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
                                          | InsertCoin
                                          | LookupCoin
                                          | UnionValue
                                          | ValueContains
                                          | ScaleValue
                                          | ValueData
                                          | UnValueData
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
  SHA2-256                    : ByteString → ByteString
  SHA3-256                    : ByteString → ByteString
  BLAKE2B-256                 : ByteString → ByteString
  verifyEd25519Sig            : ByteString → ByteString → ByteString → Maybe Bool
  verifyEcdsaSecp256k1Sig     : ByteString → ByteString → ByteString → Maybe Bool
  verifySchnorrSecp256k1Sig   : ByteString → ByteString → ByteString → Maybe Bool
  ENCODEUTF8                  : String → ByteString
  DECODEUTF8                  : ByteString → Maybe String
  serialiseDATA               : DATA → ByteString
  insertCOIN                  : ByteString → ByteString → Int → Value → Maybe Value
  lookupCOIN                  : ByteString → ByteString → Value → Int
  unionVALUE                  : Value → Value → Maybe Value
  valueCONTAINS               : Value → Value → Maybe Bool
  scaleVALUE                  : Int → Value → Maybe Value
  valueDATA                   : Value → Maybe DATA
  unValueDATA                 : DATA → Maybe Value
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

open ByteString
open Byte
open import Data.Integer.Base 
open import Relation.Nullary.Decidable using (does)

lengthBS : ByteString → Int
lengthBS [] = + 0
lengthBS (_ ∷ xs) = (+ 1) + lengthBS xs


-- no binding needed for addition
-- no binding needed for subtract
-- no binding needed for multiply
-- no binding needed for divide
-- no binding needed for quotient
-- no binding needed for remainder
-- no binding needed for mod
-- no binding needed for lessthan
-- no binding needed for lessthaneq
-- no binding needed for equals

concat : ByteString → ByteString → ByteString
concat [] ys = ys
concat (x ∷ xs) ys = x ∷ concat xs ys

{-# COMPILE GHC SHA2-256 = Hash.sha2_256 #-}
{-# COMPILE GHC SHA3-256 = Hash.sha3_256 #-}
{-# COMPILE GHC BLAKE2B-256 = Hash.blake2b_256 #-}

equals : ByteString → ByteString → Bool
equals = U.eqByteString

-- TODO: this is definitely not more readable than the PDF spec :(
B<= : ByteString → ByteString → Bool
B<= [] _ = true
B<= _ [] = false
B<= bs₁@(b₁ ∷ tail₁) bs₂@(b₂ ∷ tail₂) with
    ((+ 1) ≤ᵇ lengthBS bs₁) ∧ ((+ 1) ≤ᵇ lengthBS bs₂)
  ∧ (does (U.ᵇproj₁ b₁ Data.Bool.≤? U.ᵇproj₁ b₂))
... | true = true
... | false with 
    ((+ 1) ≤ᵇ lengthBS bs₁) ∧ ((+ 1) ≤ᵇ lengthBS bs₂)
  ∧ (does (U.ᵇproj₁ b₁ Data.Bool.≟ U.ᵇproj₁ b₂))
... | true = B<= tail₁ tail₂
... | false = false

B< : ByteString → ByteString → Bool
B< bs₁ bs₂ = B<= bs₁ bs₂ ∧ Data.Bool.not (equals bs₁ bs₂)

-- V1 of consByteString
-- {-# COMPILE GHC cons = \n xs -> BS.cons (fromIntegral @Integer n) xs #-}
-- The argument must be a valid byte value, i.e. in [0, 255]; otherwise the
-- builtin fails.

open import Data.Integer using (_≤?_)
open import Relation.Nullary.Decidable using (yes; no)

cons : Int → ByteString → Maybe ByteString
cons i xs with (+ 0) ≤? i
... | yes p = 
        if i ≤ᵇ (+ 255) then just (U.ℤToByte i ∷ xs) else nothing
    where
      instance _ = nonNegative p
... | no _ = nothing

slice : Int → Int → ByteString → ByteString
slice s k bs = U.take k (U.dropB s bs)

index : ByteString → Int → Maybe Int
index bs ix = Data.Maybe.map U.byteToℤ (go 0ℤ bs)
  where
    go : Int → ByteString → Maybe Byte
    go _ [] = nothing
    go n (x ∷ xs) =
      if does (n Data.Integer.≟ ix)
      then just x
      else go (n + 1ℤ) xs

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

{-# FOREIGN GHC import Codec.Serialise (serialise) #-}
{-# FOREIGN GHC import qualified Data.ByteString.Lazy as BSL #-}
{-# COMPILE GHC serialiseDATA = BSL.toStrict . serialise #-}

{-# FOREIGN GHC import PlutusCore.Value as Value #-}

{-# COMPILE GHC insertCOIN = \ccy tok x v -> builtinResultToMaybe $ Value.insertCoin ccy tok x v #-}
{-# COMPILE GHC lookupCOIN = Value.lookupCoin #-}
{-# COMPILE GHC unionVALUE = \v1 v2 -> builtinResultToMaybe $ Value.unionValue v1 v2 #-}
{-# COMPILE GHC valueCONTAINS = \v1 v2 -> builtinResultToMaybe $ Value.valueContains v1 v2 #-}
{-# COMPILE GHC scaleVALUE = \n v -> builtinResultToMaybe $ Value.scaleValue n v #-}
{-# COMPILE GHC valueDATA = \v -> builtinResultToMaybe $ Value.valueData v #-}
{-# COMPILE GHC unValueDATA = \d -> builtinResultToMaybe $ Value.unValueData d #-}

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

-- Bitwise operations and integer conversions (CIP-121, CIP-122, CIP-123).

open import Data.Integer using (_<?_)
open import Data.List using (foldr)
open import Data.Bool.ListAction using (all)

-- The number of bits in a bytestring.
bitLength : ByteString → Int
bitLength bs = lengthBS bs * (+ 8)

-- Is i a valid bit index for a bytestring with n bits?
validBitIndex : Int → Int → Bool
validBitIndex n i = (0ℤ ≤ᵇ i) ∧ does (i <? n)

-- The production implementation takes the shift/rotation amount as a 64-bit
-- Haskell `Int`, so amounts outside its range fail; we reproduce that here.
fitsInt : Int → Bool
fitsInt i = (-[1+ 9223372036854775807 ] ≤ᵇ i) ∧ (i ≤ᵇ + 9223372036854775807)

BStoI : Bool → ByteString → Int
BStoI true  bs = + U.byteStringToℕ bs
BStoI false bs = + U.byteStringToℕ (U.reverseBS bs)

ItoBS : Bool → Int → Int → Maybe ByteString
ItoBS e w n =
  if (0ℤ ≤ᵇ w) ∧ (w ≤ᵇ + 8192) ∧ (0ℤ ≤ᵇ n)
  then U.ℕToByteString e ∣ w ∣ ∣ n ∣
  else nothing

andBYTESTRING : Bool → ByteString → ByteString → ByteString
andBYTESTRING pad = U.zipWithBS U.andByte pad U.255B

orBYTESTRING : Bool → ByteString → ByteString → ByteString
orBYTESTRING pad = U.zipWithBS U.orByte pad U.0B

xorBYTESTRING : Bool → ByteString → ByteString → ByteString
xorBYTESTRING pad = U.zipWithBS U.xorByte pad U.0B

complementBYTESTRING : ByteString → ByteString
complementBYTESTRING = U.mapBS U.notByte

readBIT : ByteString → Int → Maybe Bool
readBIT bs i =
  if validBitIndex (bitLength bs) i
  then U.lookupBit (U.toBits bs) ∣ i ∣
  else nothing

writeBITS : ByteString → List Int → Bool → Maybe ByteString
writeBITS bs ixs u =
  if all (validBitIndex (bitLength bs)) ixs
  then just (U.fromBits (foldr (λ i → U.setBit ∣ i ∣ u) (U.toBits bs) ixs))
  else nothing

replicateBYTE : Int → Int → Maybe ByteString
replicateBYTE l w with U.toByte w
... | nothing = nothing
... | just b  =
  if (0ℤ ≤ᵇ l) ∧ (l ≤ᵇ + 8192)
  then just (U.replicateBS ∣ l ∣ b)
  else nothing

shiftBYTESTRING : ByteString → Int → Maybe ByteString
shiftBYTESTRING bs k =
  if fitsInt k
  then just (U.fromBits (U.shiftBits k (U.toBits bs)))
  else nothing

rotateBYTESTRING : ByteString → Int → Maybe ByteString
rotateBYTESTRING bs k =
  if fitsInt k
  then just (U.fromBits (U.rotateBits k (U.toBits bs)))
  else nothing

countSetBITS : ByteString → Int
countSetBITS []       = 0ℤ
countSetBITS (b ∷ bs) = (+ U.popCount b) + countSetBITS bs

findFirstSetBIT : ByteString → Int
findFirstSetBIT bs = U.firstSetBit (U.toBits bs)
```
A few examples, taken from the conformance tests.

```
private module BitwiseExamples where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Data.Nat using (ℕ)

  bs : List ℕ → ByteString
  bs []       = []
  bs (n ∷ ns) = U.ℕToByte n ∷ bs ns

  _ : andBYTESTRING false (bs (0x4f ∷ 0x00 ∷ [])) (bs (0xf4 ∷ [])) ≡ bs (0x44 ∷ [])
  _ = refl
  _ : andBYTESTRING true (bs (0x4f ∷ 0x00 ∷ [])) (bs (0xf4 ∷ [])) ≡ bs (0x44 ∷ 0x00 ∷ [])
  _ = refl
  _ : orBYTESTRING true (bs (0x4f ∷ 0x00 ∷ [])) (bs (0xf4 ∷ [])) ≡ bs (0xff ∷ 0x00 ∷ [])
  _ = refl
  _ : xorBYTESTRING false (bs (0x4f ∷ 0x00 ∷ [])) (bs (0xf4 ∷ [])) ≡ bs (0xbb ∷ [])
  _ = refl
  _ : xorBYTESTRING true [] (bs (0xff ∷ [])) ≡ bs (0xff ∷ [])
  _ = refl
  _ : complementBYTESTRING (bs (0xb0 ∷ 0x0b ∷ [])) ≡ bs (0x4f ∷ 0xf4 ∷ [])
  _ = refl

  _ : shiftBYTESTRING (bs (0xeb ∷ 0xfc ∷ [])) (+ 5) ≡ just (bs (0x7f ∷ 0x80 ∷ []))
  _ = refl
  _ : shiftBYTESTRING (bs (0xeb ∷ 0xfc ∷ [])) (- (+ 5)) ≡ just (bs (0x07 ∷ 0x5f ∷ []))
  _ = refl
  _ : shiftBYTESTRING (bs (0xeb ∷ 0xfc ∷ [])) (+ 16) ≡ just (bs (0x00 ∷ 0x00 ∷ []))
  _ = refl
  _ : shiftBYTESTRING (bs (0xeb ∷ 0xfc ∷ [])) (+ 9223372036854775808) ≡ nothing
  _ = refl
  _ : rotateBYTESTRING (bs (0xeb ∷ 0xfc ∷ [])) (+ 5) ≡ just (bs (0x7f ∷ 0x9d ∷ []))
  _ = refl
  _ : rotateBYTESTRING (bs (0xeb ∷ 0xfc ∷ [])) (- (+ 5)) ≡ just (bs (0xe7 ∷ 0x5f ∷ []))
  _ = refl
  _ : rotateBYTESTRING (bs (0xeb ∷ 0xfc ∷ [])) (+ 21) ≡ just (bs (0x7f ∷ 0x9d ∷ []))
  _ = refl
  _ : rotateBYTESTRING (bs (0xeb ∷ 0xfc ∷ [])) (- (+ 21)) ≡ just (bs (0xe7 ∷ 0x5f ∷ []))
  _ = refl
  _ : rotateBYTESTRING [] (- (+ 1)) ≡ just []
  _ = refl

  _ : readBIT (bs (0xf4 ∷ [])) (+ 0) ≡ just false
  _ = refl
  _ : readBIT (bs (0xf4 ∷ [])) (+ 2) ≡ just true
  _ = refl
  _ : readBIT (bs (0xf4 ∷ [])) (+ 8) ≡ nothing
  _ = refl
  _ : readBIT (bs (0xf4 ∷ 0xff ∷ [])) (+ 10) ≡ just true
  _ = refl
  _ : readBIT (bs (0xff ∷ [])) (- (+ 1)) ≡ nothing
  _ = refl
  _ : readBIT [] (+ 0) ≡ nothing
  _ = refl

  _ : writeBITS (bs (0xff ∷ [])) (+ 0 ∷ []) false ≡ just (bs (0xfe ∷ []))
  _ = refl
  _ : writeBITS (bs (0x00 ∷ [])) (+ 7 ∷ []) true ≡ just (bs (0x80 ∷ []))
  _ = refl
  _ : writeBITS (bs (0xf4 ∷ 0xff ∷ [])) (+ 10 ∷ + 1 ∷ []) false ≡ just (bs (0xf0 ∷ 0xfd ∷ []))
  _ = refl
  _ : writeBITS (bs (0xff ∷ [])) (+ 1 ∷ + 8 ∷ []) false ≡ nothing
  _ = refl
  _ : writeBITS [] [] true ≡ just []
  _ = refl
  _ : writeBITS [] (- (+ 1) ∷ []) true ≡ nothing
  _ = refl

  _ : replicateBYTE (+ 4) (+ 255) ≡ just (bs (0xff ∷ 0xff ∷ 0xff ∷ 0xff ∷ []))
  _ = refl
  _ : replicateBYTE (+ 0) (+ 255) ≡ just []
  _ = refl
  _ : replicateBYTE (+ 1) (+ 256) ≡ nothing
  _ = refl
  _ : replicateBYTE (- (+ 1)) (+ 0) ≡ nothing
  _ = refl
  _ : replicateBYTE (+ 8193) (+ 141) ≡ nothing
  _ = refl

  _ : countSetBITS (bs (0x01 ∷ 0x00 ∷ [])) ≡ + 1
  _ = refl
  _ : countSetBITS [] ≡ + 0
  _ = refl
  _ : findFirstSetBIT (bs (0xff ∷ 0xf2 ∷ [])) ≡ + 1
  _ = refl
  _ : findFirstSetBIT (bs (0x00 ∷ 0x00 ∷ [])) ≡ - (+ 1)
  _ = refl
  _ : findFirstSetBIT [] ≡ - (+ 1)
  _ = refl

  _ : BStoI true (bs (0x12 ∷ 0x34 ∷ [])) ≡ + 0x1234
  _ = refl
  _ : BStoI false (bs (0x12 ∷ 0x34 ∷ [])) ≡ + 0x3412
  _ = refl
  _ : BStoI true [] ≡ + 0
  _ = refl
  _ : ItoBS true (+ 5) (+ 0x123456) ≡ just (bs (0x00 ∷ 0x00 ∷ 0x12 ∷ 0x34 ∷ 0x56 ∷ []))
  _ = refl
  _ : ItoBS false (+ 5) (+ 0x123456) ≡ just (bs (0x56 ∷ 0x34 ∷ 0x12 ∷ 0x00 ∷ 0x00 ∷ []))
  _ = refl
  _ : ItoBS true (+ 0) (+ 0x123456) ≡ just (bs (0x12 ∷ 0x34 ∷ 0x56 ∷ []))
  _ = refl
  _ : ItoBS true (+ 2) (+ 0x123456) ≡ nothing
  _ = refl
  _ : ItoBS true (+ 0) (+ 0) ≡ just []
  _ = refl
  _ : ItoBS false (+ 3) (+ 0) ≡ just (bs (0x00 ∷ 0x00 ∷ 0x00 ∷ []))
  _ = refl
  _ : ItoBS true (+ 20) (- (+ 5)) ≡ nothing
  _ = refl
  _ : ItoBS true (+ 8193) (+ 0) ≡ nothing
  _ = refl
```

```

{-# COMPILE GHC RIPEMD-160 = Hash.ripemd_160 #-}
{-# FOREIGN GHC import PlutusCore.Crypto.ExpMod qualified as ExpMod #-}
-- here we explicitly do a Natural-check on m; the builtin machinery in plutus does such a check usually implicitly
-- but we cannot use the builtin machinery here.
{-# COMPILE GHC expModINTEGER = \b e m ->
    if m < 0
    then Nothing
    else fmap fromIntegral $ builtinResultToMaybe $ ExpMod.expMod b e (fromIntegral m) #-}

{-# COMPILE GHC BLS12-381-G1-multiScalarMul = \s p -> builtinResultToMaybe $ G1.multiScalarMul s p #-}
{-# COMPILE GHC BLS12-381-G2-multiScalarMul = \s p -> builtinResultToMaybe $ G2.multiScalarMul s p #-}

-- no binding needed for appendStr
-- no binding needed for traceStr
-- See Utils.List for the implementation of dropList
```

Equality of Builtins is decidable. In order to prove equality we would have to pattern match on n² cases, where n is the number of builtins. To avoid this, we identify each builtin with a natural number and defer to deciding equality on ℕ.

```

enumBuiltin : Builtin → ℕ
unquoteDef enumBuiltin = defEnum (quote Builtin) enumBuiltin

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.TrustMe using (primTrustMe)
open import Relation.Binary.PropositionalEquality using (cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)

-- TODO: this should be safe since enumBuiltin is generated; can it be proven without having to
-- explicitly match on all n² cases?
enumBuiltin-injective : (b1 b2 : Builtin) → enumBuiltin b1 ≡ enumBuiltin b2 → b1 ≡ b2
enumBuiltin-injective b1 b2 b1≡b2 = primTrustMe

decBuiltin : DecidableEquality Builtin
decBuiltin b1 b2 with (enumBuiltin b1) Data.Nat.≟ (enumBuiltin b2)
... | yes p = yes (enumBuiltin-injective b1 b2 p)
... | no np = no λ x → np (cong enumBuiltin x) 

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
