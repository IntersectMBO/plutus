---
title: Builtins
layout: page
---

This module contains the formalisation of builtins.

```
module Builtin where
```

## Imports

```
open import Data.Bool using (Bool;true;false)
open import Data.Nat using (ℕ;suc)
open import Data.Fin using (Fin) renaming (zero to Z; suc to S)
open import Data.List.NonEmpty using (List⁺;_∷⁺_;[_];reverse)
open import Data.Product using (Σ;proj₁;proj₂)
open import Relation.Binary using (DecidableEquality)

open import Data.Bool using (Bool)
open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.String using (String)
open import Utils using (ByteString;Maybe;DATA;Bls12-381-G1-Element;Bls12-381-G2-Element;Bls12-381-MlResult;♯)
import Utils as U
open import Builtin.Signature using (Sig;sig;_⊢♯;_/_⊢⋆;Args)
                 using (integer;string;bytestring;unit;bool;pdata;bls12-381-g1-element;bls12-381-g2-element;bls12-381-mlresult)
open _⊢♯ renaming (pair to bpair; list to blist)
open _/_⊢⋆
open import Builtin.Constant.AtomicType 

open import Utils.Reflection using (defDec)
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
  -- BLS12_381
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
    ```
    
    ###Operators for constructing signatures
   
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

open SugaredSignature using (signature) public

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
                                          ) #-}
```

### Abstract semantics of builtins

We need to postulate the Agda type of built-in functions
whose semantics are provided by a Haskell function.

```
postulate
  lengthBS                  : ByteString → Int
  index                     : ByteString → Int → Int
  div                       : Int → Int → Int
  quot                      : Int → Int → Int
  rem                       : Int → Int → Int
  mod                       : Int → Int → Int

  TRACE                     : {a : Set} → String → a → a

  concat                    : ByteString → ByteString → ByteString
  cons                      : Int → ByteString → Maybe ByteString
  slice                     : Int → Int → ByteString → ByteString
  B<                        : ByteString → ByteString → Bool
  B<=                       : ByteString → ByteString → Bool
  SHA2-256                  : ByteString → ByteString
  SHA3-256                  : ByteString → ByteString
  BLAKE2B-256               : ByteString → ByteString
  verifyEd25519Sig          : ByteString → ByteString → ByteString → Maybe Bool
  verifyEcdsaSecp256k1Sig   : ByteString → ByteString → ByteString → Maybe Bool
  verifySchnorrSecp256k1Sig : ByteString → ByteString → ByteString → Maybe Bool
  equals                    : ByteString → ByteString → Bool
  ENCODEUTF8                : String → ByteString
  DECODEUTF8                : ByteString → Maybe String
  serialiseDATA             : DATA → ByteString
  BLS12-381-G1-add          : Bls12-381-G1-Element → Bls12-381-G1-Element → Bls12-381-G1-Element
  BLS12-381-G1-neg          : Bls12-381-G1-Element → Bls12-381-G1-Element
  BLS12-381-G1-scalarMul    : Int → Bls12-381-G1-Element → Bls12-381-G1-Element
  BLS12-381-G1-equal        : Bls12-381-G1-Element → Bls12-381-G1-Element → Bool
  BLS12-381-G1-hashToGroup  : ByteString → ByteString → Maybe Bls12-381-G1-Element
  BLS12-381-G1-compress     : Bls12-381-G1-Element → ByteString
  BLS12-381-G1-uncompress   : ByteString → Maybe Bls12-381-G1-Element -- FIXME: this really returns Either BLSTError Element
  BLS12-381-G2-add          : Bls12-381-G2-Element → Bls12-381-G2-Element → Bls12-381-G2-Element
  BLS12-381-G2-neg          : Bls12-381-G2-Element → Bls12-381-G2-Element
  BLS12-381-G2-scalarMul    : Int → Bls12-381-G2-Element → Bls12-381-G2-Element
  BLS12-381-G2-equal        : Bls12-381-G2-Element → Bls12-381-G2-Element → Bool
  BLS12-381-G2-hashToGroup  : ByteString → ByteString → Maybe Bls12-381-G2-Element
  BLS12-381-G2-compress     : Bls12-381-G2-Element → ByteString
  BLS12-381-G2-uncompress   : ByteString → Maybe Bls12-381-G2-Element -- FIXME: this really returns Either BLSTError Element
  BLS12-381-millerLoop      : Bls12-381-G1-Element → Bls12-381-G2-Element → Bls12-381-MlResult
  BLS12-381-mulMlResult     : Bls12-381-MlResult → Bls12-381-MlResult → Bls12-381-MlResult
  BLS12-381-finalVerify     : Bls12-381-MlResult → Bls12-381-MlResult → Bool
  KECCAK-256                : ByteString → ByteString
  BLAKE2B-224               : ByteString → ByteString
```

### What builtin operations should be compiled to if we compile to Haskell

```
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

-- The Vasil verification functions return results wrapped in Emitters, which
-- may perform a side-effect such as writing some text to a log.  The code below
-- provides an adaptor function which turns an Emitter (EvaluationResult r) into
-- Just r, where r is the real return type of the builtin.
-- TODO: deal directly with emitters in Agda?

{-# FOREIGN GHC import PlutusCore.Builtin (runEmitter) #-}
{-# FOREIGN GHC import PlutusCore.Evaluation.Result (EvaluationResult (EvaluationSuccess, EvaluationFailure)) #-}
{-# FOREIGN GHC emitterResultToMaybe = \e -> case fst e of {EvaluationSuccess r -> Just r; EvaluationFailure -> Nothing} #-}

{-# COMPILE GHC verifyEd25519Sig = \k m s -> emitterResultToMaybe . runEmitter $ verifyEd25519Signature_V2 k m s #-}
{-# COMPILE GHC verifyEcdsaSecp256k1Sig = \k m s -> emitterResultToMaybe . runEmitter $ verifyEcdsaSecp256k1Signature k m s #-}
{-# COMPILE GHC verifySchnorrSecp256k1Sig = \k m s -> emitterResultToMaybe . runEmitter $ verifySchnorrSecp256k1Signature k m s #-}

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

-- no binding needed for appendStr
-- no binding needed for traceStr
```

Equality of Builtins is decidable.
The following function is used for testing, when
comparing expected with actual results.

```
decBuiltin : DecidableEquality Builtin
unquoteDef decBuiltin = defDec (quote Builtin) decBuiltin
```
