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
open import Data.Nat using (ℕ;suc)
open import Data.Fin using (Fin) renaming (zero to Z; suc to S)
open import Data.List.NonEmpty using (List⁺;_∷⁺_;[_];reverse)
open import Data.Product using (Σ;proj₁)

open import Data.Bool using (Bool)
open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.String using (String)
open import Utils using (ByteString;Maybe;DATA)
open import Builtin.Signature using (Sig;sig;_⊢♯;con;`;Args) 
import Builtin.Constant.Type ℕ (_⊢♯) as T
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
```

## Signatures

The following module defines a `signature` function assigning to each builtin an abstract type.

```
private module SugaredSignature where
```
Syntactic sugar for writing the signature of built-ins.
This is defined in its own module so that these definitions are not exported.

```
    open import Data.Product using (_×_) renaming (_,_ to _,,_)

    -- number of different type variables
    ∙ = 0
    ∀a = 1
    ∀b,a = 2

    -- shortened names for type constants and type constructors
    integer bool bytestring string unit pdata : ∀{n} → n ⊢♯
    integer = con T.integer
    bool = con T.bool
    bytestring = con T.bytestring
    string = con T.string
    unit = con T.unit
    pdata = con T.pdata

    pair : ∀{n} → n ⊢♯ → n ⊢♯ → n ⊢♯
    pair x y = con (T.pair x y)

    list : ∀{n} → n ⊢♯ → n ⊢♯
    list x = con (T.list x)

    -- names for type variables
    a : ∀{n} → suc n ⊢♯
    a = ` Z

    b : ∀{n} → suc (suc n) ⊢♯
    b = ` (S Z)
    ```
    
    ###Operators for constructing signatures
   
    The following operators are used to express signatures in a familiar way,
    but ultimately, they construct a Sig 

    An expression 
      n [ t₁ , t₂ , t₃ ]⟶ tᵣ
    
    is actually parsed as
      (((n [ t₁) , t₂) , t₃) ]⟶ tᵣ
    
    and constructs a signature

    sig n (t₃ ∷ t₂ ∷ t₁) tᵣ

    ```
    infix 12 _[_
    _[_ : (n : ℕ) → n ⊢♯ → Σ ℕ (λ n → Args n) 
    _[_ n x = n ,, [ x ]  

    infixl 10 _,_
    _,_ : (p : Σ ℕ (λ n → Args n)) → proj₁ p ⊢♯ → Σ ℕ (λ n → Args n)
    _,_ (n ,, args) arg = n ,, arg  ∷⁺ args

    infix 8 _]⟶_
    _]⟶_ : (p : Σ ℕ (λ n → Args n)) → proj₁ p ⊢♯ → Sig
    _]⟶_ (n ,, as) res = sig n as res
    ```

    The signature of each builtin

    ```
    signature : Builtin → Sig
    signature addInteger                      = ∙ [ integer , integer ]⟶ integer
    signature subtractInteger                 = ∙ [ integer , integer ]⟶ integer
    signature multiplyInteger                 = ∙ [ integer , integer ]⟶ integer
    signature divideInteger                   = ∙ [ integer , integer ]⟶ integer
    signature quotientInteger                 = ∙ [ integer , integer ]⟶ integer
    signature remainderInteger                = ∙ [ integer , integer ]⟶ integer
    signature modInteger                      = ∙ [ integer , integer ]⟶ integer
    signature equalsInteger                   = ∙ [ integer , integer ]⟶ bool
    signature lessThanInteger                 = ∙ [ integer , integer ]⟶ bool
    signature lessThanEqualsInteger           = ∙ [ integer , integer ]⟶ bool
    signature appendByteString                = ∙ [ bytestring , bytestring ]⟶ bytestring
    signature consByteString                  = ∙ [ integer , bytestring ]⟶ bytestring
    signature sliceByteString                 = ∙ [ integer , integer , bytestring ]⟶ bytestring                            
    signature lengthOfByteString              = ∙ [ bytestring ]⟶ integer
    signature indexByteString                 = ∙ [ bytestring , integer ]⟶ integer
    signature equalsByteString                = ∙ [ bytestring , bytestring ]⟶ bool
    signature lessThanByteString              = ∙ [ bytestring , bytestring ]⟶ bool
    signature lessThanEqualsByteString        = ∙ [ bytestring , bytestring ]⟶ bool
    signature sha2-256                        = ∙ [ bytestring ]⟶ bytestring
    signature sha3-256                        = ∙ [ bytestring ]⟶ bytestring
    signature blake2b-256                     = ∙ [ bytestring ]⟶ bytestring
    signature verifyEd25519Signature          = ∙ [ bytestring , bytestring , bytestring ]⟶ bool
    signature verifyEcdsaSecp256k1Signature   = ∙ [ bytestring , bytestring , bytestring ]⟶ bool
    signature verifySchnorrSecp256k1Signature = ∙ [ bytestring , bytestring , bytestring ]⟶ bool
    signature appendString                    = ∙ [ string , string ]⟶ string
    signature equalsString                    = ∙ [ string , string ]⟶ bool
    signature encodeUtf8                      = ∙ [ string ]⟶ bytestring
    signature decodeUtf8                      = ∙ [ bytestring ]⟶ string 
    signature ifThenElse                      = ∀a [ bool , a , a ]⟶ a
    signature chooseUnit                      = ∀a [ a , unit ]⟶ a
    signature trace                           = ∀a [ string , a ]⟶ a
    signature fstPair                         = ∀b,a [ pair b a ]⟶ b
    signature sndPair                         = ∀b,a [ pair b a ]⟶ a
    signature chooseList                      = ∀b,a [ list b , a , a ]⟶ a
    signature mkCons                          = ∀a [ a , list a ]⟶ list a
    signature headList                        = ∀a [ list a ]⟶ a
    signature tailList                        = ∀a [ list a ]⟶ list a
    signature nullList                        = ∀a [ list a ]⟶ bool
    signature chooseData                      = ∀a [ pdata , a , a , a , a , a ]⟶ a
    signature constrData                      = ∙ [ integer , list pdata ]⟶ pdata
    signature mapData                         = ∙ [ list (pair pdata pdata) ]⟶ pdata
    signature listData                        = ∙ [ list pdata ]⟶ pdata
    signature iData                           = ∙ [ integer ]⟶ pdata
    signature bData                           = ∙ [ bytestring ]⟶ pdata
    signature unConstrData                    = ∙ [ pdata ]⟶ pair integer (list pdata)
    signature unMapData                       = ∙ [ pdata ]⟶ list (pair pdata pdata)
    signature unListData                      = ∙ [ pdata ]⟶ list pdata
    signature unIData                         = ∙ [ pdata ]⟶ integer
    signature unBData                         = ∙ [ pdata ]⟶ bytestring
    signature equalsData                      = ∙ [ pdata , pdata ]⟶ bool
    signature serialiseData                   = ∙ [ pdata ]⟶ bytestring
    signature mkPairData                      = ∙ [ pdata , pdata ]⟶ pair pdata pdata
    signature mkNilData                       = ∙ [ unit ]⟶ list pdata
    signature mkNilPairData                   = ∙ [ unit ]⟶ list (pair pdata pdata)

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
                                          ) #-}
```

### Abstract semantics of builtins

We need to postulate the Agda type of built-in functions 
whose semantics are provided by a Haskell funciton.

```
postulate
  length     : ByteString → Int
  index      : ByteString → Int → Int
  div        : Int → Int → Int
  quot       : Int → Int → Int
  rem        : Int → Int → Int
  mod        : Int → Int → Int

  TRACE      : {a : Set} → String → a → a

  concat    : ByteString → ByteString → ByteString
  cons  : Int → ByteString → ByteString
  slice     : Int → Int → ByteString → ByteString
  B<        : ByteString -> ByteString -> Bool
  B<=        : ByteString -> ByteString -> Bool
  SHA2-256  : ByteString → ByteString
  SHA3-256  : ByteString → ByteString
  BLAKE2B-256  : ByteString → ByteString
  verifyEd25519Sig : ByteString → ByteString → ByteString → Maybe Bool
  verifyEcdsaSecp256k1Sig : ByteString → ByteString → ByteString → Maybe Bool
  verifySchnorrSecp256k1Sig : ByteString → ByteString → ByteString → Maybe Bool
  equals    : ByteString → ByteString → Bool
  ENCODEUTF8 : String → ByteString
  DECODEUTF8 : ByteString → Maybe String
  serialiseDATA : DATA → ByteString
```

### What builtin operations should be compiled to if we compile to Haskell

```
{-# FOREIGN GHC {-# LANGUAGE TypeApplications #-} #-}
{-# FOREIGN GHC import qualified Data.ByteString as BS #-}
{-# FOREIGN GHC import qualified Data.ByteArray as B #-}
{-# FOREIGN GHC import Debug.Trace (trace) #-}
{-# FOREIGN GHC import Data.ByteString.Hash as Hash #-}
{-# FOREIGN GHC import Data.Text.Encoding #-}
{-# FOREIGN GHC import qualified Data.Text as Text #-}
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


{-# COMPILE GHC TRACE = \_ s -> trace (Text.unpack s) #-}
{-# COMPILE GHC concat = BS.append #-}
{-# COMPILE GHC SHA2-256 = B.convert . Hash.sha2_256 #-}
{-# COMPILE GHC SHA3-256 = B.convert . Hash.sha3_256 #-}
{-# COMPILE GHC BLAKE2B-256 = B.convert . Hash.blake2b_256 #-}
{-# COMPILE GHC equals = (==) #-}
{-# COMPILE GHC B< = (<) #-}
{-# COMPILE GHC B<= = (<=) #-}
{-# COMPILE GHC cons = \n xs -> BS.cons (fromIntegral @Integer n) xs #-}
{-# COMPILE GHC slice = \start n xs -> BS.take (fromIntegral n) (BS.drop (fromIntegral start) xs) #-}
{-# COMPILE GHC index = \xs n -> fromIntegral (BS.index xs (fromIntegral n)) #-}
{-# FOREIGN GHC import Crypto #-}

-- The Vasil verification functions return results wrapped in Emitters, which
-- may perform a side-effect such as writing some text to a log.  The code below
-- provides an adaptor function which turns an Emitter (EvaluationResult r) into
-- Just r, where r is the real return type of the builtin.
-- TODO: deal directly with emitters in Agda?

{-# FOREIGN GHC import PlutusCore.Builtin (runEmitter) #-}
{-# FOREIGN GHC import PlutusCore.Evaluation.Result (EvaluationResult (EvaluationSuccess, EvaluationFailure)) #-}
{-# FOREIGN GHC emitterResultToMaybe = \e -> case fst e of {EvaluationSuccess r -> Just r; EvaluationFailure -> Nothing} #-}

{-# COMPILE GHC verifyEd25519Sig = \k m s -> emitterResultToMaybe . runEmitter $ verifyEd25519Signature_V1 k m s #-}
{-# COMPILE GHC verifyEcdsaSecp256k1Sig = \k m s -> emitterResultToMaybe . runEmitter $ verifyEcdsaSecp256k1Signature k m s #-}
{-# COMPILE GHC verifySchnorrSecp256k1Sig = \k m s -> emitterResultToMaybe . runEmitter $ verifySchnorrSecp256k1Signature k m s #-}

{-# COMPILE GHC ENCODEUTF8 = encodeUtf8 #-}
{-# COMPILE GHC DECODEUTF8 = eitherToMaybe . decodeUtf8' #-}

-- no binding needed for appendStr
-- no binding needed for traceStr
```
 