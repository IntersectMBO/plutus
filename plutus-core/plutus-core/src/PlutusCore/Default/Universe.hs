{-# OPTIONS -fno-warn-missing-pattern-synonym-signatures #-}
-- on 9.2.4 this is the flag that suppresses the above warning
{-# OPTIONS -Wno-missing-signatures #-}
-- 9.6 notices that all the constraints on 'TestTypesFromTheUniverseAreAllKnown'
-- are redundant (which they are), but we don't care because it only exists
-- to test that some constraints are solvable
{-# OPTIONS -Wno-redundant-constraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
#include "MachDeps.h"

-- effectfully: to the best of my experimentation, -O2 here improves
-- performance, but it's not clear why. This needs to be investigated.
{-# OPTIONS_GHC -O2 #-}

-- | The universe used by default and its instances.
module PlutusCore.Default.Universe
  ( DefaultUni (..)
  , DefaultBuiltinPattern (..)
  , pattern DefaultUniList
  , pattern DefaultUniArray
  , pattern DefaultUniPair
  , defaultUniSize
  , noMoreTypeFunctions
  , module Export -- Re-exporting universes infrastructure for convenience.
  ) where

import PlutusPrelude

import PlutusCore.Builtin
import PlutusCore.Core.Type (Type (..))
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Data (Data)
import PlutusCore.Data qualified as PLC
import PlutusCore.Default.Universe.Cardano
import PlutusCore.Evaluation.Machine.ExMemoryUsage
  ( DataNodeCount (..)
  , IntegerCostedLiterally (..)
  , NumBytesCostedAsNumWords (..)
  , TextCostedByByteLength (..)
  , ValueMaxDepth (..)
  , ValueTotalSize (..)
  )
import PlutusCore.Flat (Flat (..))
import PlutusCore.Flat.Decoder (dBEBits8, decodeListWith)
import PlutusCore.Flat.Encoder (encodeListWith)
import PlutusCore.Flat.Encoder.Strict (sizeListWith)
import PlutusCore.Flat.Types (NumBits)
import PlutusCore.FlatInstances (safeEncodeBits)
import PlutusCore.Pretty.Extra (juxtRenderContext)
import PlutusCore.Pretty.Utils (prettyBytes)
import PlutusCore.Value (Value)

import Control.Monad.Except (throwError)
import Data.ByteString (ByteString)
import Data.ByteString qualified as B
import Data.Hashable (Hashable (..))
import Data.Int
  ( Int16
  , Int32
  , Int64
  , Int8
  )
import Data.Proxy (Proxy (Proxy))
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Typeable (typeRep)
import Data.Vector qualified as Vector
import Data.Vector.Strict qualified as Strict (Vector)
import Data.Word (Word16, Word32)
import GHC.Exts (inline, oneShot)
import Prettyprinter (parens, sep, (<+>))
import Text.PrettyBy.Fixity
  ( RenderContext
  , inContextM
  , juxtPrettyM
  )
import Universe as Export

{- Note [PLC types and universes]
We encode built-in types in PLC as tags for Haskell types (the latter are also called meta-types),
see Note [Universes]. A built-in type in PLC is an inhabitant of

    Some (TypeIn uni)

where @uni@ is some universe, i.e. a collection of tags that have meta-types associated with them.

A value of a built-in type is a regular Haskell value stored in

    Some (ValueOf uni)

(together with the tag associated with its type) and such a value is also called a meta-constant.

The default universe has the following constructor (pattern synonym actually):

    DefaultUniList :: !(DefaultUni a) -> DefaultUni [a]

But note that this doesn't directly lead to interop between Plutus Core and Haskell, i.e. you can't
have a meta-list whose elements are of a PLC type. You can only have a meta-list constant with
elements of a meta-type (i.e. a type from the universe).

However it is possible to apply a built-in type to an arbitrary PLC/PIR type, since we can embed
a type of an arbitrary kind into 'Type' and then apply it via 'TyApp'. But we only use it to
get polymorphic built-in functions over polymorphic built-in types, since it's not possible
to juggle values of polymorphic built-in types instantiated with non-built-in types at runtime
(it's not even possible to represent such a value in the AST, even though it's possible to represent
such a 'Type').

Finally, it is not necessary to allow embedding PLC terms into meta-constants.
We already allow built-in functions with polymorphic types. There might be a way to utilize this
feature and have meta-constructors as built-in functions.
-}

-- See Note [Representing polymorphism].
-- | The universe used by default.
data DefaultUni a where
  DefaultUniInteger :: DefaultUni (Esc Integer)
  DefaultUniByteString :: DefaultUni (Esc ByteString)
  DefaultUniString :: DefaultUni (Esc Text)
  DefaultUniUnit :: DefaultUni (Esc ())
  DefaultUniBool :: DefaultUni (Esc Bool)
  DefaultUniProtoArray :: DefaultUni (Esc Strict.Vector)
  DefaultUniProtoList :: DefaultUni (Esc [])
  DefaultUniProtoPair :: DefaultUni (Esc (,))
  DefaultUniApply :: !(DefaultUni (Esc f)) -> !(DefaultUni (Esc a)) -> DefaultUni (Esc (f a))
  DefaultUniData :: DefaultUni (Esc Data)
  DefaultUniBLS12_381_G1_Element :: DefaultUni (Esc BLS12_381.G1.Element)
  DefaultUniBLS12_381_G2_Element :: DefaultUni (Esc BLS12_381.G2.Element)
  DefaultUniBLS12_381_MlResult :: DefaultUni (Esc BLS12_381.Pairing.MlResult)
  DefaultUniValue :: DefaultUni (Esc Value)

-- GHC infers crazy types for these two and the straightforward ones break pattern matching,
-- so we just leave GHC with its craziness.
pattern DefaultUniList uniA =
  DefaultUniProtoList `DefaultUniApply` uniA
pattern DefaultUniArray uniA =
  DefaultUniProtoArray `DefaultUniApply` uniA
pattern DefaultUniPair uniA uniB =
  DefaultUniProtoPair `DefaultUniApply` uniA `DefaultUniApply` uniB

{-| A complete, recursive pattern language for values in 'DefaultUni'. 'Match' is deliberately
built-in-only: UPLC constructors continue to use 'Case'. List-like patterns are exact, pair arity is
represented directly, and the optional payload patterns for @Data.I@ and @Data.B@ make malformed
arities unrepresentable. Pattern matching is incrementally metered as it traverses this raw syntax,
so the AST carries no cached or caller-supplied costing metadata. -}
data DefaultBuiltinPattern
  = DefaultPatternWildcard
  | DefaultPatternCapture
  | DefaultPatternInteger !Int64
  | DefaultPatternByteString !ByteString
  | DefaultPatternBool !Bool
  | DefaultPatternUnit
  | DefaultPatternList !(Vector.Vector DefaultBuiltinPattern)
  | DefaultPatternPair !DefaultBuiltinPattern !DefaultBuiltinPattern
  | DefaultPatternDataConstr !Word64 !(Vector.Vector DefaultBuiltinPattern)
  | DefaultPatternDataMap !(Vector.Vector DefaultBuiltinPattern)
  | DefaultPatternDataList !(Vector.Vector DefaultBuiltinPattern)
  | DefaultPatternDataI !(Maybe DefaultBuiltinPattern)
  | DefaultPatternDataB !(Maybe DefaultBuiltinPattern)
  deriving stock (Eq, Show, Generic)
  deriving anyclass (NFData)

-- 'Vector' deliberately has no blanket 'Hashable' instance in our dependency set, so hash the
-- serial order of structural children explicitly.
instance Hashable DefaultBuiltinPattern where
  hashWithSalt salt = \case
    DefaultPatternWildcard -> hashWithSalt salt (0 :: Int)
    DefaultPatternCapture -> hashWithSalt salt (1 :: Int)
    DefaultPatternInteger value -> salt `hashWithSalt` (2 :: Int) `hashWithSalt` value
    DefaultPatternByteString value -> salt `hashWithSalt` (3 :: Int) `hashWithSalt` value
    DefaultPatternBool value -> salt `hashWithSalt` (4 :: Int) `hashWithSalt` value
    DefaultPatternUnit -> hashWithSalt salt (5 :: Int)
    DefaultPatternList children ->
      hashChildren (hashWithSalt salt (6 :: Int)) children
    DefaultPatternPair left right ->
      salt `hashWithSalt` (7 :: Int) `hashWithSalt` left `hashWithSalt` right
    DefaultPatternDataConstr tag children ->
      hashChildren (salt `hashWithSalt` (8 :: Int) `hashWithSalt` tag) children
    DefaultPatternDataMap children ->
      hashChildren (hashWithSalt salt (9 :: Int)) children
    DefaultPatternDataList children ->
      hashChildren (hashWithSalt salt (10 :: Int)) children
    DefaultPatternDataI child -> salt `hashWithSalt` (11 :: Int) `hashWithSalt` child
    DefaultPatternDataB child -> salt `hashWithSalt` (12 :: Int) `hashWithSalt` child
    where
      hashChildren childSalt children =
        Vector.foldl' hashWithSalt (hashWithSalt childSalt $ Vector.length children) children

instance Pretty DefaultBuiltinPattern where
  pretty = \case
    DefaultPatternWildcard -> parens "wildcard"
    DefaultPatternCapture -> parens "bind"
    DefaultPatternInteger i -> parens $ "integer" <+> pretty i
    DefaultPatternByteString b -> parens $ "bytestring" <+> prettyBytes b
    DefaultPatternBool b -> parens $ "bool" <+> pretty b
    DefaultPatternUnit -> parens "unit"
    DefaultPatternList children -> prettyChildren "list" children
    DefaultPatternPair left right ->
      parens . sep $ ["pair", pretty left, pretty right]
    DefaultPatternDataConstr i children ->
      parens . sep $ "data-constr" : pretty i : prettyPatternChildren children
    DefaultPatternDataMap children -> prettyChildren "data-map" children
    DefaultPatternDataList children -> prettyChildren "data-list" children
    DefaultPatternDataI child -> prettyOptionalChild "data-i" child
    DefaultPatternDataB child -> prettyOptionalChild "data-b" child
    where
      prettyPatternChildren = fmap pretty . Vector.toList
      prettyChildren name children = parens . sep $ name : prettyPatternChildren children
      prettyOptionalChild name = parens . sep . (name :) . maybe [] (pure . pretty)

defaultBuiltinPatternTagWidth :: NumBits
defaultBuiltinPatternTagWidth = 4

instance Flat DefaultBuiltinPattern where
  encode = \case
    DefaultPatternWildcard -> tag 0
    DefaultPatternCapture -> tag 1
    DefaultPatternInteger i -> tag 2 <> encode i
    DefaultPatternByteString b -> tag 3 <> encode b
    DefaultPatternBool b -> tag 4 <> encode b
    DefaultPatternUnit -> tag 5
    DefaultPatternList children -> tag 6 <> encodeChildren children
    DefaultPatternPair left right -> tag 7 <> encode left <> encode right
    DefaultPatternDataConstr i children -> tag 8 <> encode i <> encodeChildren children
    DefaultPatternDataMap children -> tag 9 <> encodeChildren children
    DefaultPatternDataList children -> tag 10 <> encodeChildren children
    DefaultPatternDataI child -> tag 11 <> encodeOptionalChild child
    DefaultPatternDataB child -> tag 12 <> encodeOptionalChild child
    where
      tag = safeEncodeBits defaultBuiltinPatternTagWidth
      encodeChildren = encodeListWith encode . Vector.toList
      encodeOptionalChild = encodeListWith encode . maybe [] pure

  decode =
    dBEBits8 defaultBuiltinPatternTagWidth >>= \case
      0 -> pure DefaultPatternWildcard
      1 -> pure DefaultPatternCapture
      2 -> DefaultPatternInteger <$> decode
      3 -> DefaultPatternByteString <$> decode
      4 -> DefaultPatternBool <$> decode
      5 -> pure DefaultPatternUnit
      6 -> DefaultPatternList <$> decodeChildren
      7 -> DefaultPatternPair <$> decode <*> decode
      8 -> DefaultPatternDataConstr <$> decode <*> decodeChildren
      9 -> DefaultPatternDataMap <$> decodeChildren
      10 -> DefaultPatternDataList <$> decodeChildren
      11 -> DefaultPatternDataI <$> decodeOptionalChild
      12 -> DefaultPatternDataB <$> decodeOptionalChild
      tag -> fail $ "Unknown default built-in pattern tag: " ++ show tag
    where
      decodeChildren = Vector.fromList <$> decodeListWith decode
      decodeOptionalChild =
        decodeListWith decode >>= \case
          [] -> pure Nothing
          [child] -> pure $ Just child
          _ -> fail "Default Data.I/Data.B pattern takes at most one child"

  size pat sz =
    let sz' = defaultBuiltinPatternTagWidth + sz
     in case pat of
          DefaultPatternWildcard -> sz'
          DefaultPatternCapture -> sz'
          DefaultPatternInteger i -> size i sz'
          DefaultPatternByteString b -> size b sz'
          DefaultPatternBool b -> size b sz'
          DefaultPatternUnit -> sz'
          DefaultPatternList children -> sizeChildren children sz'
          DefaultPatternPair left right -> size left $ size right sz'
          DefaultPatternDataConstr i children -> size i $ sizeChildren children sz'
          DefaultPatternDataMap children -> sizeChildren children sz'
          DefaultPatternDataList children -> sizeChildren children sz'
          DefaultPatternDataI child -> sizeOptionalChild child sz'
          DefaultPatternDataB child -> sizeOptionalChild child sz'
    where
      sizeChildren = sizeListWith size . Vector.toList
      sizeOptionalChild = sizeListWith size . maybe [] pure

defaultUniSize :: forall k (a :: k). DefaultUni (Esc a) -> Int
defaultUniSize = \case
  DefaultUniApply uniF uniA -> defaultUniSize uniF + defaultUniSize uniA + 1
  _ -> 1

-- Removing 'LoopBreaker' didn't change anything at the time this comment was written, but we kept
-- it, because it hopefully provides some additional assurance that 'geqL' will not get elaborated
-- as a recursive definition.
instance AllBuiltinArgs DefaultUni (GEqL DefaultUni) a => GEqL DefaultUni a where
  geqL DefaultUniInteger a2 = do
    DefaultUniInteger <- pure a2
    pure Refl
  geqL DefaultUniByteString a2 = do
    DefaultUniByteString <- pure a2
    pure Refl
  geqL DefaultUniString a2 = do
    DefaultUniString <- pure a2
    pure Refl
  geqL DefaultUniUnit a2 = do
    DefaultUniUnit <- pure a2
    pure Refl
  geqL DefaultUniBool a2 = do
    DefaultUniBool <- pure a2
    pure Refl
  geqL (DefaultUniProtoList `DefaultUniApply` a1) listA2 = do
    DefaultUniProtoList `DefaultUniApply` a2 <- pure listA2
    Refl <- geqL (LoopBreaker a1) (LoopBreaker a2)
    pure Refl
  geqL (DefaultUniProtoArray `DefaultUniApply` a1) arrayA2 = do
    DefaultUniProtoArray `DefaultUniApply` a2 <- pure arrayA2
    Refl <- geqL (LoopBreaker a1) (LoopBreaker a2)
    pure Refl
  geqL (DefaultUniProtoPair `DefaultUniApply` a1 `DefaultUniApply` b1) pairA2 = do
    DefaultUniProtoPair `DefaultUniApply` a2 `DefaultUniApply` b2 <- pure pairA2
    Refl <- geqL (LoopBreaker a1) (LoopBreaker a2)
    Refl <- geqL (LoopBreaker b1) (LoopBreaker b2)
    pure Refl
  geqL (f `DefaultUniApply` _ `DefaultUniApply` _ `DefaultUniApply` _) _ =
    noMoreTypeFunctions f
  geqL DefaultUniData a2 = do
    DefaultUniData <- pure a2
    pure Refl
  geqL DefaultUniBLS12_381_G1_Element a2 = do
    DefaultUniBLS12_381_G1_Element <- pure a2
    pure Refl
  geqL DefaultUniBLS12_381_G2_Element a2 = do
    DefaultUniBLS12_381_G2_Element <- pure a2
    pure Refl
  geqL DefaultUniBLS12_381_MlResult a2 = do
    DefaultUniBLS12_381_MlResult <- pure a2
    pure Refl
  geqL DefaultUniValue a2 = do
    DefaultUniValue <- pure a2
    pure Refl
  {-# INLINE geqL #-}

instance GEq DefaultUni where
  -- We define 'geq' manually instead of using 'deriveGEq', because the latter creates a single
  -- recursive definition and we want two instead. The reason why we want two is because this
  -- allows GHC to inline the initial step that appears non-recursive to GHC, because recursion
  -- is hidden in the other function that is marked as @OPAQUE@ and is chosen by GHC as a
  -- loop-breaker, see https://wiki.haskell.org/Inlining_and_Specialisation#What_is_a_loop-breaker
  -- (we're not really sure if this is a reliable solution, but if it stops working, we won't miss
  -- very much and we've failed to settle on any other approach).
  --
  -- On the critical path this definition should only be used for builtins that perform equality
  -- checking of statically unknown runtime type tags ('MkCons' is one such builtin for
  -- example). All other builtins should use 'geqL' (the latter is internal to 'readKnownConstant'
  -- and is therefore hidden from the person adding a new builtin).
  --
  -- We use @NOINLINE@ instead of @OPAQUE@, because we don't actually care about the recursive
  -- definition not being inlined, we just want it to be chosen as the loop breaker.
  geq = goStep
    where
      goStep, goRec :: DefaultUni a1 -> DefaultUni a2 -> Maybe (a1 :~: a2)
      goStep DefaultUniInteger a2 = do
        DefaultUniInteger <- pure a2
        pure Refl
      goStep DefaultUniByteString a2 = do
        DefaultUniByteString <- pure a2
        pure Refl
      goStep DefaultUniString a2 = do
        DefaultUniString <- pure a2
        pure Refl
      goStep DefaultUniUnit a2 = do
        DefaultUniUnit <- pure a2
        pure Refl
      goStep DefaultUniBool a2 = do
        DefaultUniBool <- pure a2
        pure Refl
      goStep DefaultUniProtoList a2 = do
        DefaultUniProtoList <- pure a2
        pure Refl
      goStep DefaultUniProtoArray a2 = do
        DefaultUniProtoArray <- pure a2
        pure Refl
      goStep DefaultUniProtoPair a2 = do
        DefaultUniProtoPair <- pure a2
        pure Refl
      goStep (DefaultUniApply f1 x1) a2 = do
        DefaultUniApply f2 x2 <- pure a2
        Refl <- goRec f1 f2
        Refl <- goRec x1 x2
        pure Refl
      goStep DefaultUniData a2 = do
        DefaultUniData <- pure a2
        pure Refl
      goStep DefaultUniBLS12_381_G1_Element a2 = do
        DefaultUniBLS12_381_G1_Element <- pure a2
        pure Refl
      goStep DefaultUniBLS12_381_G2_Element a2 = do
        DefaultUniBLS12_381_G2_Element <- pure a2
        pure Refl
      goStep DefaultUniBLS12_381_MlResult a2 = do
        DefaultUniBLS12_381_MlResult <- pure a2
        pure Refl
      goStep DefaultUniValue a2 = do
        DefaultUniValue <- pure a2
        pure Refl
      {-# INLINE goStep #-}

      goRec = goStep
      {-# NOINLINE goRec #-}

-- | For pleasing the coverage checker.
noMoreTypeFunctions :: DefaultUni (Esc (f :: a -> b -> c -> d)) -> any
noMoreTypeFunctions (f `DefaultUniApply` _) = noMoreTypeFunctions f

instance ToKind DefaultUni where
  toSingKind DefaultUniInteger = knownKind
  toSingKind DefaultUniByteString = knownKind
  toSingKind DefaultUniString = knownKind
  toSingKind DefaultUniUnit = knownKind
  toSingKind DefaultUniBool = knownKind
  toSingKind DefaultUniProtoList = knownKind
  toSingKind DefaultUniProtoArray = knownKind
  toSingKind DefaultUniProtoPair = knownKind
  toSingKind (DefaultUniApply uniF _) = case toSingKind uniF of _ `SingKindArrow` cod -> cod
  toSingKind DefaultUniData = knownKind
  toSingKind DefaultUniBLS12_381_G1_Element = knownKind
  toSingKind DefaultUniBLS12_381_G2_Element = knownKind
  toSingKind DefaultUniBLS12_381_MlResult = knownKind
  toSingKind DefaultUniValue = knownKind

instance HasUniApply DefaultUni where
  uniApply = DefaultUniApply

  matchUniApply (DefaultUniApply f a) _ h = h f a
  matchUniApply _ z _ = z

deriving stock instance Show (DefaultUni a)
instance GShow DefaultUni where gshowsPrec = showsPrec

instance PrettyBy RenderContext (DefaultUni a) where
  prettyBy = inContextM $ \case
    DefaultUniInteger -> "integer"
    DefaultUniByteString -> "bytestring"
    DefaultUniString -> "string"
    DefaultUniUnit -> "unit"
    DefaultUniBool -> "bool"
    DefaultUniProtoList -> "list"
    DefaultUniProtoArray -> "array"
    DefaultUniProtoPair -> "pair"
    DefaultUniApply uniF uniA -> uniF `juxtPrettyM` uniA
    DefaultUniData -> "data"
    DefaultUniBLS12_381_G1_Element -> "bls12_381_G1_element"
    DefaultUniBLS12_381_G2_Element -> "bls12_381_G2_element"
    DefaultUniBLS12_381_MlResult -> "bls12_381_mlresult"
    DefaultUniValue -> "value"

instance PrettyBy RenderContext (SomeTypeIn DefaultUni) where
  prettyBy config (SomeTypeIn uni) = prettyBy config uni

{-| This always pretty-prints parens around type applications (e.g. @(list bool)@) and
doesn't pretty-print them otherwise (e.g. @integer@). -}
instance Pretty (DefaultUni a) where
  pretty = prettyBy juxtRenderContext

instance Pretty (SomeTypeIn DefaultUni) where
  pretty (SomeTypeIn uni) = pretty uni

-- | Elaborate a built-in type (see 'ElaborateBuiltin') from 'DefaultUni'.
type ElaborateBuiltinDefaultUni :: forall a. a -> a
type family ElaborateBuiltinDefaultUni x where
  ElaborateBuiltinDefaultUni (f x) = ElaborateBuiltinDefaultUni f `TyAppRep` x
  ElaborateBuiltinDefaultUni x = BuiltinHead x

type instance ElaborateBuiltin DefaultUni x = ElaborateBuiltinDefaultUni x

instance (DefaultUni `Contains` f, DefaultUni `Contains` a) => DefaultUni `Contains` f a where
  knownUni = knownUni `DefaultUniApply` knownUni

instance DefaultUni `Contains` Integer where
  knownUni = DefaultUniInteger
instance DefaultUni `Contains` ByteString where
  knownUni = DefaultUniByteString
instance DefaultUni `Contains` Text where
  knownUni = DefaultUniString
instance DefaultUni `Contains` () where
  knownUni = DefaultUniUnit
instance DefaultUni `Contains` Bool where
  knownUni = DefaultUniBool
instance DefaultUni `Contains` Value where
  knownUni = DefaultUniValue
instance DefaultUni `Contains` [] where
  knownUni = DefaultUniProtoList
instance DefaultUni `Contains` Strict.Vector where
  knownUni = DefaultUniProtoArray
instance DefaultUni `Contains` (,) where
  knownUni = DefaultUniProtoPair
instance DefaultUni `Contains` Data where
  knownUni = DefaultUniData
instance DefaultUni `Contains` BLS12_381.G1.Element where
  knownUni = DefaultUniBLS12_381_G1_Element
instance DefaultUni `Contains` BLS12_381.G2.Element where
  knownUni = DefaultUniBLS12_381_G2_Element
instance DefaultUni `Contains` BLS12_381.Pairing.MlResult where
  knownUni = DefaultUniBLS12_381_MlResult

instance
  KnownBuiltinTypeAst tyname DefaultUni Integer
  => KnownTypeAst tyname DefaultUni Integer
instance
  KnownBuiltinTypeAst tyname DefaultUni ByteString
  => KnownTypeAst tyname DefaultUni ByteString
instance
  KnownBuiltinTypeAst tyname DefaultUni Text
  => KnownTypeAst tyname DefaultUni Text
instance
  KnownBuiltinTypeAst tyname DefaultUni ()
  => KnownTypeAst tyname DefaultUni ()
instance
  KnownBuiltinTypeAst tyname DefaultUni Bool
  => KnownTypeAst tyname DefaultUni Bool
instance
  KnownBuiltinTypeAst tyname DefaultUni [a]
  => KnownTypeAst tyname DefaultUni [a]
instance
  KnownBuiltinTypeAst tyname DefaultUni (Strict.Vector a)
  => KnownTypeAst tyname DefaultUni (Strict.Vector a)
instance
  KnownBuiltinTypeAst tyname DefaultUni (a, b)
  => KnownTypeAst tyname DefaultUni (a, b)
instance
  KnownBuiltinTypeAst tyname DefaultUni Data
  => KnownTypeAst tyname DefaultUni Data
instance
  KnownBuiltinTypeAst tyname DefaultUni BLS12_381.G1.Element
  => KnownTypeAst tyname DefaultUni BLS12_381.G1.Element
instance
  KnownBuiltinTypeAst tyname DefaultUni BLS12_381.G2.Element
  => KnownTypeAst tyname DefaultUni BLS12_381.G2.Element
instance
  KnownBuiltinTypeAst tyname DefaultUni BLS12_381.Pairing.MlResult
  => KnownTypeAst tyname DefaultUni BLS12_381.Pairing.MlResult
instance
  KnownBuiltinTypeAst tyname DefaultUni Value
  => KnownTypeAst tyname DefaultUni Value

instance
  KnownBuiltinTypeIn DefaultUni term Integer
  => ReadKnownIn DefaultUni term Integer
instance
  KnownBuiltinTypeIn DefaultUni term ByteString
  => ReadKnownIn DefaultUni term ByteString
instance
  KnownBuiltinTypeIn DefaultUni term Text
  => ReadKnownIn DefaultUni term Text
instance
  KnownBuiltinTypeIn DefaultUni term ()
  => ReadKnownIn DefaultUni term ()
instance
  KnownBuiltinTypeIn DefaultUni term Bool
  => ReadKnownIn DefaultUni term Bool
instance
  KnownBuiltinTypeIn DefaultUni term Data
  => ReadKnownIn DefaultUni term Data
instance
  KnownBuiltinTypeIn DefaultUni term [a]
  => ReadKnownIn DefaultUni term [a]
instance
  KnownBuiltinTypeIn DefaultUni term (Strict.Vector a)
  => ReadKnownIn DefaultUni term (Strict.Vector a)
instance
  KnownBuiltinTypeIn DefaultUni term (a, b)
  => ReadKnownIn DefaultUni term (a, b)
instance
  KnownBuiltinTypeIn DefaultUni term BLS12_381.G1.Element
  => ReadKnownIn DefaultUni term BLS12_381.G1.Element
instance
  KnownBuiltinTypeIn DefaultUni term BLS12_381.G2.Element
  => ReadKnownIn DefaultUni term BLS12_381.G2.Element
instance
  KnownBuiltinTypeIn DefaultUni term BLS12_381.Pairing.MlResult
  => ReadKnownIn DefaultUni term BLS12_381.Pairing.MlResult
instance
  KnownBuiltinTypeIn DefaultUni term Value
  => ReadKnownIn DefaultUni term Value

instance
  KnownBuiltinTypeIn DefaultUni term Integer
  => MakeKnownIn DefaultUni term Integer
instance
  KnownBuiltinTypeIn DefaultUni term ByteString
  => MakeKnownIn DefaultUni term ByteString
instance
  KnownBuiltinTypeIn DefaultUni term Text
  => MakeKnownIn DefaultUni term Text
instance
  KnownBuiltinTypeIn DefaultUni term ()
  => MakeKnownIn DefaultUni term ()
instance
  KnownBuiltinTypeIn DefaultUni term Bool
  => MakeKnownIn DefaultUni term Bool
instance
  KnownBuiltinTypeIn DefaultUni term Data
  => MakeKnownIn DefaultUni term Data
instance
  KnownBuiltinTypeIn DefaultUni term [a]
  => MakeKnownIn DefaultUni term [a]
instance
  KnownBuiltinTypeIn DefaultUni term (Strict.Vector a)
  => MakeKnownIn DefaultUni term (Strict.Vector a)
instance
  KnownBuiltinTypeIn DefaultUni term (a, b)
  => MakeKnownIn DefaultUni term (a, b)
instance
  KnownBuiltinTypeIn DefaultUni term BLS12_381.G1.Element
  => MakeKnownIn DefaultUni term BLS12_381.G1.Element
instance
  KnownBuiltinTypeIn DefaultUni term BLS12_381.G2.Element
  => MakeKnownIn DefaultUni term BLS12_381.G2.Element
instance
  KnownBuiltinTypeIn DefaultUni term BLS12_381.Pairing.MlResult
  => MakeKnownIn DefaultUni term BLS12_381.Pairing.MlResult
instance
  KnownBuiltinTypeIn DefaultUni term Value
  => MakeKnownIn DefaultUni term Value

-- If this tells you an instance is missing, add it right above, following the pattern.
instance TestTypesFromTheUniverseAreAllKnown DefaultUni

{- Note [Integral types as Integer]
Technically our universe only contains 'Integer', but many of the builtin functions that we would
like to use work over 'Int', 'Word8' etc.

This is inconvenient and also error-prone: dealing with a function that takes an 'Int' or 'Word8'
means carefully downcasting the 'Integer', running the function, potentially upcasting at the end.
And it's easy to get wrong by e.g. blindly using 'fromInteger' or 'fromIntegral'.

Moreover, there is a latent risk here: if we *were* to build on a 32-bit architecture, then programs
which use arguments between @maxBound :: Int32@ and @maxBound :: Int64@ would behave differently!

So, what to do? We adopt the following strategy:
- We allow lifting/unlifting bounded integral types such as 'Word8' or 'Int64' via 'Integer',
  including a safe upcast in 'makeKnown' (which we could have on any architecture, but we only add
  it for 64-bit for uniformity) and a safe checked downcast in 'readKnown'.
- We allow lifting/unlifting 'Int' via 'Int64' and 'Word' via 'Word64', constraining the conversion
  between them to 64-bit architectures where this conversion is safe.

Doing this effectively bans builds on all non-64-bit systems, which is acceptable since 64-bit
systems are required for node deployment, and this way any attempts to build on them will fail fast.

We used to use newtype- and via-deriving for implementations of relevant instances, but at some
point GHC stopped attaching @INLINE@ annotations to those causing the GHC Core for builtins to have
multiple 'readKnown' and 'makeKnown' calls, so now we don't rely on deriving and implement instances
manually.
-}

-- | 'coerce' the argument, then call 'makeKnown'.
makeKnownCoerce
  :: forall b term a
   . (MakeKnownIn DefaultUni term b, Coercible a b)
  => a -> BuiltinResult term
makeKnownCoerce = coerceArg $ makeKnown @_ @_ @b
{-# INLINE makeKnownCoerce #-}

-- | Call 'readKnown', then 'coerce' the argument.
readKnownCoerce
  :: forall b term a
   . (ReadKnownIn DefaultUni term b, Coercible b a)
  => term -> ReadKnownM a
readKnownCoerce = fmap coerce #. readKnown @_ @_ @b
{-# INLINE readKnownCoerce #-}

{-| For deriving 'KnownTypeAst' instances via 'Integer' (no constructor, because we don't need any
for 'KnownTypeAst'). -}
data AsInteger a

instance KnownTypeAst tyname DefaultUni (AsInteger a) where
  type IsBuiltin _ _ = 'False
  type ToHoles _ _ _ = '[]
  type ToBinds _ acc _ = acc
  typeAst = toTypeAst $ Proxy @Integer

makeKnownAsInteger
  :: forall term a
   . (KnownBuiltinTypeIn DefaultUni term Integer, Integral a)
  => a -> BuiltinResult term
makeKnownAsInteger = makeKnown . toInteger
{-# INLINE makeKnownAsInteger #-}

readKnownAsInteger
  :: forall term a
   . (KnownBuiltinTypeIn DefaultUni term Integer, Integral a, Bounded a, Typeable a)
  => term -> ReadKnownM a
readKnownAsInteger term =
  -- See Note [Performance of ReadKnownIn and MakeKnownIn instances].
  -- Funnily, we don't need 'inline' here, unlike in the default implementation of 'readKnown'
  -- (go figure why).
  inline readKnownConstant term >>= oneShot \(i :: Integer) ->
    -- We don't make use here of 'toIntegralSized' because of performance considerations,
    -- see: https://gitlab.haskell.org/ghc/ghc/-/issues/19641
    -- TODO: benchmark an alternative 'integerToIntMaybe', modified from @ghc-bignum@
    if fromIntegral (minBound :: a) <= i && i <= fromIntegral (maxBound :: a)
      then pure $ fromIntegral i
      else
        throwError . operationalUnliftingError $
          fold
            [ Text.pack $ show i
            , " is not within the bounds of "
            , Text.pack . show . typeRep $ Proxy @a
            ]
{-# INLINE readKnownAsInteger #-}

#if WORD_SIZE_IN_BITS == 64
-- See Note [Integral types as Integer].
deriving via AsInteger Int instance
        KnownTypeAst tyname DefaultUni Int
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Int where
    makeKnown = makeKnownAsInteger
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Int where
    readKnown term = fromIntegral @Int64 @Int <$> readKnown term
    {-# INLINE readKnown #-}

deriving via AsInteger Word instance
        KnownTypeAst tyname DefaultUni Word
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Word where
    makeKnown = makeKnownAsInteger
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Word where
    readKnown term = fromIntegral @Word64 @Word <$> readKnown term
    {-# INLINE readKnown #-}
#else
-- On non-64-bit platforms (e.g. wasm32), UPLC evaluation is unsupported, but
-- we still need these instances so that the builtin machinery compiles.
deriving via AsInteger Int instance
        KnownTypeAst tyname DefaultUni Int
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Int where
    makeKnown = error "UPLC evaluation is not supported on non-64-bit platforms"
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Int where
    readKnown = error "UPLC evaluation is not supported on non-64-bit platforms"
    {-# INLINE readKnown #-}

deriving via AsInteger Word instance
        KnownTypeAst tyname DefaultUni Word
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Word where
    makeKnown = error "UPLC evaluation is not supported on non-64-bit platforms"
    {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Word where
    readKnown = error "UPLC evaluation is not supported on non-64-bit platforms"
    {-# INLINE readKnown #-}
#endif

deriving via
  AsInteger Int8
  instance
    KnownTypeAst tyname DefaultUni Int8
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Int8 where
  makeKnown = makeKnownAsInteger
  {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Int8 where
  readKnown = readKnownAsInteger
  {-# INLINE readKnown #-}

deriving via
  AsInteger Int16
  instance
    KnownTypeAst tyname DefaultUni Int16
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Int16 where
  makeKnown = makeKnownAsInteger
  {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Int16 where
  readKnown = readKnownAsInteger
  {-# INLINE readKnown #-}

deriving via
  AsInteger Int32
  instance
    KnownTypeAst tyname DefaultUni Int32
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Int32 where
  makeKnown = makeKnownAsInteger
  {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Int32 where
  readKnown = readKnownAsInteger
  {-# INLINE readKnown #-}

deriving via
  AsInteger Int64
  instance
    KnownTypeAst tyname DefaultUni Int64
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Int64 where
  makeKnown = makeKnownAsInteger
  {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Int64 where
  readKnown = readKnownAsInteger
  {-# INLINE readKnown #-}

deriving via
  AsInteger Word8
  instance
    KnownTypeAst tyname DefaultUni Word8
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Word8 where
  makeKnown = makeKnownAsInteger
  {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Word8 where
  readKnown = readKnownAsInteger
  {-# INLINE readKnown #-}

deriving via
  AsInteger Word16
  instance
    KnownTypeAst tyname DefaultUni Word16
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Word16 where
  makeKnown = makeKnownAsInteger
  {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Word16 where
  readKnown = readKnownAsInteger
  {-# INLINE readKnown #-}

deriving via
  AsInteger Word32
  instance
    KnownTypeAst tyname DefaultUni Word32
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Word32 where
  makeKnown = makeKnownAsInteger
  {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Word32 where
  readKnown = readKnownAsInteger
  {-# INLINE readKnown #-}

deriving via
  AsInteger Word64
  instance
    KnownTypeAst tyname DefaultUni Word64
instance KnownBuiltinTypeIn DefaultUni term Integer => MakeKnownIn DefaultUni term Word64 where
  makeKnown = makeKnownAsInteger
  {-# INLINE makeKnown #-}
instance KnownBuiltinTypeIn DefaultUni term Integer => ReadKnownIn DefaultUni term Word64 where
  readKnown = readKnownAsInteger
  {-# INLINE readKnown #-}

deriving newtype instance
  KnownTypeAst tyname DefaultUni NumBytesCostedAsNumWords
instance
  KnownBuiltinTypeIn DefaultUni term Integer
  => MakeKnownIn DefaultUni term NumBytesCostedAsNumWords
  where
  makeKnown = makeKnownCoerce @Integer
  {-# INLINE makeKnown #-}

instance
  KnownBuiltinTypeIn DefaultUni term Integer
  => ReadKnownIn DefaultUni term NumBytesCostedAsNumWords
  where
  readKnown = readKnownCoerce @Integer
  {-# INLINE readKnown #-}

deriving newtype instance
  KnownTypeAst tyname DefaultUni IntegerCostedLiterally
instance
  KnownBuiltinTypeIn DefaultUni term Integer
  => MakeKnownIn DefaultUni term IntegerCostedLiterally
  where
  makeKnown = makeKnownCoerce @Integer
  {-# INLINE makeKnown #-}
instance
  KnownBuiltinTypeIn DefaultUni term Integer
  => ReadKnownIn DefaultUni term IntegerCostedLiterally
  where
  readKnown = readKnownCoerce @Integer
  {-# INLINE readKnown #-}

deriving newtype instance
  KnownTypeAst tyname DefaultUni TextCostedByByteLength
instance
  KnownBuiltinTypeIn DefaultUni term Text
  => MakeKnownIn DefaultUni term TextCostedByByteLength
  where
  makeKnown = makeKnownCoerce @Text
  {-# INLINE makeKnown #-}
instance
  KnownBuiltinTypeIn DefaultUni term Text
  => ReadKnownIn DefaultUni term TextCostedByByteLength
  where
  readKnown = readKnownCoerce @Text
  {-# INLINE readKnown #-}

deriving newtype instance
  KnownTypeAst tyname DefaultUni ValueTotalSize
instance
  KnownBuiltinTypeIn DefaultUni term Value
  => MakeKnownIn DefaultUni term ValueTotalSize
  where
  makeKnown = makeKnownCoerce @Value
  {-# INLINE makeKnown #-}
instance
  KnownBuiltinTypeIn DefaultUni term Value
  => ReadKnownIn DefaultUni term ValueTotalSize
  where
  readKnown = readKnownCoerce @Value
  {-# INLINE readKnown #-}

deriving newtype instance
  KnownTypeAst tyname DefaultUni ValueMaxDepth
instance
  KnownBuiltinTypeIn DefaultUni term Value
  => MakeKnownIn DefaultUni term ValueMaxDepth
  where
  makeKnown = makeKnownCoerce @Value
  {-# INLINE makeKnown #-}
instance
  KnownBuiltinTypeIn DefaultUni term Value
  => ReadKnownIn DefaultUni term ValueMaxDepth
  where
  readKnown = readKnownCoerce @Value
  {-# INLINE readKnown #-}

deriving newtype instance
  KnownTypeAst tyname DefaultUni DataNodeCount
instance
  KnownBuiltinTypeIn DefaultUni term Value
  => MakeKnownIn DefaultUni term DataNodeCount
  where
  makeKnown = makeKnownCoerce @Data
  {-# INLINE makeKnown #-}
instance
  KnownBuiltinTypeIn DefaultUni term Value
  => ReadKnownIn DefaultUni term DataNodeCount
  where
  readKnown = readKnownCoerce @Data
  {-# INLINE readKnown #-}

deriving via
  AsInteger Natural
  instance
    KnownTypeAst tyname DefaultUni Natural
instance
  KnownBuiltinTypeIn DefaultUni term Integer
  => MakeKnownIn DefaultUni term Natural
  where
  makeKnown = makeKnownAsInteger
  {-# INLINE makeKnown #-}
instance
  KnownBuiltinTypeIn DefaultUni term Integer
  => ReadKnownIn DefaultUni term Natural
  where
  readKnown term =
    -- See Note [Performance of ReadKnownIn and MakeKnownIn instances].
    -- Funnily, we don't really need 'inline' here, unlike in the default implementation of
    -- 'readKnown' (go figure why), but we still use it just to be sure.
    inline readKnownConstant term >>= oneShot \(i :: Integer) ->
      -- TODO: benchmark alternatives:signumInteger,integerIsNegative,integerToNaturalThrow
      if i >= 0
        -- TODO: benchmark alternatives: ghc>=9 integerToNatural
        then pure $ fromInteger i
        else
          throwError . operationalUnliftingError $
            fold
              [ Text.pack $ show i
              , " is not within the bounds of Natural"
              ]
  {-# INLINE readKnown #-}

deriving newtype instance
  KnownTypeAst tyname DefaultUni CInteger

instance
  KnownBuiltinTypeIn DefaultUni term Integer
  => MakeKnownIn DefaultUni term CInteger
  where
  makeKnown (CInteger i)
    | i > maxBoundInteger || i < minBoundInteger =
        BuiltinFailure
          (pure "Integer out of bounds")
          BuiltinEvaluationFailure
    | otherwise = makeKnown i
  {-# INLINE makeKnown #-}

instance
  KnownBuiltinTypeIn DefaultUni term Integer
  => ReadKnownIn DefaultUni term CInteger
  where
  readKnown term =
    inline readKnownConstant term >>= oneShot \(i :: Integer) ->
      if i > maxBoundInteger || i < minBoundInteger
        then
          throwError . operationalUnliftingError $
            "Integer out of bounds"
        else pure $ CInteger i
  {-# INLINE readKnown #-}

deriving newtype instance
  KnownTypeAst tyname DefaultUni CByteString
instance
  KnownBuiltinTypeIn DefaultUni term ByteString
  => MakeKnownIn DefaultUni term CByteString
  where
  makeKnown (CByteString s)
    | B.length s > maxBoundByteString =
        BuiltinFailure
          (pure "Bytestring overflow")
          BuiltinEvaluationFailure
    | otherwise = makeKnown s
  {-# INLINE makeKnown #-}
instance
  KnownBuiltinTypeIn DefaultUni term ByteString
  => ReadKnownIn DefaultUni term CByteString
  where
  readKnown term =
    inline readKnownConstant term >>= oneShot \(s :: ByteString) ->
      if B.length s > maxBoundByteString
        then
          throwError . operationalUnliftingError $
            "ByteString overflow"
        else pure $ CByteString s
  {-# INLINE readKnown #-}

outOfBoundsErr :: Pretty a => a -> Vector.Vector term -> Text
outOfBoundsErr x branches =
  fold
    [ "'case "
    , display x
    , "' is out of bounds for the given number of branches: "
    , display $ Vector.length branches
    ]

byteStringPatternWords :: ByteString -> Int
byteStringPatternWords bs =
  let (wholeWords, trailingBytes) = B.length bs `quotRem` 8
   in max 1 $ wholeWords + if trailingBytes == 0 then 0 else 1
{-# INLINE byteStringPatternWords #-}

instance AnnotateCaseBuiltin DefaultUni where
  annotateCaseBuiltin ty branches = case ty of
    TyBuiltin _ (SomeTypeIn DefaultUniUnit) ->
      case branches of
        [x] -> Right [(x, [])]
        _ -> Left "Casing on unit only allows exactly one branch"
    TyBuiltin _ (SomeTypeIn DefaultUniBool) ->
      case branches of
        [f] -> Right [(f, [])]
        [f, t] -> Right [(f, []), (t, [])]
        _ -> Left "Casing on bool requires exactly one branch or two branches"
    TyBuiltin _ (SomeTypeIn DefaultUniInteger) ->
      Right $ map (,[]) branches
    listTy@(TyApp _ (TyBuiltin _ (SomeTypeIn DefaultUniProtoList)) argTy) ->
      case branches of
        [cons] -> Right [(cons, [argTy, listTy])]
        [cons, nil] -> Right [(cons, [argTy, listTy]), (nil, [])]
        _ -> Left "Casing on list requires exactly one branch or two branches"
    (TyApp _ (TyApp _ (TyBuiltin _ (SomeTypeIn DefaultUniProtoPair)) lTyArg) rTyArg) ->
      case branches of
        [f] -> Right [(f, [lTyArg, rTyArg])]
        _ -> Left "Casing on pair requires exactly one branch"
    _ -> Left $ display (void ty) <> " isn't supported in 'case'"

instance CaseBuiltin DefaultUni where
  caseBuiltin someVal@(Some (ValueOf uni x)) branches = case uni of
    DefaultUniUnit
      | 1 == len -> HeadOnly $ branches Vector.! 0
      | otherwise -> HeadError $ outOfBoundsErr someVal branches
    DefaultUniBool -> case x of
      -- We allow there to be only one branch as long as the scrutinee is 'False'.
      -- This is strictly to save size by not having the 'True' branch if it was gonna be
      -- 'Error' anyway.
      False | len == 1 || len == 2 -> HeadOnly $ branches Vector.! 0
      True | len == 2 -> HeadOnly $ branches Vector.! 1
      _ -> HeadError $ outOfBoundsErr someVal branches
    DefaultUniInteger
      | 0 <= x && x < toInteger len -> HeadOnly $ branches Vector.! fromInteger x
      | otherwise -> HeadError $ outOfBoundsErr someVal branches
    DefaultUniList ty
      | len == 1 ->
          case x of
            [] -> HeadError "Expected non-empty list, got empty list for casing list"
            (y : ys) -> headSpine (branches Vector.! 0) [someValueOf ty y, someValueOf uni ys]
      | len == 2 ->
          case x of
            [] -> HeadOnly $ branches Vector.! 1
            (y : ys) -> headSpine (branches Vector.! 0) [someValueOf ty y, someValueOf uni ys]
      | otherwise -> HeadError $ outOfBoundsErr someVal branches
    DefaultUniPair tyL tyR
      | len == 1 ->
          case x of
            (l, r) -> headSpine (branches Vector.! 0) [someValueOf tyL l, someValueOf tyR r]
      | otherwise -> HeadError $ outOfBoundsErr someVal branches
    _ -> HeadError $ display uni <> " isn't supported in 'case'"
    where
      !len = Vector.length branches
  {-# INLINE caseBuiltin #-}

{-| Pending success work for one depth-first alternative. Every constructor stores the same
fallback cursor, and the terminal constructor additionally stores the successful handler. This is
an explicit work stack, not a chain of functional continuations: a mismatch abandons it in constant
time, while success resumes one frame at a time. Deferred field contents and traversal beyond the
paid exact-arity probe stay lazy until the next structural spend. The cursor is deliberately the
first field of both pending-work constructors, keeping its hot projection at a uniform payload
position. -}
data DefaultPatternWorkStack term where
  DefaultPatternWorkDone
    :: term
    -> {-# UNPACK #-} !(Vector.Vector (DefaultBuiltinPattern, term))
    -> DefaultPatternWorkStack term
  DefaultPatternValueWork
    :: !(Vector.Vector (DefaultBuiltinPattern, term))
    -> !DefaultBuiltinPattern
    -> Some (ValueOf DefaultUni)
    -> !(DefaultPatternWorkStack term)
    -> DefaultPatternWorkStack term
  DefaultPatternFieldsWork
    :: !(Vector.Vector (DefaultBuiltinPattern, term))
    -> !(Vector.Vector DefaultBuiltinPattern)
    -> !(DefaultUni (Esc a))
    -> [a]
    -> !(DefaultPatternWorkStack term)
    -> DefaultPatternWorkStack term

{-| Return the fallback cursor stored on the immediate continuation. Every frame belonging to an
alternative stores the same cursor, so a mismatch never has to walk the work stack. -}
defaultPatternWorkAlternatives
  :: DefaultPatternWorkStack term
  -> Vector.Vector (DefaultBuiltinPattern, term)
defaultPatternWorkAlternatives (DefaultPatternWorkDone _ alternatives) = alternatives
defaultPatternWorkAlternatives (DefaultPatternValueWork alternatives _ _ _) = alternatives
defaultPatternWorkAlternatives (DefaultPatternFieldsWork alternatives _ _ _ _) = alternatives
{-# INLINE defaultPatternWorkAlternatives #-}

{-| Reached captures in reverse encounter order. Each strict cons is charged before construction.
On success, the strict tail-recursive materializer consumes the list directly into a 'Spine' in
handler-application order. -}
type DefaultReverseCaptures = [Some (ValueOf DefaultUni)]

spendDefaultPatternWork
  :: Word64
  -> PatternMatchM s ()
spendDefaultPatternWork work = spendPatternWork (PatternWork work)
{-# INLINE spendDefaultPatternWork #-}

spendDefaultStructuralWork
  :: PatternMatchM s ()
spendDefaultStructuralWork = spendPatternWork PatternStructuralWork
{-# INLINE spendDefaultStructuralWork #-}

spendDefaultFailureWork
  :: PatternMatchM s ()
spendDefaultFailureWork = spendPatternWork PatternFailureWork
{-# INLINE spendDefaultFailureWork #-}

{-| Select the first matching alternative. The alternative loop lives beside the universe-specific
matcher so the CEK invokes matching once, just as it invokes builtin casing once.

Each alternative probe is charged before deconstructing the vector cursor or forcing the selected
pattern/handler pair. Pattern traversal then charges its own work directly as it proceeds. -}
matchDefaultAlternatives
  :: forall s term
   . Some (ValueOf DefaultUni)
  -> Vector.Vector (DefaultBuiltinPattern, term)
  -> PatternMatchM s (HeadSpine Text term (Some (ValueOf DefaultUni)))
matchDefaultAlternatives rootValue alternatives =
  PatternMatchM $ \spend -> runPatternMatchM (attemptSpend >> goPaidAlternative alternatives) spend
  where
    -- Reusing these actions reruns their spending effects; it does not prepay work.
    attemptSpend = spendDefaultPatternWork 1
    structuralSpend = spendDefaultStructuralWork
    failureSpend = spendDefaultFailureWork

    goPaidAlternative
      :: Vector.Vector (DefaultBuiltinPattern, term)
      -> PatternMatchM s (HeadSpine Text term (Some (ValueOf DefaultUni)))
    goPaidAlternative remainingAlternatives = case Vector.uncons remainingAlternatives of
      Nothing -> pure $ HeadError "none of the match alternatives matched"
      Just ((pat, handler), laterAlternatives) ->
        -- The alternative-attempt or preceding failure charge covers dispatching this root
        -- node below. Recursive nodes and field steps charge themselves before inspection.
        matchPaidValue
          pat
          rootValue
          (DefaultPatternWorkDone handler laterAlternatives)
          []

    nextAlternative
      :: DefaultPatternWorkStack term
      -> PatternMatchM s (HeadSpine Text term (Some (ValueOf DefaultUni)))
    nextAlternative workStack = do
      -- The pattern work that discovered the mismatch was covered by its root, nested-node, or
      -- field charge. This separate charge covers abandoning that result and probing/dispatching
      -- the next alternative.
      failureSpend
      goPaidAlternative $ defaultPatternWorkAlternatives workStack

    finish
      :: term
      -> DefaultReverseCaptures
      -> PatternMatchM s (HeadSpine Text term (Some (ValueOf DefaultUni)))
    finish handler [] = pure $ HeadOnly handler
    finish handler (finalCapture : previousCaptures) =
      let materialize
            :: Spine (Some (ValueOf DefaultUni))
            -> DefaultReverseCaptures
            -> Spine (Some (ValueOf DefaultUni))
          materialize !acc [] = acc
          materialize !acc (capture : previous) =
            materialize (SpineCons capture acc) previous
          !captureSpine = materialize (SpineLast finalCapture) previousCaptures
       in pure $ HeadSpine handler captureSpine

    resumeWork
      :: DefaultPatternWorkStack term
      -> DefaultReverseCaptures
      -> PatternMatchM s (HeadSpine Text term (Some (ValueOf DefaultUni)))
    resumeWork workStack captures = case workStack of
      DefaultPatternWorkDone handler _ -> finish handler captures
      DefaultPatternValueWork _ next nextValue rest -> do
        -- Charge before forcing the deferred package. In particular, a pair's right-hand
        -- payload stays lazy until its own structural step has been paid for.
        structuralSpend
        matchPaidValue
          next
          nextValue
          rest
          captures
      DefaultPatternFieldsWork _ patterns elemUni fields rest ->
        matchFields
          patterns
          elemUni
          fields
          rest
          captures

    matchValue
      :: DefaultBuiltinPattern
      -> Some (ValueOf DefaultUni)
      -> DefaultPatternWorkStack term
      -> DefaultReverseCaptures
      -> PatternMatchM s (HeadSpine Text term (Some (ValueOf DefaultUni)))
    matchValue
      patternToMatch
      currentValue
      rest
      captures = do
        structuralSpend
        matchPaidValue
          patternToMatch
          currentValue
          rest
          captures

    matchPaidValue
      :: DefaultBuiltinPattern
      -> Some (ValueOf DefaultUni)
      -> DefaultPatternWorkStack term
      -> DefaultReverseCaptures
      -> PatternMatchM s (HeadSpine Text term (Some (ValueOf DefaultUni)))
    matchPaidValue
      patternToMatch
      currentValueOf@(Some (ValueOf currentUni currentValue))
      rest
      captures =
        case patternToMatch of
          DefaultPatternWildcard ->
            resumeWork rest captures
          DefaultPatternCapture -> do
            -- One unit pays for the later strict Spine cell, and one for its implicit handler
            -- application. The charge remains spent if later work abandons this alternative.
            spendDefaultPatternWork 2
            let !captures' = currentValueOf : captures
            resumeWork rest captures'
          DefaultPatternInteger expected -> case currentUni of
            DefaultUniInteger
              | currentValue == toInteger expected ->
                  resumeWork rest captures
            _ -> nextAlternative rest
          DefaultPatternByteString expected -> case currentUni of
            DefaultUniByteString
              | B.length currentValue /= B.length expected ->
                  nextAlternative rest
              | otherwise ->
                  -- Length is strict bytestring metadata. Pay for the entire native comparison
                  -- before equality is allowed to inspect the payload.
                  spendDefaultPatternWork
                    (fromIntegral $ byteStringPatternWords expected)
                    >>= \() ->
                      if currentValue == expected
                        then resumeWork rest captures
                        else nextAlternative rest
            _ -> nextAlternative rest
          DefaultPatternBool expected -> case currentUni of
            DefaultUniBool
              | currentValue == expected ->
                  resumeWork rest captures
            _ -> nextAlternative rest
          DefaultPatternUnit -> case currentUni of
            DefaultUniUnit -> resumeWork rest captures
            _ -> nextAlternative rest
          DefaultPatternList children -> case currentUni of
            DefaultUniList elemUni ->
              matchFields
                children
                elemUni
                currentValue
                rest
                captures
            _ -> nextAlternative rest
          DefaultPatternPair leftPattern rightPattern -> case currentUni of
            DefaultUniPair leftUni rightUni -> case currentValue of
              (left, right) ->
                matchValue
                  leftPattern
                  (someValueOf leftUni left)
                  ( DefaultPatternValueWork
                      (defaultPatternWorkAlternatives rest)
                      rightPattern
                      (someValueOf rightUni right)
                      rest
                  )
                  captures
            _ -> nextAlternative rest
          DefaultPatternDataConstr expectedTag children -> case currentUni of
            DefaultUniData -> case currentValue of
              PLC.Constr actualTag fields
                | actualTag == toInteger expectedTag ->
                    matchFields
                      children
                      DefaultUniData
                      fields
                      rest
                      captures
              _ -> nextAlternative rest
            _ -> nextAlternative rest
          DefaultPatternDataMap children -> case currentUni of
            DefaultUniData -> case currentValue of
              PLC.Map fields ->
                matchFields
                  children
                  (DefaultUniPair DefaultUniData DefaultUniData)
                  fields
                  rest
                  captures
              _ -> nextAlternative rest
            _ -> nextAlternative rest
          DefaultPatternDataList children -> case currentUni of
            DefaultUniData -> case currentValue of
              PLC.List fields ->
                matchFields
                  children
                  DefaultUniData
                  fields
                  rest
                  captures
              _ -> nextAlternative rest
            _ -> nextAlternative rest
          DefaultPatternDataI child -> case currentUni of
            DefaultUniData -> case (child, currentValue) of
              (Nothing, PLC.I _) -> resumeWork rest captures
              (Just nested, PLC.I integer) ->
                matchValue
                  nested
                  (someValueOf DefaultUniInteger integer)
                  rest
                  captures
              _ -> nextAlternative rest
            _ -> nextAlternative rest
          DefaultPatternDataB child -> case currentUni of
            DefaultUniData -> case (child, currentValue) of
              (Nothing, PLC.B _) -> resumeWork rest captures
              (Just nested, PLC.B bytes) ->
                matchValue
                  nested
                  (someValueOf DefaultUniByteString bytes)
                  rest
                  captures
              _ -> nextAlternative rest
            _ -> nextAlternative rest

    matchFields
      :: forall a
       . Vector.Vector DefaultBuiltinPattern
      -> DefaultUni (Esc a)
      -> [a]
      -> DefaultPatternWorkStack term
      -> DefaultReverseCaptures
      -> PatternMatchM s (HeadSpine Text term (Some (ValueOf DefaultUni)))
    -- This is the general field loop for every container shape. For non-empty patterns, the
    -- field list remains lazy until the structural spend succeeds. The empty-pattern arity
    -- probe is covered by the already-paid parent dispatch.
    matchFields
      patterns
      elemUni
      currentFields
      rest
      currentCaptures =
        if Vector.null patterns
          then case currentFields of
            [] -> resumeWork rest currentCaptures
            _ -> nextAlternative rest
          else do
            structuralSpend
            case (Vector.uncons patterns, currentFields) of
              (Nothing, _) -> nextAlternative rest
              (_, []) -> nextAlternative rest
              (Just (currentPattern, remainingPatterns), field : remainingFields)
                | Vector.null remainingPatterns -> case remainingFields of
                    [] ->
                      -- The field-edge spend covers this final child dispatch. Entering the paid
                      -- matcher directly avoids dispatching nested final children twice.
                      matchPaidValue
                        currentPattern
                        (someValueOf elemUni field)
                        rest
                        currentCaptures
                    _ -> nextAlternative rest
                | otherwise -> case remainingFields of
                    [] -> nextAlternative rest
                    _ -> case currentPattern of
                      DefaultPatternWildcard ->
                        matchFields
                          remainingPatterns
                          elemUni
                          remainingFields
                          rest
                          currentCaptures
                      DefaultPatternCapture -> do
                        spendDefaultPatternWork 2
                        let !capture = someValueOf elemUni field
                            !captures' = capture : currentCaptures
                        matchFields
                          remainingPatterns
                          elemUni
                          remainingFields
                          rest
                          captures'
                      nested ->
                        -- This field-edge spend includes dispatch of the child. A nested match
                        -- therefore enters the paid matcher directly; any later edge resumes this
                        -- general field loop through the explicit work stack.
                        matchPaidValue
                          nested
                          (someValueOf elemUni field)
                          ( DefaultPatternFieldsWork
                              (defaultPatternWorkAlternatives rest)
                              remainingPatterns
                              elemUni
                              remainingFields
                              rest
                          )
                          currentCaptures
{-# OPAQUE matchDefaultAlternatives #-}

instance MatchBuiltin DefaultUni DefaultBuiltinPattern where
  matchBuiltin
    :: Some (ValueOf DefaultUni)
    -> Vector.Vector (DefaultBuiltinPattern, term)
    -> PatternMatchM s (HeadSpine Text term (Some (ValueOf DefaultUni)))
  matchBuiltin = matchDefaultAlternatives
  {-# INLINE matchBuiltin #-}

{- Note [Stable encoding of tags]
'encodeUni' and 'decodeUni' are used for serialisation and deserialisation of types from the
universe and we need serialised things to be extremely stable, hence the definitions of 'encodeUni'
and 'decodeUni' must be amended only in a backwards compatible manner.

See Note [Stable encoding of TPLC]
-}

instance Closed DefaultUni where
  type
    DefaultUni `Everywhere` constr =
      ( constr `Permits` Integer
      , constr `Permits` ByteString
      , constr `Permits` Text
      , constr `Permits` ()
      , constr `Permits` Bool
      , constr `Permits` Value
      , constr `Permits` []
      , constr `Permits` Strict.Vector
      , constr `Permits` (,)
      , constr `Permits` Data
      , constr `Permits` BLS12_381.G1.Element
      , constr `Permits` BLS12_381.G2.Element
      , constr `Permits` BLS12_381.Pairing.MlResult
      )

  -- See Note [Stable encoding of tags].
  -- IF YOU'RE GETTING A WARNING HERE, DON'T FORGET TO AMEND 'withDecodedUni' RIGHT BELOW.
  encodeUni DefaultUniInteger = [0]
  encodeUni DefaultUniByteString = [1]
  encodeUni DefaultUniString = [2]
  encodeUni DefaultUniUnit = [3]
  encodeUni DefaultUniBool = [4]
  encodeUni DefaultUniProtoList = [5]
  encodeUni DefaultUniProtoPair = [6]
  encodeUni (DefaultUniApply uniF uniA) = 7 : encodeUni uniF ++ encodeUni uniA
  encodeUni DefaultUniData = [8]
  encodeUni DefaultUniBLS12_381_G1_Element = [9]
  encodeUni DefaultUniBLS12_381_G2_Element = [10]
  encodeUni DefaultUniBLS12_381_MlResult = [11]
  encodeUni DefaultUniProtoArray = [12]
  encodeUni DefaultUniValue = [13]

  -- See Note [Decoding universes].
  -- See Note [Stable encoding of tags].
  withDecodedUni k =
    peelUniTag >>= \case
      0 -> k DefaultUniInteger
      1 -> k DefaultUniByteString
      2 -> k DefaultUniString
      3 -> k DefaultUniUnit
      4 -> k DefaultUniBool
      5 -> k DefaultUniProtoList
      6 -> k DefaultUniProtoPair
      7 ->
        withDecodedUni @DefaultUni $ \uniF ->
          withDecodedUni @DefaultUni $ \uniA ->
            withApplicable uniF uniA $
              k $
                uniF `DefaultUniApply` uniA
      8 -> k DefaultUniData
      9 -> k DefaultUniBLS12_381_G1_Element
      10 -> k DefaultUniBLS12_381_G2_Element
      11 -> k DefaultUniBLS12_381_MlResult
      12 -> k DefaultUniProtoArray
      13 -> k DefaultUniValue
      _ -> empty

  bring
    :: forall constr a r proxy
     . DefaultUni `Everywhere` constr
    => proxy constr -> DefaultUni (Esc a) -> (constr a => r) -> r
  bring _ DefaultUniInteger r = r
  bring _ DefaultUniByteString r = r
  bring _ DefaultUniString r = r
  bring _ DefaultUniUnit r = r
  bring _ DefaultUniBool r = r
  bring p (DefaultUniProtoList `DefaultUniApply` uniA) r =
    bring p uniA r
  bring p (DefaultUniProtoArray `DefaultUniApply` uniA) r =
    bring p uniA r
  bring p (DefaultUniProtoPair `DefaultUniApply` uniA `DefaultUniApply` uniB) r =
    bring p uniA $ bring p uniB r
  bring _ (f `DefaultUniApply` _ `DefaultUniApply` _ `DefaultUniApply` _) _ =
    noMoreTypeFunctions f
  bring _ DefaultUniData r = r
  bring _ DefaultUniBLS12_381_G1_Element r = r
  bring _ DefaultUniBLS12_381_G2_Element r = r
  bring _ DefaultUniBLS12_381_MlResult r = r
  bring _ DefaultUniValue r = r
