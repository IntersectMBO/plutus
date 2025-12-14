{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module PlutusTx.Blueprint.Definition.Unroll where

import Prelude

import Data.Kind (Type)
import Data.Typeable (Typeable)
import Data.Void (Void)
import GHC.Generics (Generic (Rep), K1, M1, U1, type (:*:), type (:+:))
import GHC.TypeLits qualified as GHC
import PlutusTx.Blueprint.Definition.Id
  ( DefinitionId (..)
  , definitionIdFromType
  , definitionIdFromTypeK
  , definitionIdList
  , definitionIdTuple2
  , definitionIdTuple3
  , definitionIdUnit
  )
import PlutusTx.Blueprint.Definition.TF
  ( Concat
  , IfStuckRep
  , IfStuckUnroll
  , Insert
  , Nub
  , Reverse
  , type (++)
  )
import PlutusTx.Builtins.Internal
  ( BuiltinByteString
  , BuiltinData
  , BuiltinList
  , BuiltinPair
  , BuiltinString
  , BuiltinUnit
  )

----------------------------------------------------------------------------------------------------
-- Functionality to "unroll" types. -- For more context see Note ["Unrolling" types] -----------

{- Note ["Unrolling" types]

ContractBlueprint needs to be parameterized by a list of types used in
a contract's type signature (including nested types) in order to:
  a) produce a JSON-schema definition for every type used.
  b) ensure that the schema definitions are referenced in a type-safe way.

Given the following contract validator's type signature:

  typedValidator :: Redeemer -> Datum -> ScriptContext -> Bool

and the following data type definitions:

  data Redeemer = MkRedeemer MyStruct
  data MyStruct = MkMyStruct { field1 :: Integer, field2 :: Bool }
  type Datum = ()

The ContractBlueprint type should be:

  ContractBlueprint '[Redeemer, MyStruct, Integer, Bool, ()]

However, for contract blurprints authors specifying all the nested types manually is
cumbersome and error-prone. To make it easier to work with, we provide the Unroll type family
that can be used to traverse a type accumulating all types nested within it:

  Unroll Redeemer ~ '[Redeemer, MyStruct, Integer, Bool]
  UnrollAll '[Redeemer, Datum] ~ '[Redeemer, MyStruct, Integer, Bool, ()]

This way blueprint authors can specify the top-level types used in a contract and the UnrollAll
type family will take care of discovering all the nested types:

  Blueprint '[Redeemer, Datum]

  is equivalent to

  ContractBlueprint '[Redeemer, MyStruct, Integer, Bool, ()]

-}

{-| Designates a class of types that could be used as a Blueprint Definition.
     Each such type:
     - could be unrolled to a list of all nested types (including the type itself).
     - has a unique 'DefinitionId'. -}
class HasBlueprintDefinition (t :: Type) where
  type Unroll t :: [Type]
  type Unroll t = Insert t (GUnroll (IfStuckRep (RepIsStuckError t) (Rep t)))

  definitionId :: DefinitionId

  -- | Derive a 'DefinitionId' for a type.
  default definitionId :: Typeable t => DefinitionId
  definitionId = definitionIdFromType @t

instance HasBlueprintDefinition Void where
  type Unroll Void = '[Void]

instance HasBlueprintDefinition () where
  type Unroll () = '[()]
  definitionId = definitionIdUnit

instance HasBlueprintDefinition Bool where
  type Unroll Bool = '[Bool]

instance HasBlueprintDefinition Int where
  type Unroll Int = '[Int]

instance HasBlueprintDefinition Integer where
  type Unroll Integer = '[Integer]

instance HasBlueprintDefinition BuiltinData where
  type Unroll BuiltinData = '[BuiltinData]

instance HasBlueprintDefinition BuiltinUnit where
  type Unroll BuiltinUnit = '[BuiltinUnit]

instance HasBlueprintDefinition BuiltinString where
  type Unroll BuiltinString = '[BuiltinString]

instance HasBlueprintDefinition BuiltinByteString where
  type Unroll BuiltinByteString = '[BuiltinByteString]

instance HasBlueprintDefinition a => HasBlueprintDefinition (BuiltinList a) where
  type Unroll (BuiltinList a) = Insert (BuiltinList a) (Unrolled a)
  definitionId = definitionIdFromTypeK @(Type -> Type) @BuiltinList <> definitionId @a

instance
  (HasBlueprintDefinition a, HasBlueprintDefinition b)
  => HasBlueprintDefinition (BuiltinPair a b)
  where
  type Unroll (BuiltinPair a b) = Insert (BuiltinPair a b) (Unrolled a ++ Unrolled b)
  definitionId =
    definitionIdFromTypeK @(Type -> Type -> Type) @BuiltinPair
      <> definitionId @a
      <> definitionId @b

instance HasBlueprintDefinition a => HasBlueprintDefinition (Maybe a) where
  type Unroll (Maybe a) = Insert (Maybe a) (Unrolled a)
  definitionId = definitionIdFromTypeK @(Type -> Type) @Maybe <> definitionId @a

instance HasBlueprintDefinition a => HasBlueprintDefinition [a] where
  type Unroll [a] = Insert [a] (Unrolled a)
  definitionId = definitionIdList <> definitionId @a

instance (HasBlueprintDefinition a, HasBlueprintDefinition b) => HasBlueprintDefinition (a, b) where
  type Unroll (a, b) = Insert (a, b) (Unrolled a ++ Unrolled b)
  definitionId = definitionIdTuple2 <> definitionId @a <> definitionId @b

instance
  (HasBlueprintDefinition a, HasBlueprintDefinition b, HasBlueprintDefinition c)
  => HasBlueprintDefinition (a, b, c)
  where
  type Unroll (a, b, c) = Insert (a, b, c) (Unrolled a ++ Unrolled b ++ Unrolled c)
  definitionId = definitionIdTuple3 <> definitionId @a <> definitionId @b <> definitionId @c

{-| Compile-time error that happens when a type couldn't be unrolled
('Unroll' TF is "stuck") -}
type family UnrollIsStuckError x where
  UnrollIsStuckError x =
    GHC.TypeError (GHC.Text "No instance: " GHC.:<>: GHC.ShowType (HasBlueprintDefinition x))

{-| Compile-time error that happens when type's generic representation is not defined
('Rep' TF is "stuck") -}
type family RepIsStuckError x where
  RepIsStuckError x =
    GHC.TypeError (GHC.Text "No instance: " GHC.:<>: GHC.ShowType (Generic x))

-- | Same as 'Unroll' but with a nicer error message
type Unrolled t = Reverse (IfStuckUnroll (UnrollIsStuckError t) (Unroll t))

-- | Unrolls all types in the list 'xs'
type family UnrollAll xs :: [Type] where
  UnrollAll '[] = '[]
  UnrollAll (x ': xs) = Nub (Concat (Unrolled x) (UnrollAll xs))

-- | Unroll a generic representation of a type into a list of all nested types.
type family GUnroll (t :: Type -> Type) :: [Type] where
  GUnroll (M1 _ _ f) = GUnroll f
  GUnroll (f :*: g) = GUnroll f ++ GUnroll g
  GUnroll (f :+: g) = GUnroll f ++ GUnroll g
  GUnroll (K1 _ c) = Unrolled c
  GUnroll U1 = '[]
