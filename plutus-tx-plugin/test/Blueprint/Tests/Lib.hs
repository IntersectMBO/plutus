{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Blueprint.Tests.Lib
  ( module Blueprint.Tests.Lib
  , module AsData
  ) where

import Blueprint.Tests.Lib.AsData.Decls as AsData (datum2)
import Codec.Serialise (serialise)
import Control.Lens (over, (&))
import Control.Monad.Reader (asks)
import Data.ByteString (ByteString)
import Data.ByteString.Lazy qualified as LBS
import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Data.Void (Void)
import GHC.Generics (Generic)
import PlutusCore.Flat qualified as Flat
import PlutusTx.AsData (asData)
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Definition
  ( HasBlueprintDefinition (..)
  , Unrolled
  , definitionIdFromTypeK
  , definitionRef
  )
import PlutusTx.Blueprint.Schema (Schema (..), emptyBytesSchema)
import PlutusTx.Blueprint.Schema.Annotation
  ( SchemaComment (..)
  , SchemaDescription (..)
  , SchemaInfo (..)
  , SchemaTitle (..)
  , emptySchemaInfo
  )
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)
import PlutusTx.Builtins.Internal (BuiltinByteString, BuiltinData, BuiltinString, emptyByteString)
import PlutusTx.Code qualified as PlutusTx
import PlutusTx.IsData (FromData, ToData (..), UnsafeFromData (..))
import PlutusTx.Lift (liftCodeDef, makeLift)
import PlutusTx.TH qualified as PlutusTx
import System.FilePath ((</>))
import Test.Tasty (TestName)
import Test.Tasty.Extras (TestNested, embed)
import Test.Tasty.Golden (goldenVsFile)
import UntypedPlutusCore qualified as UPLC
import Prelude

----------------------------------------------------------------------------------------------------
-- Validator 1 for testing blueprints --------------------------------------------------------------

{-# ANN type Params (SchemaTitle "Acme Parameter") #-}
{-# ANN type Params (SchemaDescription "A parameter that does something awesome") #-}
data Params = MkParams
  { myUnit :: ()
  , myBool :: Bool
  , myInteger :: Integer
  , myListOfInts :: [Integer]
  , myBuiltinData :: BuiltinData
  , myBuiltinByteString :: BuiltinByteString
  }
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

$(makeLift ''Params)
$(makeIsDataSchemaIndexed ''Params [('MkParams, 0)])

unrolledParams
  :: Unrolled Params
    :~: [ Params
        , Bool
        , ()
        , [Integer]
        , Integer
        , BuiltinData
        , BuiltinByteString
        ]
unrolledParams = Refl

newtype Bytes (phantom :: Type) = MkAcmeBytes BuiltinByteString
  deriving newtype (ToData, FromData, UnsafeFromData)

instance HasBlueprintDefinition phantom => HasBlueprintDefinition (Bytes phantom) where
  type Unroll (Bytes phantom) = '[Bytes phantom]
  definitionId = definitionIdFromTypeK @(Type -> Type) @Bytes <> definitionId @phantom

instance HasBlueprintSchema (Bytes phantom) ts where
  schema = SchemaBytes emptySchemaInfo {title = Just "SchemaBytes"} emptyBytesSchema

{-# ANN MkDatumPayload (SchemaComment "MkDatumPayload") #-}

data DatumPayload = MkDatumPayload
  { myAwesomeDatum1 :: Integer
  , myAwesomeDatum2 :: Bytes Void
  }
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

unrolledDatumPayload :: Unrolled DatumPayload :~: [DatumPayload, Integer, Bytes Void]
unrolledDatumPayload = Refl

{-# ANN type Datum (SchemaTitle "Acme Datum") #-}
{-# ANN type Datum (SchemaDescription "A datum that contains something awesome") #-}

{-# ANN DatumLeft (SchemaTitle "Datum") #-}
{-# ANN DatumLeft (SchemaDescription "DatumLeft") #-}
{-# ANN DatumLeft (SchemaComment "This constructor is parameterless") #-}

{-# ANN DatumRight (SchemaTitle "Datum") #-}
{-# ANN DatumRight (SchemaDescription "DatumRight") #-}
{-# ANN DatumRight (SchemaComment "This constructor has a payload") #-}

data Datum = DatumLeft | DatumRight DatumPayload
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

unrolledDatum :: Unrolled Datum :~: [Datum, Bytes Void, Integer, DatumPayload]
unrolledDatum = Refl

{-# ANN type Redeemer (SchemaTitle "Acme Redeemer") #-}
{-# ANN type Redeemer (SchemaDescription "A redeemer that does something awesome") #-}

type Redeemer = BuiltinString

type ScriptContext = ()

$(makeIsDataSchemaIndexed ''DatumPayload [('MkDatumPayload, 0)])
$(makeIsDataSchemaIndexed ''Datum [('DatumLeft, 0), ('DatumRight, 1)])

typedValidator1 :: Params -> Datum -> Redeemer -> ScriptContext -> Bool
typedValidator1 _params _datum _redeemer _context = False
{-# INLINEABLE typedValidator1 #-}

validatorScript1 :: PlutusTx.CompiledCode (Datum -> Redeemer -> ScriptContext -> Bool)
validatorScript1 =
  $$(PlutusTx.compile [||typedValidator1||])
    `PlutusTx.unsafeApplyCode` liftCodeDef
      MkParams
        { myUnit = ()
        , myBool = True
        , myInteger = fromIntegral (maxBound @Int) + 1
        , myListOfInts = [1, 2, 3]
        , myBuiltinData = toBuiltinData (3 :: Integer)
        , myBuiltinByteString = emptyByteString
        }

----------------------------------------------------------------------------------------------------
-- Validator 2 for testing blueprints --------------------------------------------------------------

newtype Param2a = MkParam2a Bool
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

$(makeLift ''Param2a)
$(makeIsDataSchemaIndexed ''Param2a [('MkParam2a, 0)])

newtype Param2b = MkParam2b Bool
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)

$(makeLift ''Param2b)
$(makeIsDataSchemaIndexed ''Param2b [('MkParam2b, 0)])

$(asData datum2)

type Redeemer2 = Integer

typedValidator2 :: Param2a -> Param2b -> Datum2 -> Redeemer2 -> ScriptContext -> Bool
typedValidator2 _p1 _p2 _datum _redeemer _context = True
{-# INLINEABLE typedValidator2 #-}

validatorScript2 :: PlutusTx.CompiledCode (Datum2 -> Redeemer2 -> ScriptContext -> Bool)
validatorScript2 =
  $$(PlutusTx.compile [||typedValidator2||])
    `PlutusTx.unsafeApplyCode` liftCodeDef (MkParam2a False)
    `PlutusTx.unsafeApplyCode` liftCodeDef (MkParam2b True)

----------------------------------------------------------------------------------------------------
-- Helper functions --------------------------------------------------------------------------------

serialisedScript :: PlutusTx.CompiledCode t -> ByteString
serialisedScript validatorScript =
  PlutusTx.getPlcNoAnn validatorScript
    & over UPLC.progTerm (UPLC.termMapNames UPLC.unNameDeBruijn)
    & UPLC.UnrestrictedProgram
    & Flat.flat
    & serialise
    & LBS.toStrict

goldenJson :: TestName -> (FilePath -> IO ()) -> TestNested
goldenJson name cb = do
  goldenPath <- asks $ foldr (</>) name
  let actual = goldenPath ++ ".actual.json"
  let golden = goldenPath ++ ".golden.json"
  embed $ goldenVsFile name golden actual (cb actual)
