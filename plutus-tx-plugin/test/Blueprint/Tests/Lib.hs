{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE BlockArguments        #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

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
import Data.Void (Void)
import Flat qualified
import GHC.Generics (Generic)
import PlutusTx.AsData (asData)
import PlutusTx.Blueprint.Class (HasSchema (..))
import PlutusTx.Blueprint.Definition (AsDefinitionId, definitionRef)
import PlutusTx.Blueprint.Schema (Schema (..), emptyBytesSchema)
import PlutusTx.Blueprint.Schema.Annotation (SchemaComment (..), SchemaDescription (..),
                                             SchemaInfo (..), SchemaTitle (..), emptySchemaInfo)
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)
import PlutusTx.Builtins.Internal (BuiltinByteString, BuiltinData, BuiltinString, emptyByteString)
import PlutusTx.Code qualified as PlutusTx
import PlutusTx.IsData (FromData, ToData (..), UnsafeFromData (..))
import PlutusTx.Lift (liftCodeDef, makeLift)
import PlutusTx.TH qualified as PlutusTx
import Prelude
import System.FilePath ((</>))
import Test.Tasty (TestName)
import Test.Tasty.Extras (TestNested)
import Test.Tasty.Golden (goldenVsFile)
import UntypedPlutusCore qualified as UPLC

----------------------------------------------------------------------------------------------------
-- Validator 1 for testing blueprints --------------------------------------------------------------

{-# ANN type Params (SchemaTitle "Acme Parameter") #-}
{-# ANN type Params (SchemaDescription "A parameter that does something awesome") #-}
data Params = MkParams
  { myUnit              :: ()
  , myBool              :: Bool
  , myInteger           :: Integer
  , myBuiltinData       :: BuiltinData
  , myBuiltinByteString :: BuiltinByteString
  }
  deriving stock (Generic)
  deriving anyclass (AsDefinitionId)

$(makeLift ''Params)
$(makeIsDataSchemaIndexed ''Params [('MkParams, 0)])

newtype Bytes (phantom :: Type) = MkAcmeBytes BuiltinByteString
  deriving stock (Generic)
  deriving anyclass (AsDefinitionId)
  deriving newtype (ToData, FromData, UnsafeFromData)

instance HasSchema (Bytes phantom) ts where
  schema = SchemaBytes emptySchemaInfo{title = Just "SchemaBytes"} emptyBytesSchema

{-# ANN MkDatumPayload (SchemaComment "MkDatumPayload") #-}

data DatumPayload = MkDatumPayload
  { myAwesomeDatum1 :: Integer
  , myAwesomeDatum2 :: Bytes Void
  }
  deriving stock (Generic)
  deriving anyclass (AsDefinitionId)

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
  deriving anyclass (AsDefinitionId)

{-# ANN type Redeemer (SchemaTitle "Acme Redeemer") #-}
{-# ANN type Redeemer (SchemaDescription "A redeemer that does something awesome") #-}

type Redeemer = BuiltinString

type ScriptContext = ()

$(makeIsDataSchemaIndexed ''DatumPayload [('MkDatumPayload, 0)])
$(makeIsDataSchemaIndexed ''Datum [('DatumLeft, 0), ('DatumRight, 1)])

{-# INLINEABLE typedValidator1 #-}
typedValidator1 :: Params -> Datum -> Redeemer -> ScriptContext -> Bool
typedValidator1 _params _datum _redeemer _context = False

validatorScript1 :: PlutusTx.CompiledCode (Datum -> Redeemer -> ScriptContext -> Bool)
validatorScript1 =
  $$(PlutusTx.compile [||typedValidator1||])
    `PlutusTx.unsafeApplyCode` liftCodeDef
      MkParams
        { myUnit = ()
        , myBool = True
        , myInteger = fromIntegral (maxBound @Int) + 1
        , myBuiltinData = toBuiltinData (3 :: Integer)
        , myBuiltinByteString = emptyByteString
        }

----------------------------------------------------------------------------------------------------
-- Validator 2 for testing blueprints --------------------------------------------------------------

newtype Param2a = MkParam2a Bool
  deriving stock (Generic)
  deriving anyclass (AsDefinitionId)

$(makeLift ''Param2a)
$(makeIsDataSchemaIndexed ''Param2a [('MkParam2a, 0)])

newtype Param2b = MkParam2b Bool
  deriving stock (Generic)
  deriving anyclass (AsDefinitionId)

$(makeLift ''Param2b)
$(makeIsDataSchemaIndexed ''Param2b [('MkParam2b, 0)])

$(asData datum2)

type Redeemer2 = Integer

{-# INLINEABLE typedValidator2 #-}
typedValidator2 :: Param2a -> Param2b -> Datum2 -> Redeemer2 -> ScriptContext -> Bool
typedValidator2 _p1 _p2 _datum _redeemer _context = True

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
  pure $ goldenVsFile name golden actual (cb actual)
