{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE BlockArguments        #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module Blueprint.Tests.Lib where

import Codec.Serialise (serialise)
import Control.Lens (over, (&))
import Control.Monad.Reader (asks)
import Data.ByteString (ByteString)
import Data.ByteString.Lazy qualified as LBS
import Data.Kind (Type)
import Data.Void (Void)
import Flat qualified
import GHC.Generics (Generic)
import PlutusCore.Version (plcVersion110)
import PlutusTx.Blueprint.Class (HasSchema (..))
import PlutusTx.Blueprint.Definition (AsDefinitionId, definitionRef)
import PlutusTx.Blueprint.Schema (Schema (..), emptyBytesSchema)
import PlutusTx.Blueprint.Schema.Annotation (SchemaComment (..), SchemaDescription (..),
                                             SchemaInfo (..), SchemaTitle (..), emptySchemaInfo)
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)
import PlutusTx.Builtins.Internal (BuiltinByteString, BuiltinData, BuiltinString, emptyByteString)
import PlutusTx.Code qualified as PlutusTx
import PlutusTx.IsData.Class (FromData, ToData (..), UnsafeFromData (..))
import PlutusTx.IsData.Class qualified as PlutusTx
import PlutusTx.Lift qualified as PlutusTx
import PlutusTx.Prelude qualified as PlutusTx
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

$(PlutusTx.makeLift ''Params)
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

{-# INLINEABLE untypedValidator1 #-}
untypedValidator1 :: Params -> BuiltinData -> BuiltinString -> BuiltinData -> ()
untypedValidator1 params datum redeemer ctx =
  PlutusTx.check $ typedValidator1 params acmeDatum acmeRedeemer scriptContext
 where
  acmeDatum :: Datum = PlutusTx.unsafeFromBuiltinData datum
  acmeRedeemer :: Redeemer = redeemer
  scriptContext :: ScriptContext = PlutusTx.unsafeFromBuiltinData ctx

validatorScript1 :: PlutusTx.CompiledCode (BuiltinData -> BuiltinString -> BuiltinData -> ())
validatorScript1 =
  $$(PlutusTx.compile [||untypedValidator1||])
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode
      plcVersion110
      MkParams
        { myUnit = ()
        , myBool = True
        , myInteger = fromIntegral (maxBound @Int) + 1
        , myBuiltinData = PlutusTx.toBuiltinData (3 :: Integer)
        , myBuiltinByteString = emptyByteString
        }

----------------------------------------------------------------------------------------------------
-- Validator 2 for testing blueprints --------------------------------------------------------------

data Params2 = MkParams2 Bool Bool
  deriving stock (Generic)
  deriving anyclass (AsDefinitionId)

$(PlutusTx.makeLift ''Params2)
$(makeIsDataSchemaIndexed ''Params2 [('MkParams2, 0)])

type Datum2 = Integer
type Redeemer2 = Integer

{-# INLINEABLE typedValidator2 #-}
typedValidator2 :: Params2 -> Datum2 -> Redeemer2 -> ScriptContext -> Bool
typedValidator2 _params _datum _redeemer _context = True

untypedValidator2 :: Params2 -> BuiltinData -> BuiltinData -> BuiltinData -> ()
untypedValidator2 params datum redeemer ctx =
  PlutusTx.check $ typedValidator2 params datum2 redeemer2 scriptContext
 where
  datum2 :: Datum2 = PlutusTx.unsafeFromBuiltinData datum
  redeemer2 :: Redeemer2 = PlutusTx.unsafeFromBuiltinData redeemer
  scriptContext :: ScriptContext = PlutusTx.unsafeFromBuiltinData ctx

validatorScript2 :: PlutusTx.CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())
validatorScript2 =
  $$(PlutusTx.compile [||untypedValidator2||])
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 (MkParams2 True False)

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
