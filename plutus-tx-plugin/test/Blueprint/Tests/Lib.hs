{-# LANGUAGE BangPatterns          #-}
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

import Prelude

import Codec.Serialise (serialise)
import Control.Lens (over, (&))
import Data.ByteString (ByteString)
import Data.ByteString.Lazy qualified as LBS
import Data.Kind (Type)
import Data.Void (Void)
import Flat qualified
import PlutusCore.Version (plcVersion110)
import PlutusTx hiding (Typeable)
import PlutusTx.Blueprint.Class (HasSchema (..))
import PlutusTx.Blueprint.Definition (AsDefinitionId, definitionRef)
import PlutusTx.Blueprint.Schema (Schema (..), SchemaInfo (..), emptyBytesSchema, emptySchemaInfo)
import PlutusTx.Builtins (BuiltinByteString, BuiltinString, emptyByteString)
import PlutusTx.Prelude qualified as PlutusTx
import UntypedPlutusCore qualified as UPLC

data Params = MkParams
  { myUnit              :: ()
  , myBool              :: Bool
  , myInteger           :: Integer
  , myBuiltinData       :: BuiltinData
  , myBuiltinByteString :: BuiltinByteString
  }
  deriving anyclass (AsDefinitionId)

$(PlutusTx.makeLift ''Params)
$(makeIsDataSchemaIndexed ''Params [('MkParams, 0)])

newtype Bytes (phantom :: Type) = MkAcmeBytes BuiltinByteString
  deriving newtype (ToData, FromData, UnsafeFromData)
  deriving anyclass (AsDefinitionId)

instance HasSchema (Bytes phantom) ts where
  schema = SchemaBytes emptySchemaInfo{title = Just "SchemaBytes"} emptyBytesSchema

data DatumPayload = MkDatumPayload
  { myAwesomeDatum1 :: Integer
  , myAwesomeDatum2 :: Bytes Void
  }
  deriving anyclass (AsDefinitionId)

$(makeIsDataSchemaIndexed ''DatumPayload [('MkDatumPayload, 0)])

data Datum = DatumLeft | DatumRight DatumPayload
  deriving anyclass (AsDefinitionId)

$(makeIsDataSchemaIndexed ''Datum [('DatumLeft, 0), ('DatumRight, 1)])

type Redeemer = BuiltinString

type ScriptContext = ()

type Validator = Params -> Datum -> Redeemer -> ScriptContext -> Bool

serialisedScript :: ByteString
serialisedScript =
  PlutusTx.getPlcNoAnn validatorScript
    & over UPLC.progTerm (UPLC.termMapNames UPLC.unNameDeBruijn)
    & UPLC.UnrestrictedProgram
    & Flat.flat
    & serialise
    & LBS.toStrict
 where
  {-# INLINEABLE typedValidator #-}
  typedValidator :: Validator
  typedValidator _params _datum _redeemer _context = False

  {-# INLINEABLE untypedValidator #-}
  untypedValidator :: Params -> BuiltinData -> BuiltinString -> BuiltinData -> ()
  untypedValidator params datum redeemer ctx =
    PlutusTx.check $ typedValidator params acmeDatum acmeRedeemer scriptContext
   where
    acmeDatum :: Datum = PlutusTx.unsafeFromBuiltinData datum
    acmeRedeemer :: Redeemer = redeemer
    scriptContext :: ScriptContext = PlutusTx.unsafeFromBuiltinData ctx

  validatorScript :: PlutusTx.CompiledCode (BuiltinData -> BuiltinString -> BuiltinData -> ())
  validatorScript =
    $$(PlutusTx.compile [||untypedValidator||])
      `PlutusTx.unsafeApplyCode` PlutusTx.liftCode
        plcVersion110
        MkParams
          { myUnit = ()
          , myBool = True
          , myInteger = fromIntegral (maxBound @Int) + 1
          , myBuiltinData = PlutusTx.toBuiltinData (3 :: Integer)
          , myBuiltinByteString = emptyByteString
          }
