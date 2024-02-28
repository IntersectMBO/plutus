{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}

module Blueprint.Fixture where

import Prelude

import Control.Lens (over)
import Data.ByteString (ByteString)
import Flat qualified
import PlutusCore.Version (plcVersion110)
import PlutusTx hiding (Typeable)
import PlutusTx.Blueprint.Class (HasDataSchema (..))
import PlutusTx.Blueprint.Definition (AsDefinitionId, definitionRef)
import PlutusTx.Blueprint.Schema (Schema (..))
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

newtype Bytes = MkAcmeBytes BuiltinByteString
  deriving newtype (ToData, FromData, UnsafeFromData)
  deriving anyclass (AsDefinitionId)

instance HasDataSchema Bytes ts where
  dataSchema =
    SchemaBytes
      (Just "SchemaBytes") -- Title
      Nothing -- Description
      Nothing -- Comment
      [] -- Enum
      Nothing -- Min length
      Nothing -- Max length

data DatumPayload = MkDatumPayload
  { myAwesomeDatum1 :: Integer
  , myAwesomeDatum2 :: Bytes
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
  Flat.flat
    $ UPLC.UnrestrictedProgram
    $ over UPLC.progTerm (UPLC.termMapNames UPLC.unNameDeBruijn)
    $ PlutusTx.getPlcNoAnn validatorScript
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
