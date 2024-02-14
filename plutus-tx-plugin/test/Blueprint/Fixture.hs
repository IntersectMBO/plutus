{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
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

import Data.ByteString (ByteString)
import Flat qualified
import PlutusCore.Version (plcVersion110)
import PlutusPrelude (over)
import PlutusTx
import PlutusTx.Builtins.Internal (BuiltinByteString, BuiltinInteger, emptyByteString)
import PlutusTx.Prelude qualified as PlutusTx
import UntypedPlutusCore qualified as UPLC

data AcmeParams = MkAcmeParams
  { myAwesomeParameter1 :: Integer
  , myAwesomeParameter2 :: BuiltinInteger
  , myAwesomeParameter3 :: BuiltinData
  , myAwesomeParameter4 :: BuiltinByteString
  }

$(PlutusTx.makeLift ''AcmeParams)
$(makeIsDataSchemaIndexed ''AcmeParams [('MkAcmeParams, 0)])

data AcmeDatumPayload = MkAcmeDatumPayload
  { myAwesomeDatum1 :: Integer
  , myAwesomeDatum2 :: Integer
  }

$(makeIsDataSchemaIndexed ''AcmeDatumPayload [('MkAcmeDatumPayload, 0)])

data AcmeDatum = AcmeDatumLeft | AcmeDatumRight AcmeDatumPayload

$(makeIsDataSchemaIndexed ''AcmeDatum [('AcmeDatumLeft, 0), ('AcmeDatumRight, 1)])

type AcmeRedeemer = Integer

type ScriptContext = ()

type AcmeValidator = AcmeParams -> AcmeDatum -> AcmeRedeemer -> ScriptContext -> Bool

serialisedScript :: ByteString
serialisedScript =
  Flat.flat
    $ UPLC.UnrestrictedProgram
    $ over UPLC.progTerm (UPLC.termMapNames UPLC.unNameDeBruijn)
    $ PlutusTx.getPlcNoAnn acmeValidatorScript
 where
  {-# INLINEABLE acmeTypedValidator #-}
  acmeTypedValidator :: AcmeValidator
  acmeTypedValidator _params _datum _redeemer _context = False

  {-# INLINEABLE acmeUntypedValidator #-}
  acmeUntypedValidator :: AcmeParams -> BuiltinData -> BuiltinData -> BuiltinData -> ()
  acmeUntypedValidator params datum redeemer ctx =
    PlutusTx.check $ acmeTypedValidator params acmeDatum acmeRedeemer scriptContext
   where
    acmeDatum :: AcmeDatum = PlutusTx.unsafeFromBuiltinData datum
    acmeRedeemer :: AcmeRedeemer = PlutusTx.unsafeFromBuiltinData redeemer
    scriptContext :: ScriptContext = PlutusTx.unsafeFromBuiltinData ctx

  acmeValidatorScript :: PlutusTx.CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())
  acmeValidatorScript =
    $$(PlutusTx.compile [||acmeUntypedValidator||])
      `PlutusTx.unsafeApplyCode` PlutusTx.liftCode
        plcVersion110
        MkAcmeParams
          { myAwesomeParameter1 = 1
          , myAwesomeParameter2 = 2
          , myAwesomeParameter3 = PlutusTx.toBuiltinData (3 :: Integer)
          , myAwesomeParameter4 = emptyByteString
          }
