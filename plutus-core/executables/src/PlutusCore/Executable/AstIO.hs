-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

-- | Reading and writing ASTs with various name types in flat format.
module PlutusCore.Executable.AstIO
  ( serialisePirProgramFlat
  , serialisePlcProgramFlat
  , serialiseUplcProgramFlat
  , loadPirASTfromFlat
  , loadPlcASTfromFlat
  , loadUplcASTfromFlat
  , fromNamedDeBruijnUPLC
  , toDeBruijnTermPLC
  , toDeBruijnTermUPLC
  , toDeBruijnTypePLC
  , toNamedDeBruijnUPLC
  )
where

import PlutusCore.Executable.Types
import PlutusPrelude

import PlutusCore qualified as PLC
import PlutusCore.DeBruijn
  ( deBruijnTy
  , fakeNameDeBruijn
  , fakeTyNameDeBruijn
  , unNameDeBruijn
  , unNameTyDeBruijn
  )

import PlutusIR.Core.Instance.Pretty ()

import UntypedPlutusCore qualified as UPLC

import Control.Lens (traverseOf)
import Data.ByteString.Lazy qualified as BSL
import PlutusCore.Flat (Flat, flat, unflat)

type UplcProgDB ann = UPLC.Program PLC.DeBruijn PLC.DefaultUni PLC.DefaultFun ann
type UplcProgNDB ann = UPLC.Program PLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ann

type PlcProgDB ann = PLC.Program PLC.TyDeBruijn PLC.DeBruijn PLC.DefaultUni PLC.DefaultFun ann
type PlcProgNDB ann = PLC.Program PLC.NamedTyDeBruijn PLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ann

-- For the plutus-metatheory tests
type UplcTermDB ann = UPLC.Term PLC.DeBruijn PLC.DefaultUni PLC.DefaultFun ann
type UplcTermNDB ann = UPLC.Term PLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ann

type PlcTermDB ann = PLC.Term PLC.TyDeBruijn PLC.DeBruijn PLC.DefaultUni PLC.DefaultFun ann
type PlcTermNDB ann = PLC.Term PLC.NamedTyDeBruijn PLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ann

type PlcType ann = PLC.Type PLC.TyName PLC.DefaultUni ann
type PlcTypeDB ann = PLC.Type PLC.TyDeBruijn PLC.DefaultUni ann
type PlcTypeNDB ann = PLC.Type PLC.NamedTyDeBruijn PLC.DefaultUni ann

{-| PIR does not support names involving de Bruijn indices. We do allow these
formats here to facilitate code sharing, but issue the error below if they're
encountered.  This should never happen in practice because the options
parsers for the `pir` command only accept the Named and Textual formats. -}
unsupportedNameTypeError :: AstNameType -> a
unsupportedNameTypeError nameType = error $ "ASTs with " ++ show nameType ++ " names are not supported for PIR"

---------------- Name conversions ----------------

-- Untyped terms and programs
{-| Convert an untyped term to one where the 'name' type is textual names
with de Bruijn indices. -}
toNamedDeBruijnTermUPLC :: UplcTerm ann -> UplcTermNDB ann
toNamedDeBruijnTermUPLC = unsafeFromRight @PLC.FreeVariableError . UPLC.deBruijnTerm

-- | Convert an untyped term to one where the 'name' type is de Bruijn indices.
toDeBruijnTermUPLC :: UplcTerm ann -> UplcTermDB ann
toDeBruijnTermUPLC = UPLC.termMapNames unNameDeBruijn . toNamedDeBruijnTermUPLC

{-| Convert an untyped program to one where the 'name' type is textual names
with de Bruijn indices. -}
toNamedDeBruijnUPLC :: UplcProg ann -> UplcProgNDB ann
toNamedDeBruijnUPLC (UPLC.Program ann ver term) =
  UPLC.Program ann ver (toNamedDeBruijnTermUPLC term)

-- | Convert an untyped program to one where the 'name' type is de Bruijn indices.
toDeBruijnUPLC :: UplcProg ann -> UplcProgDB ann
toDeBruijnUPLC (UPLC.Program ann ver term) =
  UPLC.Program ann ver (toDeBruijnTermUPLC term)

-- | Convert an untyped program with named de Bruijn indices to one with textual names.
fromNamedDeBruijnUPLC :: UplcProgNDB ann -> UplcProg ann
fromNamedDeBruijnUPLC =
  unsafeFromRight @PLC.FreeVariableError
    . PLC.runQuoteT
    . traverseOf UPLC.progTerm UPLC.unDeBruijnTerm

-- | Convert an untyped program with de Bruijn indices to one with textual names.
fromDeBruijnUPLC :: UplcProgDB ann -> UplcProg ann
fromDeBruijnUPLC = fromNamedDeBruijnUPLC . UPLC.programMapNames fakeNameDeBruijn

-- Typed terms and programs

{-| Convert a typed term to one where the 'name' type is textual names
with de Bruijn indices. -}
toNamedDeBruijnTermPLC :: PlcTerm ann -> PlcTermNDB ann
toNamedDeBruijnTermPLC = unsafeFromRight @PLC.FreeVariableError . PLC.deBruijnTerm

-- | Convert a typed term to one where the 'name' type is de Bruijn indices.
toDeBruijnTermPLC :: PlcTerm ann -> PlcTermDB ann
toDeBruijnTermPLC = PLC.termMapNames unNameTyDeBruijn unNameDeBruijn . toNamedDeBruijnTermPLC

{-| Convert a typed program to one where the 'name' type is textual names with
de Bruijn indices. -}
toNamedDeBruijnPLC :: PlcProg ann -> PlcProgNDB ann
toNamedDeBruijnPLC (PLC.Program ann ver term) =
  PLC.Program ann ver (toNamedDeBruijnTermPLC term)

-- | Convert a typed program to one where the 'name' type is de Bruijn indices.
toDeBruijnPLC :: PlcProg ann -> PlcProgDB ann
toDeBruijnPLC (PLC.Program ann ver term) =
  PLC.Program ann ver (toDeBruijnTermPLC term)

-- | Convert a type to one where the 'tyname' type is named de Bruijn indices.
toNamedDeBruijnTypePLC :: PlcType ann -> PlcTypeNDB ann
toNamedDeBruijnTypePLC = unsafeFromRight @PLC.FreeVariableError . deBruijnTy

-- | Convert a type to one where the 'tyname' type is de Bruijn indices.
toDeBruijnTypePLC :: PlcType ann -> PlcTypeDB ann
toDeBruijnTypePLC = PLC.typeMapNames unNameTyDeBruijn . toNamedDeBruijnTypePLC

-- | Convert a typed program with named de Bruijn indices to one with textual names.
fromNamedDeBruijnPLC :: PlcProgNDB ann -> PlcProg ann
fromNamedDeBruijnPLC =
  unsafeFromRight @PLC.FreeVariableError
    . PLC.runQuoteT
    . traverseOf PLC.progTerm PLC.unDeBruijnTerm

-- | Convert a typed program with de Bruijn indices to one with textual names.
fromDeBruijnPLC :: PlcProgDB ann -> PlcProg ann
fromDeBruijnPLC = fromNamedDeBruijnPLC . PLC.programMapNames fakeTyNameDeBruijn fakeNameDeBruijn

-- Flat serialisation in various formats.

serialisePirProgramFlat
  :: Flat ann
  => AstNameType
  -> PirProg ann
  -> BSL.ByteString
serialisePirProgramFlat =
  \case
    Named -> BSL.fromStrict . flat
    DeBruijn -> unsupportedNameTypeError DeBruijn
    NamedDeBruijn -> unsupportedNameTypeError NamedDeBruijn

serialisePlcProgramFlat
  :: Flat ann
  => AstNameType
  -> PlcProg ann
  -> BSL.ByteString
serialisePlcProgramFlat =
  \case
    Named -> BSL.fromStrict . flat
    DeBruijn -> BSL.fromStrict . flat . toDeBruijnPLC
    NamedDeBruijn -> BSL.fromStrict . flat . toNamedDeBruijnPLC

serialiseUplcProgramFlat
  :: Flat ann
  => AstNameType
  -> UplcProg ann
  -> BSL.ByteString
serialiseUplcProgramFlat =
  \case
    Named -> BSL.fromStrict . flat . UPLC.UnrestrictedProgram
    DeBruijn -> BSL.fromStrict . flat . UPLC.UnrestrictedProgram . toDeBruijnUPLC
    NamedDeBruijn -> BSL.fromStrict . flat . UPLC.UnrestrictedProgram . toNamedDeBruijnUPLC

-- Deserialising ASTs from Flat

-- Read a binary-encoded file (eg, Flat-encoded PLC)
getBinaryInput :: Input -> IO BSL.ByteString
getBinaryInput StdInput = BSL.getContents
getBinaryInput (FileInput file) = BSL.readFile file

unflatOrFail :: Flat a => BSL.ByteString -> a
unflatOrFail input =
  case unflat input of
    Left e -> error $ "Flat deserialisation failure: " ++ show e
    Right r -> r

loadPirASTfromFlat
  :: Flat a
  => AstNameType
  -> Input
  -> IO (PirProg a)
loadPirASTfromFlat flatMode inp =
  getBinaryInput inp
    <&> case flatMode of
      Named -> unflatOrFail
      _ -> unsupportedNameTypeError flatMode

-- | Read and deserialise a Flat-encoded PIR/PLC AST
loadPlcASTfromFlat
  :: Flat a
  => AstNameType
  -> Input
  -> IO (PlcProg a)
loadPlcASTfromFlat flatMode inp =
  getBinaryInput inp
    <&> case flatMode of
      Named -> unflatOrFail
      DeBruijn -> unflatOrFail <&> fromDeBruijnPLC
      NamedDeBruijn -> unflatOrFail <&> fromNamedDeBruijnPLC

-- | Read and deserialise a Flat-encoded UPLC AST
loadUplcASTfromFlat
  :: Flat ann
  => AstNameType
  -> Input
  -> IO (UplcProg ann)
loadUplcASTfromFlat flatMode inp =
  getBinaryInput inp
    <&> case flatMode of
      Named -> unflatOrFail <&> UPLC.unUnrestrictedProgram
      DeBruijn -> unflatOrFail <&> UPLC.unUnrestrictedProgram <&> fromDeBruijnUPLC
      NamedDeBruijn -> unflatOrFail <&> UPLC.unUnrestrictedProgram <&> fromNamedDeBruijnUPLC
