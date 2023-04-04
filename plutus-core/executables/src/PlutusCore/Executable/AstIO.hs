-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}

-- | Reading and writing ASTs with various name types in flat format.

module PlutusCore.Executable.AstIO
    ( serialisePirProgramFlat
    , serialisePlcProgramFlat
    , serialiseUplcProgramFlat
    , loadPirASTfromFlat
    , loadPlcASTfromFlat
    , loadUplcASTfromFlat)
where

import PlutusCore.Executable.Types

import PlutusCore qualified as PLC
import PlutusCore.DeBruijn (fakeNameDeBruijn, fakeTyNameDeBruijn, unNameDeBruijn, unNameTyDeBruijn)

import PlutusIR.Core.Instance.Pretty ()

import UntypedPlutusCore qualified as UPLC

import Control.Lens (traverseOf)
import Control.Monad.Except (runExcept, runExceptT)
import Data.ByteString.Lazy qualified as BSL
import Data.Functor ((<&>))
import Flat (Flat, flat, unflat)

type UplcProgDB ann = UPLC.Program PLC.DeBruijn PLC.DefaultUni PLC.DefaultFun ann
type UplcProgNDB ann = UPLC.Program PLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ann

type PlcProgDB ann = PLC.Program PLC.TyDeBruijn PLC.DeBruijn PLC.DefaultUni PLC.DefaultFun ann
type PlcProgNDB ann = PLC.Program PLC.NamedTyDeBruijn PLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ann

-- | PIR does not support names involving de Bruijn indices. We do allow these
-- formats here to facilitate code sharing, but issue the error below if they're
-- encountered.  This should never happen in practice because the options
-- parsers for the `pir` command only accept the Named and Textual formats.
unsupportedNameTypeError :: AstNameType -> a
unsupportedNameTypeError nameType = error $ "ASTs with " ++ show nameType ++ " names are not supported for PIR"

---------------- Name conversions ----------------

-- Untyped programs

-- | Convert an untyped program to one where the 'name' type is textual names
-- with de Bruijn indices.
toNamedDeBruijnUPLC :: UplcProg ann -> UplcProgNDB ann
toNamedDeBruijnUPLC prog =
    case runExcept @PLC.FreeVariableError $ traverseOf UPLC.progTerm UPLC.deBruijnTerm prog of
        Left e  -> error $ show e
        Right p -> p

-- | Convert an untyped program to one where the 'name' type is de Bruijn indices.
toDeBruijnUPLC :: UplcProg ann -> UplcProgDB ann
toDeBruijnUPLC = UPLC.programMapNames unNameDeBruijn . toNamedDeBruijnUPLC


-- | Convert an untyped program with named de Bruijn indices to one with textual names.
fromNamedDeBruijnUPLC :: UplcProgNDB ann -> UplcProg ann
fromNamedDeBruijnUPLC prog =
    case PLC.runQuote $
         runExceptT @PLC.FreeVariableError $ traverseOf UPLC.progTerm UPLC.unDeBruijnTerm prog of
      Left e  -> error $ show e
      Right p -> p

-- | Convert an untyped program with de Bruijn indices to one with textual names.
fromDeBruijnUPLC :: UplcProgDB ann -> UplcProg ann
fromDeBruijnUPLC = fromNamedDeBruijnUPLC . UPLC.programMapNames fakeNameDeBruijn

-- Typed programs

-- | Convert a typed program to one where the 'name' type is textual names with
-- de Bruijn indices.
toNamedDeBruijnPLC :: PlcProg ann -> PlcProgNDB ann
toNamedDeBruijnPLC prog =
    case runExcept @PLC.FreeVariableError $ traverseOf PLC.progTerm PLC.deBruijnTerm prog of
        Left e  -> error $ show e
        Right p -> p

-- | Convert a typed program to one where the 'name' type is de Bruijn indices.
toDeBruijnPLC :: PlcProg ann -> PlcProgDB ann
toDeBruijnPLC = PLC.programMapNames unNameTyDeBruijn unNameDeBruijn . toNamedDeBruijnPLC


-- | Convert a typed program with named de Bruijn indices to one with textual names.
fromNamedDeBruijnPLC :: PlcProgNDB ann -> PlcProg ann
fromNamedDeBruijnPLC prog = do
  case PLC.runQuote $
       runExceptT @PLC.FreeVariableError $ traverseOf PLC.progTerm PLC.unDeBruijnTerm prog of
    Left e  -> error $ show e
    Right p -> p

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
      Named         -> BSL.fromStrict . flat
      DeBruijn      -> unsupportedNameTypeError DeBruijn
      NamedDeBruijn -> unsupportedNameTypeError NamedDeBruijn

serialisePlcProgramFlat
    :: Flat ann
    => AstNameType
    -> PlcProg ann
    -> BSL.ByteString
serialisePlcProgramFlat =
    \case
     Named         -> BSL.fromStrict . flat
     DeBruijn      -> BSL.fromStrict . flat . toDeBruijnPLC
     NamedDeBruijn -> BSL.fromStrict . flat . toNamedDeBruijnPLC

serialiseUplcProgramFlat
    :: Flat ann
    => AstNameType
    -> UplcProg ann
    -> BSL.ByteString
serialiseUplcProgramFlat =
    \case
     Named         -> BSL.fromStrict . flat. UPLC.UnrestrictedProgram
     DeBruijn      -> BSL.fromStrict . flat. UPLC.UnrestrictedProgram . toDeBruijnUPLC
     NamedDeBruijn -> BSL.fromStrict . flat .UPLC.UnrestrictedProgram . toNamedDeBruijnUPLC

-- Deserialising ASTs from Flat

-- Read a binary-encoded file (eg, Flat-encoded PLC)
getBinaryInput :: Input -> IO BSL.ByteString
getBinaryInput StdInput         = BSL.getContents
getBinaryInput (FileInput file) = BSL.readFile file

unflatOrFail :: Flat a => BSL.ByteString -> a
unflatOrFail input =
    case unflat input of
     Left e  -> error $ "Flat deserialisation failure: " ++ show e
     Right r -> r

loadPirASTfromFlat
    :: Flat a
    => AstNameType
    -> Input
    -> IO (PirProg a)
loadPirASTfromFlat flatMode inp =
    getBinaryInput inp <&>
    case flatMode of
      Named -> unflatOrFail
      _     -> unsupportedNameTypeError flatMode

-- | Read and deserialise a Flat-encoded PIR/PLC AST
loadPlcASTfromFlat
    :: Flat a
    => AstNameType
    -> Input
    -> IO (PlcProg a)
loadPlcASTfromFlat flatMode inp =
    getBinaryInput inp <&>
    case flatMode of
      Named         -> unflatOrFail
      DeBruijn      -> unflatOrFail <&> fromDeBruijnPLC
      NamedDeBruijn -> unflatOrFail <&> fromNamedDeBruijnPLC

-- | Read and deserialise a Flat-encoded UPLC AST
loadUplcASTfromFlat
    :: Flat ann
    => AstNameType
    -> Input
    -> IO (UplcProg ann)
loadUplcASTfromFlat flatMode inp =
    getBinaryInput inp <&>
    case flatMode of
      Named         -> unflatOrFail <&> UPLC.unUnrestrictedProgram
      DeBruijn      -> unflatOrFail <&> UPLC.unUnrestrictedProgram <&> fromDeBruijnUPLC
      NamedDeBruijn -> unflatOrFail <&> UPLC.unUnrestrictedProgram <&> fromNamedDeBruijnUPLC

