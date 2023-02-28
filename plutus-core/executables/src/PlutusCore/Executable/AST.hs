-- editorconfig-checker-disable-file
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}

module PlutusCore.Executable.AST where

import PlutusCore.Executable.Types

import PlutusCore qualified as PLC
import PlutusCore.DeBruijn (fakeNameDeBruijn, unNameDeBruijn, unNameTyDeBruijn)

import PlutusIR qualified as PIR
import PlutusIR.Core.Instance.Pretty ()
import PlutusIR.Core.Type qualified as PIR

import UntypedPlutusCore qualified as UPLC

import Control.Lens hiding (ix, op)
import Control.Monad.Except
import Data.ByteString.Lazy qualified as BSL
import Flat (Flat, flat, unflat)


unsupported = error "UNSUPPORTED"

-- Flat serialisation in various formats.

serialisePirProgramFlat nameType p =
    case nameType of
      Named         -> pure $ BSL.fromStrict $ flat p
      DeBruijn      -> BSL.fromStrict . flat <$> toDeBruijnPIR p
      NamedDeBruijn -> BSL.fromStrict . flat <$> toNamedDeBruijnPIR p

serialisePlcProgramFlat nameType p =
        case nameType of
          Named         -> pure $ BSL.fromStrict $ flat p
          DeBruijn      -> BSL.fromStrict . flat <$> toDeBruijnPLC p
          NamedDeBruijn -> BSL.fromStrict . flat <$> toNamedDeBruijnPLC p

serialiseUplcProgramFlat nameType p =
        case nameType of
          Named         -> pure $ BSL.fromStrict $ flat p
          DeBruijn      -> BSL.fromStrict . flat <$> toDeBruijnUPLC p
          NamedDeBruijn -> BSL.fromStrict . flat <$> toNamedDeBruijnUPLC p


---------------- Name conversions ----------------

-- | Convert an untyped program to one where the 'name' type is de Bruijn indices.
toDeBruijnUPLC :: UplcProg ann -> IO (UPLC.Program UPLC.DeBruijn PLC.DefaultUni PLC.DefaultFun ann)
toDeBruijnUPLC prog =
    case runExcept @UPLC.FreeVariableError $ traverseOf UPLC.progTerm UPLC.deBruijnTerm prog of
        Left e  -> error $ show e
        Right p -> return $ UPLC.programMapNames unNameDeBruijn p

{- | Convert an untyped program to one where the 'name' type is
 textual names with de Bruijn indices.
-}
toNamedDeBruijnUPLC ::
    UplcProg ann ->
    IO (UPLC.Program UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ann)
toNamedDeBruijnUPLC prog =
    case runExcept @PLC.FreeVariableError $ traverseOf UPLC.progTerm UPLC.deBruijnTerm prog of
        Left e  -> error $ show e
        Right p -> return p

-- | Convert a typed program to one where the 'name' type is de Bruijn indices.
toDeBruijnPLC :: PlcProg ann -> IO (PLC.Program PLC.TyDeBruijn PLC.DeBruijn PLC.DefaultUni PLC.DefaultFun ann)
toDeBruijnPLC prog =
    case runExcept @PLC.FreeVariableError $ traverseOf PLC.progTerm PLC.deBruijnTerm prog of
        Left e  -> error $ show e
        Right p -> return $ PLC.programMapNames unNameTyDeBruijn unNameDeBruijn  p

{- | Convert a typed program to one where the 'name' type is textual names with de
 Bruijn indices.
-}
toNamedDeBruijnPLC ::
    PlcProg ann ->
    IO (PLC.Program PLC.NamedTyDeBruijn PLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ann)
toNamedDeBruijnPLC prog =
    case runExcept @PLC.FreeVariableError $ traverseOf PLC.progTerm PLC.deBruijnTerm prog of
        Left e  -> error $ show e
        Right p -> return p

-- | Convert a typed program to one where the 'name' type is de Bruijn indices.
toDeBruijnPIR :: PirProg ann -> IO (PIR.Program PLC.TyDeBruijn PLC.DeBruijn PLC.DefaultUni PLC.DefaultFun ann)
toDeBruijnPIR prog = unsupported
{- | Convert a typed program to one where the 'name' type is textual names with de
 Bruijn indices.
-}
toNamedDeBruijnPIR ::
    PirProg ann ->
    IO (PIR.Program PLC.NamedTyDeBruijn PLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ann)
toNamedDeBruijnPIR prog = unsupported


-- Deserialising ASTs from Flat

fakeTyNameDeBruijn :: PLC.DeBruijn -> PLC.NamedTyDeBruijn
fakeTyNameDeBruijn = PLC.NamedTyDeBruijn . fakeNameDeBruijn

type UplcProgramNdB ann = UPLC.Program PLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ann
type PirProgramNdB ann = PIR.Program PLC.NamedTyDeBruijn PLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ann
type PlcProgramNdB ann = PLC.Program PLC.NamedTyDeBruijn PLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ann

-- Read a binary-encoded file (eg, Flat-encoded PLC)
getBinaryInput :: Input -> IO BSL.ByteString
getBinaryInput StdInput         = BSL.getContents
getBinaryInput (FileInput file) = BSL.readFile file

loadPirASTfromFlat :: Flat a => AstNameType -> Input -> IO (PirProg a)
loadPirASTfromFlat flatMode inp = do
    input <- getBinaryInput inp
    case flatMode of
        Named         -> handleResult $ unflat input
        DeBruijn      -> unsupported
        NamedDeBruijn -> unsupported
    where
      handleResult =
          \case
           Left e  -> error $ "Flat deserialisation failure: " ++ show e
           Right r -> return r


-- | Read and deserialise a Flat-encoded PIR/PLC AST
loadPlcASTfromFlat :: Flat a => AstNameType -> Input -> IO (PlcProg a)
loadPlcASTfromFlat flatMode inp = do
    input <- getBinaryInput inp
    case flatMode of
        Named     -> handleResult $ unflat input
        DeBruijn  ->
            do
              deserialised <- handleResult $ unflat input
              let namedProgram = PLC.programMapNames fakeTyNameDeBruijn fakeNameDeBruijn deserialised
              fromDeBruijn namedProgram
        NamedDeBruijn ->
            do
              deserialised <- handleResult $ unflat input
              fromDeBruijn deserialised
    where
      handleResult =
          \case
           Left e  -> error $ "Flat deserialisation failure: " ++ show e
           Right r -> return r

      fromDeBruijn :: PlcProgramNdB ann -> IO (PlcProg ann)
      fromDeBruijn prog = do
        case PLC.runQuote $
             runExceptT @PLC.FreeVariableError $ traverseOf PLC.progTerm PLC.unDeBruijnTerm prog of
          Left e  -> error $ show e
          Right p -> return p

-- | Read and deserialise a Flat-encoded UPLC AST
loadUplcASTfromFlat :: Flat ann => AstNameType -> Input -> IO (UplcProg ann)
loadUplcASTfromFlat flatMode inp = do
    input <- getBinaryInput inp
    case flatMode of
        Named -> handleResult $ unflat input
        DeBruijn -> do
            deserialised <- handleResult $ unflat input
            let namedProgram = UPLC.programMapNames fakeNameDeBruijn deserialised
            -- ^ namedProgram has names that look like `FakeNamedDeBruijn "i" ix`, where
            -- ix is the de Bruijn index.
            fromDeBruijn namedProgram
            -- ^ This converts the indices to Uniques so that we end up with proper names.
        NamedDeBruijn -> do
            deserialised <- handleResult $ unflat input
            fromDeBruijn deserialised
  where
    fromDeBruijn :: UplcProgramNdB ann -> IO (UplcProg ann)
    fromDeBruijn prog = do
      case PLC.runQuote $
           runExceptT @UPLC.FreeVariableError $ traverseOf UPLC.progTerm UPLC.unDeBruijnTerm prog of
        Left e  -> error $ show e
        Right p -> return p
    handleResult =
        \case
            Left e  -> error $ "Flat deserialisation failure: " ++ show e
            Right r -> return r

