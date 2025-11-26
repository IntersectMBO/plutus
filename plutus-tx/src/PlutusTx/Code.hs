-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module PlutusTx.Code where

import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BSL
import PlutusCore qualified as PLC
import PlutusCore.Annotation (SrcSpans)
import PlutusCore.Flat (Flat (..), unflat)
import PlutusCore.Flat.Decoder (DecodeException)
import PlutusCore.Pretty (PrettyConst, RenderContext)
import PlutusIR qualified as PIR
import PlutusTx.Coverage (CoverageIndex)
import PlutusTx.Lift.Instances ()
import UntypedPlutusCore qualified as UPLC

-- We do not use qualified import because the whole module contains off-chain code
import PlutusPrelude
import Prelude as Haskell

-- The final type parameter is inferred to be phantom, but we give it a nominal
-- role, since it corresponds to the Haskell type of the program that was compiled into
-- this 'CompiledCodeIn'. It could be okay to give it a representational role, since
-- we compile newtypes the same as their underlying types, but people probably just
-- shouldn't coerce the final parameter regardless, so we play it safe with a nominal role.
type role CompiledCodeIn representational representational nominal

-- NOTE: any changes to this type must be paralleled by changes
-- in the plugin code that generates values of this type. That is
-- done by code generation so it's not typechecked normally.

{-| A compiled Plutus Tx program. The last type parameter indicates
the type of the Haskell expression that was compiled, and
hence the type of the compiled code.

Note: the compiled PLC program does *not* have normalized types,
if you want to put it on the chain you must normalize the types first. -}
data CompiledCodeIn uni fun a
  = SerializedCode
      BS.ByteString
      -- ^ Serialized UPLC program of type 'UPLC.Program NamedDeBruijn uni fun SrcSpans'.
      (Maybe BS.ByteString)
      -- ^ Serialized PIR program of type 'PIR.Program PIR.TyName PIR.Name uni fun SrcSpans'.
      CoverageIndex
  | -- Metadata used for program coverage.
    DeserializedCode
      (UPLC.Program UPLC.NamedDeBruijn uni fun SrcSpans)
      -- ^ Deserialized UPLC program
      (Maybe (PIR.Program PLC.TyName PLC.Name uni fun SrcSpans))
      -- ^ Deserialized PIR program, if available
      CoverageIndex
      -- ^ Metadata used for program coverage.

-- | 'CompiledCodeIn' instantiated with default built-in types and functions.
type CompiledCode = CompiledCodeIn PLC.DefaultUni PLC.DefaultFun

-- | Apply a compiled function to a compiled argument. Will fail if the versions don't match.
applyCode
  :: ( PLC.Closed uni
     , uni `PLC.Everywhere` Flat
     , Flat fun
     , Pretty fun
     , PLC.Everywhere uni PrettyConst
     , PrettyBy RenderContext (PLC.SomeTypeIn uni)
     )
  => CompiledCodeIn uni fun (a -> b)
  -> CompiledCodeIn uni fun a
  -> Either String (CompiledCodeIn uni fun b)
applyCode fun arg = do
  let uplc = unsafeFromRight $ UPLC.applyProgram (getPlc fun) (getPlc arg)
  -- Probably this could be done with more appropriate combinators, but the
  -- nested Maybes make it very easy to do the wrong thing here (I did it
  -- wrong first!), so I wrote it painfully explicitly.
  pir <- case (getPir fun, getPir arg) of
    (Just funPir, Just argPir) -> case PIR.applyProgram funPir argPir of
      Right appliedPir -> pure (Just appliedPir)
      -- Had PIR for both, but failed to apply them, this should fail
      Left err -> Left $ show err
    -- Missing PIR for one or both, this succeeds but has no PIR
    (Just funPir, Nothing) ->
      Left $
        "Missing PIR for the argument."
          <> "Got PIR for the function program \n"
          <> display funPir
    (Nothing, Just argPir) ->
      Left $
        "Missing PIR for the function program."
          <> "Got PIR for the argument \n"
          <> display argPir
    (Nothing, Nothing) -> Left "Missing PIR for both the function program and the argument."

  pure $ DeserializedCode uplc pir (getCovIdx fun <> getCovIdx arg)

{-| Apply a compiled function to a compiled argument. Will throw if the versions don't match,
should only be used in non-production code. -}
unsafeApplyCode
  :: ( PLC.Closed uni
     , uni `PLC.Everywhere` Flat
     , Flat fun
     , Pretty fun
     , PLC.Everywhere uni PrettyConst
     , PrettyBy RenderContext (PLC.SomeTypeIn uni)
     )
  => CompiledCodeIn uni fun (a -> b) -> CompiledCodeIn uni fun a -> CompiledCodeIn uni fun b
unsafeApplyCode fun arg = case applyCode fun arg of
  Right c -> c
  Left err -> error err

-- | The size of a 'CompiledCodeIn' as measured in AST nodes.
countAstNodes
  :: (PLC.Closed uni, uni `PLC.Everywhere` Flat, Flat fun)
  => CompiledCodeIn uni fun a
  -> Integer
countAstNodes = UPLC.unAstSize . UPLC.programAstSize . getPlc

{- Note [Deserializing the AST]
The types suggest that we can fail to deserialize the AST that we embedded in the program.
However, we just did it ourselves, so this should be impossible, and we signal this with an
exception.
-}
newtype ImpossibleDeserialisationFailure = ImpossibleDeserialisationFailure DecodeException
  deriving anyclass (Exception)
instance Show ImpossibleDeserialisationFailure where
  show (ImpossibleDeserialisationFailure e) = "Failed to deserialise our own program! This is a bug, please report it. Caused by: " ++ show e

-- | Get the actual Plutus Core program out of a 'CompiledCodeIn'.
getPlc
  :: (PLC.Closed uni, uni `PLC.Everywhere` Flat, Flat fun)
  => CompiledCodeIn uni fun a -> UPLC.Program UPLC.NamedDeBruijn uni fun SrcSpans
getPlc wrapper = case wrapper of
  SerializedCode plc _ _ -> case unflat (BSL.fromStrict plc) of
    Left e -> throw $ ImpossibleDeserialisationFailure e
    Right (UPLC.UnrestrictedProgram p) -> p
  DeserializedCode plc _ _ -> plc

getPlcNoAnn
  :: (PLC.Closed uni, uni `PLC.Everywhere` Flat, Flat fun)
  => CompiledCodeIn uni fun a -> UPLC.Program UPLC.NamedDeBruijn uni fun ()
getPlcNoAnn = void . getPlc

-- | Get the Plutus IR program, if there is one, out of a 'CompiledCodeIn'.
getPir
  :: (PLC.Closed uni, uni `PLC.Everywhere` Flat, Flat fun)
  => CompiledCodeIn uni fun a -> Maybe (PIR.Program PIR.TyName PIR.Name uni fun SrcSpans)
getPir wrapper = case wrapper of
  SerializedCode _ pir _ -> case pir of
    Just bs -> case unflat (BSL.fromStrict bs) of
      Left e -> throw $ ImpossibleDeserialisationFailure e
      Right p -> Just p
    Nothing -> Nothing
  DeserializedCode _ pir _ -> pir

getPirNoAnn
  :: (PLC.Closed uni, uni `PLC.Everywhere` Flat, Flat fun)
  => CompiledCodeIn uni fun a -> Maybe (PIR.Program PIR.TyName PIR.Name uni fun ())
getPirNoAnn = fmap void . getPir

getCovIdx :: CompiledCodeIn uni fun a -> CoverageIndex
getCovIdx wrapper = case wrapper of
  SerializedCode _ _ idx -> idx
  DeserializedCode _ _ idx -> idx
