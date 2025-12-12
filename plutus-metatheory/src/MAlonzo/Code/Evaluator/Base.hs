{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
{-# LANGUAGE TypeApplications #-}

module MAlonzo.Code.Evaluator.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Check
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Raw
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Scoped
import qualified MAlonzo.Code.Scoped.Extrication
import qualified MAlonzo.Code.Utils

import PlutusCore.Pretty
import qualified Data.Text as T
import PlutusCore.Error
import qualified FFI.Untyped as U
import Raw
-- Evaluator.Base.ParseError
type T_ParseError_4 = PlutusCore.Error.ParserErrorBundle
d_ParseError_4
  = error
      "MAlonzo Runtime Error: postulate evaluated: Evaluator.Base.ParseError"
-- Evaluator.Base.prettyPrintTm
d_prettyPrintTm_6 ::
  MAlonzo.Code.Raw.T_RawTm_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_prettyPrintTm_6 = display @T.Text . unconv 0
-- Evaluator.Base.prettyPrintTy
d_prettyPrintTy_8 ::
  MAlonzo.Code.Raw.T_RawTy_2 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_prettyPrintTy_8 = display @T.Text . unconvT 0
-- Evaluator.Base.prettyPrintUTm
d_prettyPrintUTm_10 ::
  MAlonzo.Code.RawU.T_Untyped_208 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_prettyPrintUTm_10 = display @T.Text . U.uconv 0
-- Evaluator.Base.ERROR
d_ERROR_12 = ()
type T_ERROR_12 = ERROR
pattern C_typeError_14 a0 = TypeError a0
pattern C_parseError_16 a0 = ParseError a0
pattern C_scopeError_18 a0 = ScopeError a0
pattern C_runtimeError_20 a0 = RuntimeError a0
pattern C_jsonError_22 a0 = JsonError a0
check_typeError_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_ERROR_12
check_typeError_14 = TypeError
check_parseError_16 :: T_ParseError_4 -> T_ERROR_12
check_parseError_16 = ParseError
check_scopeError_18 ::
  MAlonzo.Code.Scoped.T_ScopeError_576 -> T_ERROR_12
check_scopeError_18 = ScopeError
check_runtimeError_20 ::
  MAlonzo.Code.Utils.T_RuntimeError_378 -> T_ERROR_12
check_runtimeError_20 = RuntimeError
check_jsonError_22 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_ERROR_12
check_jsonError_22 = JsonError
cover_ERROR_12 :: ERROR -> ()
cover_ERROR_12 x
  = case x of
      TypeError _ -> ()
      ParseError _ -> ()
      ScopeError _ -> ()
      RuntimeError _ -> ()
      JsonError _ -> ()
-- Evaluator.Base.uglyTypeError
d_uglyTypeError_24 ::
  MAlonzo.Code.Check.T_TypeError_12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyTypeError_24 v0
  = case coe v0 of
      MAlonzo.Code.Check.C_kindMismatch_18 v1 v2
        -> coe ("kindMismatch" :: Data.Text.Text)
      MAlonzo.Code.Check.C_notFunKind_26 v1
        -> coe ("NotFunKind" :: Data.Text.Text)
      MAlonzo.Code.Check.C_notPat_32 v1
        -> coe ("notPat" :: Data.Text.Text)
      MAlonzo.Code.Check.C_UnknownType_34
        -> coe ("UnknownType" :: Data.Text.Text)
      MAlonzo.Code.Check.C_notPi_44 v1 v2
        -> coe ("notPi" :: Data.Text.Text)
      MAlonzo.Code.Check.C_notMu_56 v1 v2
        -> coe ("notMu" :: Data.Text.Text)
      MAlonzo.Code.Check.C_notFunType_66 v1 v2
        -> coe ("notFunType" :: Data.Text.Text)
      MAlonzo.Code.Check.C_notSOP_76 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("notSOP" :: Data.Text.Text)
             (coe
                d_prettyPrintTy_8
                (MAlonzo.Code.Scoped.d_extricateScopeTy_780
                   (coe MAlonzo.Code.Scoped.Extrication.d_len'8902'_4 (coe v1))
                   (coe
                      MAlonzo.Code.Scoped.Extrication.d_extricateNf'8902'_26 (coe v1)
                      (coe MAlonzo.Code.Utils.C_'42'_684) (coe v2))))
      MAlonzo.Code.Check.C_IndexOutOfBounds_82 v1 v2
        -> coe ("IndexOutOfBounds" :: Data.Text.Text)
      MAlonzo.Code.Check.C_TooManyConstrArgs_84
        -> coe ("TooManyConstrArgs" :: Data.Text.Text)
      MAlonzo.Code.Check.C_TooFewConstrArgs_86
        -> coe ("TooFewConstrArgs" :: Data.Text.Text)
      MAlonzo.Code.Check.C_TooFewCases_88
        -> coe ("TooFewCases" :: Data.Text.Text)
      MAlonzo.Code.Check.C_TooManyCases_90
        -> coe ("TooManyCases" :: Data.Text.Text)
      MAlonzo.Code.Check.C_typeMismatch_100 v1 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (coe
                d_prettyPrintTy_8
                (MAlonzo.Code.Scoped.d_extricateScopeTy_780
                   (coe MAlonzo.Code.Scoped.Extrication.d_len'8902'_4 (coe v1))
                   (coe
                      MAlonzo.Code.Scoped.Extrication.d_extricateNf'8902'_26 (coe v1)
                      (coe v2) (coe v3))))
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (" doesn't match " :: Data.Text.Text)
                (coe
                   d_prettyPrintTy_8
                   (MAlonzo.Code.Scoped.d_extricateScopeTy_780
                      (coe MAlonzo.Code.Scoped.Extrication.d_len'8902'_4 (coe v1))
                      (coe
                         MAlonzo.Code.Scoped.Extrication.d_extricateNf'8902'_26 (coe v1)
                         (coe v2) (coe v4)))))
      MAlonzo.Code.Check.C_builtinError_102
        -> coe ("builtinError" :: Data.Text.Text)
      MAlonzo.Code.Check.C_Unimplemented_104 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Feature " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                (" not implemented" :: Data.Text.Text))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Evaluator.Base.reportError
d_reportError_66 ::
  T_ERROR_12 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_reportError_66 v0
  = case coe v0 of
      C_typeError_14 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("typeError: " :: Data.Text.Text) v1
      C_parseError_16 v1 -> coe ("parseError" :: Data.Text.Text)
      C_scopeError_18 v1 -> coe ("scopeError" :: Data.Text.Text)
      C_runtimeError_20 v1
        -> case coe v1 of
             MAlonzo.Code.Utils.C_gasError_380
               -> coe ("gasError" :: Data.Text.Text)
             MAlonzo.Code.Utils.C_userError_382
               -> coe ("userError" :: Data.Text.Text)
             MAlonzo.Code.Utils.C_runtimeTypeError_384
               -> coe ("runtimeTypeError" :: Data.Text.Text)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_jsonError_22 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("jsonError: " :: Data.Text.Text) v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Evaluator.Base.maxsteps
d_maxsteps_72 :: Integer
d_maxsteps_72 = coe (10000000000 :: Integer)
