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

module MAlonzo.Code.Evaluator.Term where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Algorithmic
import qualified MAlonzo.Code.Algorithmic.CEK
import qualified MAlonzo.Code.Algorithmic.CK
import qualified MAlonzo.Code.Algorithmic.Evaluation
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Check
import qualified MAlonzo.Code.Cost
import qualified MAlonzo.Code.Cost.Model
import qualified MAlonzo.Code.Cost.Raw
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Evaluator.Base
import qualified MAlonzo.Code.Raw
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Scoped
import qualified MAlonzo.Code.Scoped.Extrication
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.CEK
import qualified MAlonzo.Code.Untyped.CEKWithCost
import qualified MAlonzo.Code.Utils

import Data.Bifunctor
import Data.Functor
import Data.Either
import Control.Monad.Trans.Except
import Raw
import PlutusCore
import PlutusCore.DeBruijn
import qualified UntypedPlutusCore as U
import qualified UntypedPlutusCore.Parser as U
import qualified FFI.Untyped as U
-- Evaluator.Term.Term
type T_Term_14 =
  PlutusCore.Term NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun ()
d_Term_14
  = error
      "MAlonzo Runtime Error: postulate evaluated: Evaluator.Term.Term"
-- Evaluator.Term.Type
type T_Type_16 = PlutusCore.Type NamedTyDeBruijn DefaultUni ()
d_Type_16
  = error
      "MAlonzo Runtime Error: postulate evaluated: Evaluator.Term.Type"
-- Evaluator.Term.TermN
type T_TermN_18 =
  PlutusCore.Term TyName Name DefaultUni DefaultFun PlutusCore.SrcSpan
d_TermN_18
  = error
      "MAlonzo Runtime Error: postulate evaluated: Evaluator.Term.TermN"
-- Evaluator.Term.TypeN
type T_TypeN_20 =
  PlutusCore.Type TyName DefaultUni PlutusCore.SrcSpan
d_TypeN_20
  = error
      "MAlonzo Runtime Error: postulate evaluated: Evaluator.Term.TypeN"
-- Evaluator.Term.TermNU
type T_TermNU_22 =
  U.Term Name DefaultUni DefaultFun PlutusCore.SrcSpan
d_TermNU_22
  = error
      "MAlonzo Runtime Error: postulate evaluated: Evaluator.Term.TermNU"
-- Evaluator.Term.TermU
type T_TermU_24 = U.Term NamedDeBruijn DefaultUni DefaultFun ()
d_TermU_24
  = error
      "MAlonzo Runtime Error: postulate evaluated: Evaluator.Term.TermU"
-- Evaluator.Term.parseTm
d_parseTm_26 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ParseError_4 T_TermN_18
d_parseTm_26 = runQuoteT . parseTerm
-- Evaluator.Term.parseTmU
d_parseTmU_28 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ParseError_4 T_TermNU_22
d_parseTmU_28 = runQuoteT . U.parseTerm
-- Evaluator.Term.parseTy
d_parseTy_30 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ParseError_4 T_TypeN_20
d_parseTy_30 = runQuoteT . parseType
-- Evaluator.Term.deBruijnifyTm
d_deBruijnifyTm_32 ::
  T_TermN_18 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_FreeVariableError_574 T_Term_14
d_deBruijnifyTm_32 = second void . runExcept . deBruijnTerm
-- Evaluator.Term.deBruijnifyTy
d_deBruijnifyTy_34 ::
  T_TypeN_20 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_FreeVariableError_574 T_Type_16
d_deBruijnifyTy_34 = second void . runExcept . deBruijnTy
-- Evaluator.Term.deBruijnifyTmU
d_deBruijnifyTmU_36 ::
  T_TermNU_22 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_FreeVariableError_574 T_TermU_24
d_deBruijnifyTmU_36 = second void . runExcept . U.deBruijnTerm
-- Evaluator.Term.convTm
d_convTm_38 :: T_Term_14 -> MAlonzo.Code.Raw.T_RawTm_32
d_convTm_38 = conv
-- Evaluator.Term.unconvTm
d_unconvTm_40 :: MAlonzo.Code.Raw.T_RawTm_32 -> T_Term_14
d_unconvTm_40 = unconv 0
-- Evaluator.Term.convTy
d_convTy_42 :: T_Type_16 -> MAlonzo.Code.Raw.T_RawTy_2
d_convTy_42 = convT
-- Evaluator.Term.unconvTy
d_unconvTy_44 :: MAlonzo.Code.Raw.T_RawTy_2 -> T_Type_16
d_unconvTy_44 = unconvT 0
-- Evaluator.Term.convTmU
d_convTmU_46 :: T_TermU_24 -> MAlonzo.Code.RawU.T_Untyped_208
d_convTmU_46 = U.conv
-- Evaluator.Term.unconvTmU
d_unconvTmU_48 :: MAlonzo.Code.RawU.T_Untyped_208 -> T_TermU_24
d_unconvTmU_48 = U.uconv 0
-- Evaluator.Term.checkKindX
checkKindAgda ::
  T_Type_16 ->
  MAlonzo.Code.Utils.T_Kind_652 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
checkKindAgda = coe d_checkKindX_50
d_checkKindX_50 ::
  T_Type_16 ->
  MAlonzo.Code.Utils.T_Kind_652 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_checkKindX_50 v0 v1
  = coe
      MAlonzo.Code.Utils.du_eitherBind_42
      (coe
         MAlonzo.Code.Utils.du_withE_282
         (coe MAlonzo.Code.Evaluator.Base.C_scopeError_18)
         (coe
            MAlonzo.Code.Scoped.d_scopeCheckTy_616
            (coe
               MAlonzo.Code.Check.d_len'8902'_106
               (coe MAlonzo.Code.Type.C_'8709'_4))
            (coe
               MAlonzo.Code.Scoped.d_shifterTy_194 (coe (0 :: Integer))
               (coe MAlonzo.Code.Scoped.C_Z_44) (coe d_convTy_42 v0))))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Utils.du_eitherBind_42
              (coe
                 MAlonzo.Code.Utils.du_withE_282
                 (coe
                    (\ v3 ->
                       coe
                         MAlonzo.Code.Evaluator.Base.C_typeError_14
                         (coe MAlonzo.Code.Evaluator.Base.d_uglyTypeError_24 (coe v3))))
                 (coe
                    MAlonzo.Code.Check.d_inferKind_562
                    (coe MAlonzo.Code.Type.C_'8709'_4) (coe v2)))
              (coe
                 (\ v3 ->
                    case coe v3 of
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                        -> coe
                             MAlonzo.Code.Utils.du_eitherBind_42
                             (coe
                                MAlonzo.Code.Utils.du_withE_282
                                (coe
                                   (\ v6 ->
                                      coe
                                        MAlonzo.Code.Evaluator.Base.C_typeError_14
                                        (coe
                                           MAlonzo.Code.Evaluator.Base.d_uglyTypeError_24
                                           (coe MAlonzo.Code.Check.C_kindMismatch_18 v1 v4))))
                                (coe
                                   MAlonzo.Code.Utils.du_dec2Either_294
                                   (coe MAlonzo.Code.Check.d_decKind_138 (coe v1) (coe v4))))
                             (coe
                                (\ v6 ->
                                   coe
                                     MAlonzo.Code.Utils.C_inj'8322'_14
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                      _ -> MAlonzo.RTE.mazUnreachableError))))
-- Evaluator.Term.inferKind∅
inferKindAgda ::
  T_Type_16 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Utils.T_Kind_652
inferKindAgda = coe d_inferKind'8709'_68
d_inferKind'8709'_68 ::
  T_Type_16 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Utils.T_Kind_652
d_inferKind'8709'_68 v0
  = coe
      MAlonzo.Code.Utils.du_eitherBind_42
      (coe
         MAlonzo.Code.Utils.du_withE_282
         (coe MAlonzo.Code.Evaluator.Base.C_scopeError_18)
         (coe
            MAlonzo.Code.Scoped.d_scopeCheckTy_616
            (coe
               MAlonzo.Code.Check.d_len'8902'_106
               (coe MAlonzo.Code.Type.C_'8709'_4))
            (coe
               MAlonzo.Code.Scoped.d_shifterTy_194 (coe (0 :: Integer))
               (coe MAlonzo.Code.Scoped.C_Z_44) (coe d_convTy_42 v0))))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.du_eitherBind_42
              (coe
                 MAlonzo.Code.Utils.du_withE_282
                 (coe
                    (\ v2 ->
                       coe
                         MAlonzo.Code.Evaluator.Base.C_typeError_14
                         (coe MAlonzo.Code.Evaluator.Base.d_uglyTypeError_24 (coe v2))))
                 (coe
                    MAlonzo.Code.Check.d_inferKind_562
                    (coe MAlonzo.Code.Type.C_'8709'_4) (coe v1)))
              (coe
                 (\ v2 ->
                    case coe v2 of
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                        -> coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe v3)
                      _ -> MAlonzo.RTE.mazUnreachableError))))
-- Evaluator.Term.normalizeType
normalizeTypeAgda ::
  T_Type_16 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12 T_Type_16
normalizeTypeAgda = coe d_normalizeType_80
d_normalizeType_80 ::
  T_Type_16 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12 T_Type_16
d_normalizeType_80 v0
  = coe
      MAlonzo.Code.Utils.du_eitherBind_42
      (coe
         MAlonzo.Code.Utils.du_withE_282
         (coe MAlonzo.Code.Evaluator.Base.C_scopeError_18)
         (coe
            MAlonzo.Code.Scoped.d_scopeCheckTy_616
            (coe
               MAlonzo.Code.Check.d_len'8902'_106
               (coe MAlonzo.Code.Type.C_'8709'_4))
            (coe
               MAlonzo.Code.Scoped.d_shifterTy_194 (coe (0 :: Integer))
               (coe MAlonzo.Code.Scoped.C_Z_44) (coe d_convTy_42 v0))))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.du_eitherBind_42
              (coe
                 MAlonzo.Code.Utils.du_withE_282
                 (coe
                    (\ v2 ->
                       coe
                         MAlonzo.Code.Evaluator.Base.C_typeError_14
                         (coe MAlonzo.Code.Evaluator.Base.d_uglyTypeError_24 (coe v2))))
                 (coe
                    MAlonzo.Code.Check.d_inferKind_562
                    (coe MAlonzo.Code.Type.C_'8709'_4) (coe v1)))
              (coe
                 (\ v2 ->
                    case coe v2 of
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                        -> coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe
                                d_unconvTy_44
                                (MAlonzo.Code.Scoped.d_unshifterTy_360
                                   (coe (0 :: Integer)) (coe MAlonzo.Code.Scoped.C_Z_44)
                                   (coe
                                      MAlonzo.Code.Scoped.d_extricateScopeTy_780
                                      (coe
                                         MAlonzo.Code.Scoped.Extrication.d_len'8902'_4
                                         (coe MAlonzo.Code.Type.C_'8709'_4))
                                      (coe
                                         MAlonzo.Code.Scoped.Extrication.d_extricateNf'8902'_26
                                         (coe MAlonzo.Code.Type.C_'8709'_4) (coe v3) (coe v4)))))
                      _ -> MAlonzo.RTE.mazUnreachableError))))
-- Evaluator.Term.inferType∅
inferTypeAgda ::
  T_Term_14 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12 T_Type_16
inferTypeAgda = coe d_inferType'8709'_92
d_inferType'8709'_92 ::
  T_Term_14 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12 T_Type_16
d_inferType'8709'_92 v0
  = coe
      MAlonzo.Code.Utils.du_eitherBind_42
      (coe
         MAlonzo.Code.Utils.du_withE_282
         (coe MAlonzo.Code.Evaluator.Base.C_scopeError_18)
         (coe
            MAlonzo.Code.Scoped.d_scopeCheckTm_686 (coe (0 :: Integer))
            (coe MAlonzo.Code.Scoped.C_Z_44)
            (coe
               MAlonzo.Code.Scoped.d_shifter_272 (coe (0 :: Integer))
               (coe MAlonzo.Code.Scoped.C_Z_44) (coe d_convTm_38 v0))))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.du_eitherBind_42
              (coe
                 MAlonzo.Code.Utils.du_withE_282
                 (coe
                    (\ v2 ->
                       coe
                         MAlonzo.Code.Evaluator.Base.C_typeError_14
                         (coe MAlonzo.Code.Evaluator.Base.d_uglyTypeError_24 (coe v2))))
                 (coe
                    MAlonzo.Code.Check.d_inferType_1156
                    (coe MAlonzo.Code.Type.C_'8709'_4)
                    (coe MAlonzo.Code.Algorithmic.C_'8709'_4) (coe v1)))
              (coe
                 (\ v2 ->
                    case coe v2 of
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                        -> coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe
                                d_unconvTy_44
                                (MAlonzo.Code.Scoped.d_unshifterTy_360
                                   (coe (0 :: Integer)) (coe MAlonzo.Code.Scoped.C_Z_44)
                                   (coe
                                      MAlonzo.Code.Scoped.d_extricateScopeTy_780
                                      (coe
                                         MAlonzo.Code.Scoped.Extrication.d_len'8902'_4
                                         (coe MAlonzo.Code.Type.C_'8709'_4))
                                      (coe
                                         MAlonzo.Code.Scoped.Extrication.d_extricateNf'8902'_26
                                         (coe MAlonzo.Code.Type.C_'8709'_4)
                                         (coe MAlonzo.Code.Utils.C_'42'_654) (coe v3)))))
                      _ -> MAlonzo.RTE.mazUnreachableError))))
-- Evaluator.Term.checkType∅
checkTypeAgda ::
  T_Type_16 ->
  T_Term_14 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
checkTypeAgda = coe d_checkType'8709'_104
d_checkType'8709'_104 ::
  T_Type_16 ->
  T_Term_14 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_checkType'8709'_104 v0 v1
  = coe
      MAlonzo.Code.Utils.du_eitherBind_42
      (coe
         MAlonzo.Code.Utils.du_withE_282
         (coe MAlonzo.Code.Evaluator.Base.C_scopeError_18)
         (coe
            MAlonzo.Code.Scoped.d_scopeCheckTy_616
            (coe
               MAlonzo.Code.Check.d_len'8902'_106
               (coe MAlonzo.Code.Type.C_'8709'_4))
            (coe
               MAlonzo.Code.Scoped.d_shifterTy_194 (coe (0 :: Integer))
               (coe MAlonzo.Code.Scoped.C_Z_44) (coe d_convTy_42 v0))))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Utils.du_eitherBind_42
              (coe
                 MAlonzo.Code.Utils.du_withE_282
                 (coe
                    (\ v3 ->
                       coe
                         MAlonzo.Code.Evaluator.Base.C_typeError_14
                         (coe MAlonzo.Code.Evaluator.Base.d_uglyTypeError_24 (coe v3))))
                 (coe
                    MAlonzo.Code.Check.d_checkKind_554
                    (coe MAlonzo.Code.Type.C_'8709'_4) (coe v2)
                    (coe MAlonzo.Code.Utils.C_'42'_654)))
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.Utils.du_eitherBind_42
                      (coe
                         MAlonzo.Code.Utils.du_withE_282
                         (coe MAlonzo.Code.Evaluator.Base.C_scopeError_18)
                         (coe
                            MAlonzo.Code.Scoped.d_scopeCheckTm_686 (coe (0 :: Integer))
                            (coe MAlonzo.Code.Scoped.C_Z_44)
                            (coe
                               MAlonzo.Code.Scoped.d_shifter_272 (coe (0 :: Integer))
                               (coe MAlonzo.Code.Scoped.C_Z_44) (coe d_convTm_38 v1))))
                      (coe
                         (\ v4 ->
                            coe
                              MAlonzo.Code.Utils.du__'62''62'__214
                              (coe MAlonzo.Code.Utils.du_EitherP_274)
                              (coe
                                 MAlonzo.Code.Utils.du_withE_282
                                 (coe
                                    (\ v5 ->
                                       coe
                                         MAlonzo.Code.Evaluator.Base.C_typeError_14
                                         (coe
                                            MAlonzo.Code.Evaluator.Base.d_uglyTypeError_24
                                            (coe v5))))
                                 (coe
                                    MAlonzo.Code.Check.d_checkType_1148
                                    (coe MAlonzo.Code.Type.C_'8709'_4)
                                    (coe MAlonzo.Code.Algorithmic.C_'8709'_4) (coe v4) (coe v3)))
                              (coe
                                 MAlonzo.Code.Utils.C_inj'8322'_14
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))))))
-- Evaluator.Term.normalizeTypeTerm
normalizeTypeTermAgda ::
  T_Term_14 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12 T_Term_14
normalizeTypeTermAgda = coe d_normalizeTypeTerm_120
d_normalizeTypeTerm_120 ::
  T_Term_14 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12 T_Term_14
d_normalizeTypeTerm_120 v0
  = coe
      MAlonzo.Code.Utils.du_eitherBind_42
      (coe
         MAlonzo.Code.Utils.du_withE_282
         (coe MAlonzo.Code.Evaluator.Base.C_scopeError_18)
         (coe
            MAlonzo.Code.Scoped.d_scopeCheckTm_686 (coe (0 :: Integer))
            (coe MAlonzo.Code.Scoped.C_Z_44)
            (coe
               MAlonzo.Code.Scoped.d_shifter_272 (coe (0 :: Integer))
               (coe MAlonzo.Code.Scoped.C_Z_44) (coe d_convTm_38 v0))))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.du_eitherBind_42
              (coe
                 MAlonzo.Code.Utils.du_withE_282
                 (coe
                    (\ v2 ->
                       coe
                         MAlonzo.Code.Evaluator.Base.C_typeError_14
                         (coe MAlonzo.Code.Evaluator.Base.d_uglyTypeError_24 (coe v2))))
                 (coe
                    MAlonzo.Code.Check.d_inferType_1156
                    (coe MAlonzo.Code.Type.C_'8709'_4)
                    (coe MAlonzo.Code.Algorithmic.C_'8709'_4) (coe v1)))
              (coe
                 (\ v2 ->
                    case coe v2 of
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                        -> coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe
                                d_unconvTm_40
                                (MAlonzo.Code.Scoped.d_unshifter_434
                                   (coe (0 :: Integer)) (coe MAlonzo.Code.Scoped.C_Z_44)
                                   (coe
                                      MAlonzo.Code.Scoped.d_extricateScope_828
                                      (coe
                                         MAlonzo.Code.Scoped.Extrication.d_len'8902'_4
                                         (coe MAlonzo.Code.Type.C_'8709'_4))
                                      (coe
                                         MAlonzo.Code.Scoped.Extrication.d_len_94
                                         (coe MAlonzo.Code.Type.C_'8709'_4)
                                         (coe MAlonzo.Code.Algorithmic.C_'8709'_4))
                                      (coe
                                         MAlonzo.Code.Scoped.Extrication.d_extricate_140
                                         (coe MAlonzo.Code.Type.C_'8709'_4)
                                         (coe MAlonzo.Code.Algorithmic.C_'8709'_4) (coe v3)
                                         (coe v4)))))
                      _ -> MAlonzo.RTE.mazUnreachableError))))
-- Evaluator.Term.runTL
runTLAgda ::
  T_Term_14 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12 T_Term_14
runTLAgda = coe d_runTL_132
d_runTL_132 ::
  T_Term_14 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12 T_Term_14
d_runTL_132 v0
  = coe
      MAlonzo.Code.Utils.du_eitherBind_42
      (coe
         MAlonzo.Code.Utils.du_withE_282
         (coe MAlonzo.Code.Evaluator.Base.C_scopeError_18)
         (coe
            MAlonzo.Code.Scoped.d_scopeCheckTm_686 (coe (0 :: Integer))
            (coe MAlonzo.Code.Scoped.C_Z_44)
            (coe
               MAlonzo.Code.Scoped.d_shifter_272 (coe (0 :: Integer))
               (coe MAlonzo.Code.Scoped.C_Z_44) (coe d_convTm_38 v0))))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.du_eitherBind_42
              (coe
                 MAlonzo.Code.Utils.du_withE_282
                 (coe
                    (\ v2 ->
                       coe
                         MAlonzo.Code.Evaluator.Base.C_typeError_14
                         (coe MAlonzo.Code.Evaluator.Base.d_uglyTypeError_24 (coe v2))))
                 (coe
                    MAlonzo.Code.Check.d_inferType_1156
                    (coe MAlonzo.Code.Type.C_'8709'_4)
                    (coe MAlonzo.Code.Algorithmic.C_'8709'_4) (coe v1)))
              (coe
                 (\ v2 ->
                    case coe v2 of
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                        -> coe
                             MAlonzo.Code.Utils.du_eitherBind_42
                             (coe
                                MAlonzo.Code.Utils.du_withE_282
                                (coe MAlonzo.Code.Evaluator.Base.C_runtimeError_20)
                                (coe
                                   MAlonzo.Code.Algorithmic.Evaluation.d_stepper_86 (coe v3)
                                   (coe v4) (coe MAlonzo.Code.Evaluator.Base.d_maxsteps_72)))
                             (coe
                                (\ v5 ->
                                   coe
                                     MAlonzo.Code.Utils.C_inj'8322'_14
                                     (coe
                                        d_unconvTm_40
                                        (MAlonzo.Code.Scoped.d_unshifter_434
                                           (coe (0 :: Integer)) (coe MAlonzo.Code.Scoped.C_Z_44)
                                           (coe
                                              MAlonzo.Code.Scoped.d_extricateScope_828
                                              (coe
                                                 MAlonzo.Code.Scoped.Extrication.d_len'8902'_4
                                                 (coe MAlonzo.Code.Type.C_'8709'_4))
                                              (coe
                                                 MAlonzo.Code.Scoped.Extrication.d_len_94
                                                 (coe MAlonzo.Code.Type.C_'8709'_4)
                                                 (coe MAlonzo.Code.Algorithmic.C_'8709'_4))
                                              (coe
                                                 MAlonzo.Code.Scoped.Extrication.d_extricate_140
                                                 (coe MAlonzo.Code.Type.C_'8709'_4)
                                                 (coe MAlonzo.Code.Algorithmic.C_'8709'_4) (coe v3)
                                                 (coe v5)))))))
                      _ -> MAlonzo.RTE.mazUnreachableError))))
-- Evaluator.Term.runTCK
runTCKAgda ::
  T_Term_14 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12 T_Term_14
runTCKAgda = coe d_runTCK_146
d_runTCK_146 ::
  T_Term_14 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12 T_Term_14
d_runTCK_146 v0
  = coe
      MAlonzo.Code.Utils.du_eitherBind_42
      (coe
         MAlonzo.Code.Utils.du_withE_282
         (coe MAlonzo.Code.Evaluator.Base.C_scopeError_18)
         (coe
            MAlonzo.Code.Scoped.d_scopeCheckTm_686 (coe (0 :: Integer))
            (coe MAlonzo.Code.Scoped.C_Z_44)
            (coe
               MAlonzo.Code.Scoped.d_shifter_272 (coe (0 :: Integer))
               (coe MAlonzo.Code.Scoped.C_Z_44) (coe d_convTm_38 v0))))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.du_eitherBind_42
              (coe
                 MAlonzo.Code.Utils.du_withE_282
                 (coe
                    (\ v2 ->
                       coe
                         MAlonzo.Code.Evaluator.Base.C_typeError_14
                         (coe MAlonzo.Code.Evaluator.Base.d_uglyTypeError_24 (coe v2))))
                 (coe
                    MAlonzo.Code.Check.d_inferType_1156
                    (coe MAlonzo.Code.Type.C_'8709'_4)
                    (coe MAlonzo.Code.Algorithmic.C_'8709'_4) (coe v1)))
              (coe
                 (\ v2 ->
                    case coe v2 of
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                        -> coe
                             MAlonzo.Code.Utils.du_eitherBind_42
                             (coe
                                MAlonzo.Code.Utils.du_withE_282
                                (coe MAlonzo.Code.Evaluator.Base.C_runtimeError_20)
                                (coe
                                   MAlonzo.Code.Algorithmic.CK.du_stepper_372
                                   (coe MAlonzo.Code.Evaluator.Base.d_maxsteps_72)
                                   (coe
                                      MAlonzo.Code.Algorithmic.CK.C__'9659'__40 (coe v3)
                                      (coe MAlonzo.Code.Algorithmic.CK.C_ε_22) (coe v4))))
                             (coe
                                (\ v5 ->
                                   case coe v5 of
                                     MAlonzo.Code.Algorithmic.CK.C__'9659'__40 v6 v7 v8
                                       -> coe
                                            MAlonzo.Code.Utils.C_inj'8321'_12
                                            (coe
                                               MAlonzo.Code.Evaluator.Base.C_runtimeError_20
                                               (coe MAlonzo.Code.Utils.C_gasError_350))
                                     MAlonzo.Code.Algorithmic.CK.C__'9669'__46 v6 v7 v8 v9
                                       -> coe
                                            MAlonzo.Code.Utils.C_inj'8321'_12
                                            (coe
                                               MAlonzo.Code.Evaluator.Base.C_runtimeError_20
                                               (coe MAlonzo.Code.Utils.C_gasError_350))
                                     MAlonzo.Code.Algorithmic.CK.C_'9633'_50 v6 v7
                                       -> coe
                                            MAlonzo.Code.Utils.C_inj'8322'_14
                                            (coe
                                               d_unconvTm_40
                                               (MAlonzo.Code.Scoped.d_unshifter_434
                                                  (coe (0 :: Integer))
                                                  (coe MAlonzo.Code.Scoped.C_Z_44)
                                                  (coe
                                                     MAlonzo.Code.Scoped.d_extricateScope_828
                                                     (coe
                                                        MAlonzo.Code.Scoped.Extrication.d_len'8902'_4
                                                        (coe MAlonzo.Code.Type.C_'8709'_4))
                                                     (coe
                                                        MAlonzo.Code.Scoped.Extrication.d_len_94
                                                        (coe MAlonzo.Code.Type.C_'8709'_4)
                                                        (coe MAlonzo.Code.Algorithmic.C_'8709'_4))
                                                     (coe
                                                        MAlonzo.Code.Scoped.Extrication.d_extricate_140
                                                        (coe MAlonzo.Code.Type.C_'8709'_4)
                                                        (coe MAlonzo.Code.Algorithmic.C_'8709'_4)
                                                        (coe v3) (coe v6)))))
                                     MAlonzo.Code.Algorithmic.CK.C_'9670'_54 v6
                                       -> coe
                                            MAlonzo.Code.Utils.C_inj'8322'_14
                                            (coe
                                               d_unconvTm_40
                                               (MAlonzo.Code.Scoped.d_unshifter_434
                                                  (coe (0 :: Integer))
                                                  (coe MAlonzo.Code.Scoped.C_Z_44)
                                                  (coe
                                                     MAlonzo.Code.Scoped.d_extricateScope_828
                                                     (coe (0 :: Integer))
                                                     (coe MAlonzo.Code.Scoped.C_Z_44)
                                                     (coe
                                                        MAlonzo.Code.Scoped.Extrication.d_extricate_140
                                                        (coe MAlonzo.Code.Type.C_'8709'_4)
                                                        (coe MAlonzo.Code.Algorithmic.C_'8709'_4)
                                                        (coe v3)
                                                        (coe
                                                           MAlonzo.Code.Algorithmic.C_error_268)))))
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                      _ -> MAlonzo.RTE.mazUnreachableError))))
-- Evaluator.Term.runTCEK
runTCEKAgda ::
  T_Term_14 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12 T_Term_14
runTCEKAgda = coe d_runTCEK_166
d_runTCEK_166 ::
  T_Term_14 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12 T_Term_14
d_runTCEK_166 v0
  = coe
      MAlonzo.Code.Utils.du_eitherBind_42
      (coe
         MAlonzo.Code.Utils.du_withE_282
         (coe MAlonzo.Code.Evaluator.Base.C_scopeError_18)
         (coe
            MAlonzo.Code.Scoped.d_scopeCheckTm_686 (coe (0 :: Integer))
            (coe MAlonzo.Code.Scoped.C_Z_44)
            (coe
               MAlonzo.Code.Scoped.d_shifter_272 (coe (0 :: Integer))
               (coe MAlonzo.Code.Scoped.C_Z_44) (coe d_convTm_38 v0))))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.du_eitherBind_42
              (coe
                 MAlonzo.Code.Utils.du_withE_282
                 (coe
                    (\ v2 ->
                       coe
                         MAlonzo.Code.Evaluator.Base.C_typeError_14
                         (coe MAlonzo.Code.Evaluator.Base.d_uglyTypeError_24 (coe v2))))
                 (coe
                    MAlonzo.Code.Check.d_inferType_1156
                    (coe MAlonzo.Code.Type.C_'8709'_4)
                    (coe MAlonzo.Code.Algorithmic.C_'8709'_4) (coe v1)))
              (coe
                 (\ v2 ->
                    case coe v2 of
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                        -> coe
                             MAlonzo.Code.Utils.du_eitherBind_42
                             (coe
                                MAlonzo.Code.Utils.du_withE_282
                                (coe MAlonzo.Code.Evaluator.Base.C_runtimeError_20)
                                (coe
                                   MAlonzo.Code.Algorithmic.CEK.du_stepper_1602
                                   (coe MAlonzo.Code.Evaluator.Base.d_maxsteps_72)
                                   (coe
                                      MAlonzo.Code.Algorithmic.CEK.C__'894'_'9659'__1258
                                      (coe MAlonzo.Code.Algorithmic.C_'8709'_4) (coe v3)
                                      (coe MAlonzo.Code.Algorithmic.CEK.C_ε_1240)
                                      (coe MAlonzo.Code.Algorithmic.CEK.C_'91''93'_202) (coe v4))))
                             (coe
                                (\ v5 ->
                                   case coe v5 of
                                     MAlonzo.Code.Algorithmic.CEK.C__'894'_'9659'__1258 v6 v7 v8 v9 v10
                                       -> coe
                                            MAlonzo.Code.Utils.C_inj'8321'_12
                                            (coe
                                               MAlonzo.Code.Evaluator.Base.C_runtimeError_20
                                               (coe MAlonzo.Code.Utils.C_gasError_350))
                                     MAlonzo.Code.Algorithmic.CEK.C__'9669'__1262 v6 v7 v8
                                       -> coe
                                            MAlonzo.Code.Utils.C_inj'8321'_12
                                            (coe
                                               MAlonzo.Code.Evaluator.Base.C_runtimeError_20
                                               (coe MAlonzo.Code.Utils.C_gasError_350))
                                     MAlonzo.Code.Algorithmic.CEK.C_'9633'_1264 v6
                                       -> coe
                                            MAlonzo.Code.Utils.C_inj'8322'_14
                                            (coe
                                               d_unconvTm_40
                                               (MAlonzo.Code.Scoped.d_unshifter_434
                                                  (coe (0 :: Integer))
                                                  (coe MAlonzo.Code.Scoped.C_Z_44)
                                                  (coe
                                                     MAlonzo.Code.Scoped.d_extricateScope_828
                                                     (coe
                                                        MAlonzo.Code.Scoped.Extrication.d_len'8902'_4
                                                        (coe MAlonzo.Code.Type.C_'8709'_4))
                                                     (coe
                                                        MAlonzo.Code.Scoped.Extrication.d_len_94
                                                        (coe MAlonzo.Code.Type.C_'8709'_4)
                                                        (coe MAlonzo.Code.Algorithmic.C_'8709'_4))
                                                     (coe
                                                        MAlonzo.Code.Scoped.Extrication.d_extricate_140
                                                        (coe MAlonzo.Code.Type.C_'8709'_4)
                                                        (coe MAlonzo.Code.Algorithmic.C_'8709'_4)
                                                        (coe v3)
                                                        (coe
                                                           MAlonzo.Code.Algorithmic.CEK.d_discharge_228
                                                           (coe v3) (coe v6))))))
                                     MAlonzo.Code.Algorithmic.CEK.C_'9670'_1266 v6
                                       -> coe
                                            MAlonzo.Code.Utils.C_inj'8322'_14
                                            (coe
                                               d_unconvTm_40
                                               (MAlonzo.Code.Scoped.d_unshifter_434
                                                  (coe (0 :: Integer))
                                                  (coe MAlonzo.Code.Scoped.C_Z_44)
                                                  (coe
                                                     MAlonzo.Code.Scoped.d_extricateScope_828
                                                     (coe (0 :: Integer))
                                                     (coe MAlonzo.Code.Scoped.C_Z_44)
                                                     (coe
                                                        MAlonzo.Code.Scoped.Extrication.d_extricate_140
                                                        (coe MAlonzo.Code.Type.C_'8709'_4)
                                                        (coe MAlonzo.Code.Algorithmic.C_'8709'_4)
                                                        (coe v3)
                                                        (coe
                                                           MAlonzo.Code.Algorithmic.C_error_268)))))
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                      _ -> MAlonzo.RTE.mazUnreachableError))))
-- Evaluator.Term.runUValue
d_runUValue_186 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Untyped.CEK.T_Value_14
d_runUValue_186 v0
  = coe
      MAlonzo.Code.Utils.du_eitherBind_42
      (coe
         MAlonzo.Code.Utils.du_withE_282
         (coe MAlonzo.Code.Evaluator.Base.C_runtimeError_20)
         (coe
            MAlonzo.Code.Untyped.CEK.d_stepper_1276
            (coe MAlonzo.Code.Evaluator.Base.d_maxsteps_72)
            (coe
               MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222
               (coe MAlonzo.Code.Untyped.CEK.C_ε_10)
               (coe MAlonzo.Code.Untyped.CEK.C_'91''93'_18) v0)))
      (coe
         (\ v1 ->
            let v2
                  = coe
                      MAlonzo.Code.Utils.C_inj'8321'_12
                      (coe
                         MAlonzo.Code.Evaluator.Base.C_runtimeError_20
                         (coe MAlonzo.Code.Utils.C_gasError_350)) in
            coe
              (case coe v1 of
                 MAlonzo.Code.Untyped.CEK.C_'9633'_226 v3
                   -> coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe v3)
                 MAlonzo.Code.Untyped.CEK.C_'9670'_228
                   -> coe
                        MAlonzo.Code.Utils.C_inj'8321'_12
                        (coe
                           MAlonzo.Code.Evaluator.Base.C_runtimeError_20
                           (coe MAlonzo.Code.Utils.C_userError_352))
                 _ -> coe v2)))
-- Evaluator.Term.runU
runUAgda ::
  T_TermU_24 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12 T_TermU_24
runUAgda = coe d_runU_194
d_runU_194 ::
  T_TermU_24 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12 T_TermU_24
d_runU_194 v0
  = coe
      MAlonzo.Code.Utils.du_eitherBind_42
      (coe
         MAlonzo.Code.Utils.du_withE_282
         (coe MAlonzo.Code.Evaluator.Base.C_scopeError_18)
         (coe
            MAlonzo.Code.Untyped.d_scopeCheckU0_326 (coe d_convTmU_46 v0)))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.du_eitherBind_42 (coe d_runUValue_186 (coe v1))
              (coe
                 (\ v2 ->
                    coe
                      MAlonzo.Code.Utils.C_inj'8322'_14
                      (coe
                         d_unconvTmU_48
                         (MAlonzo.Code.Untyped.d_extricateU0_240
                            (coe MAlonzo.Code.Untyped.CEK.d_discharge_126 (coe v2))))))))
-- Evaluator.Term.runUCounting
runUCountingAgda ::
  MAlonzo.Code.Utils.T__'215'__366
    MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
    (MAlonzo.Code.Utils.T_List_384
       (MAlonzo.Code.Utils.T__'215'__366
          MAlonzo.Code.Agda.Builtin.String.T_String_6
          MAlonzo.Code.Cost.Raw.T_CpuAndMemoryModel_190)) ->
  T_TermU_24 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    (MAlonzo.Code.Utils.T__'215'__366
       T_TermU_24 (MAlonzo.Code.Utils.T__'215'__366 Integer Integer))
runUCountingAgda = coe d_runUCounting_202
d_runUCounting_202 ::
  MAlonzo.Code.Utils.T__'215'__366
    MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
    (MAlonzo.Code.Utils.T_List_384
       (MAlonzo.Code.Utils.T__'215'__366
          MAlonzo.Code.Agda.Builtin.String.T_String_6
          MAlonzo.Code.Cost.Raw.T_CpuAndMemoryModel_190)) ->
  T_TermU_24 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    (MAlonzo.Code.Utils.T__'215'__366
       T_TermU_24 (MAlonzo.Code.Utils.T__'215'__366 Integer Integer))
d_runUCounting_202 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C__'44'__380 v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Data.Maybe.Base.du_maybe_32
                     (coe
                        (\ v4 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe MAlonzo.Code.Cost.Model.d_lookupModel_474 (coe v4))))
                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                     (coe
                        MAlonzo.Code.Cost.Model.du_allJust_510
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Cost.Model.d_getModel_432
                              (coe MAlonzo.Code.Builtin.C_addInteger_4) (coe v3))
                           (coe
                              MAlonzo.Code.Data.List.Base.du_map_22
                              (coe
                                 (\ v4 -> MAlonzo.Code.Cost.Model.d_getModel_432 (coe v4) (coe v3)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Builtin.C_subtractInteger_6)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe MAlonzo.Code.Builtin.C_multiplyInteger_8)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe MAlonzo.Code.Builtin.C_divideInteger_10)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe MAlonzo.Code.Builtin.C_quotientInteger_12)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe MAlonzo.Code.Builtin.C_remainderInteger_14)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe MAlonzo.Code.Builtin.C_modInteger_16)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe MAlonzo.Code.Builtin.C_equalsInteger_18)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Builtin.C_lessThanInteger_20)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Builtin.C_lessThanEqualsInteger_22)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Builtin.C_appendByteString_24)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Builtin.C_consByteString_26)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Builtin.C_sliceByteString_28)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Builtin.C_lengthOfByteString_30)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Builtin.C_indexByteString_32)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Builtin.C_equalsByteString_34)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Builtin.C_lessThanByteString_36)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Builtin.C_lessThanEqualsByteString_38)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Builtin.C_sha2'45'256_40)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Builtin.C_sha3'45'256_42)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Builtin.C_blake2b'45'256_44)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Builtin.C_verifyEd25519Signature_46)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                (coe
                                                                                                   MAlonzo.Code.Builtin.C_verifyEcdsaSecp256k1Signature_48)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Builtin.C_verifySchnorrSecp256k1Signature_50)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Builtin.C_appendString_52)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Builtin.C_equalsString_54)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Builtin.C_encodeUtf8_56)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Builtin.C_decodeUtf8_58)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Builtin.C_ifThenElse_60)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Builtin.C_chooseUnit_62)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Builtin.C_trace_64)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Builtin.C_fstPair_66)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Builtin.C_sndPair_68)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Builtin.C_chooseList_70)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Builtin.C_mkCons_72)
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Builtin.C_headList_74)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Builtin.C_tailList_76)
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Builtin.C_nullList_78)
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Builtin.C_lengthOfArray_80)
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                   (coe
                                                                                                                                                      MAlonzo.Code.Builtin.C_listToArray_82)
                                                                                                                                                   (coe
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Builtin.C_indexArray_84)
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Builtin.C_chooseData_86)
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Builtin.C_constrData_88)
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                               (coe
                                                                                                                                                                  MAlonzo.Code.Builtin.C_mapData_90)
                                                                                                                                                               (coe
                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.Builtin.C_listData_92)
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                     (coe
                                                                                                                                                                        MAlonzo.Code.Builtin.C_iData_94)
                                                                                                                                                                     (coe
                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.Builtin.C_bData_96)
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                           (coe
                                                                                                                                                                              MAlonzo.Code.Builtin.C_unConstrData_98)
                                                                                                                                                                           (coe
                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                              (coe
                                                                                                                                                                                 MAlonzo.Code.Builtin.C_unMapData_100)
                                                                                                                                                                              (coe
                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                 (coe
                                                                                                                                                                                    MAlonzo.Code.Builtin.C_unListData_102)
                                                                                                                                                                                 (coe
                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                    (coe
                                                                                                                                                                                       MAlonzo.Code.Builtin.C_unIData_104)
                                                                                                                                                                                    (coe
                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                       (coe
                                                                                                                                                                                          MAlonzo.Code.Builtin.C_unBData_106)
                                                                                                                                                                                       (coe
                                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                          (coe
                                                                                                                                                                                             MAlonzo.Code.Builtin.C_equalsData_108)
                                                                                                                                                                                          (coe
                                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                             (coe
                                                                                                                                                                                                MAlonzo.Code.Builtin.C_serialiseData_110)
                                                                                                                                                                                             (coe
                                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                (coe
                                                                                                                                                                                                   MAlonzo.Code.Builtin.C_mkPairData_112)
                                                                                                                                                                                                (coe
                                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                   (coe
                                                                                                                                                                                                      MAlonzo.Code.Builtin.C_mkNilData_114)
                                                                                                                                                                                                   (coe
                                                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                      (coe
                                                                                                                                                                                                         MAlonzo.Code.Builtin.C_mkNilPairData_116)
                                                                                                                                                                                                      (coe
                                                                                                                                                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                         (coe
                                                                                                                                                                                                            MAlonzo.Code.Builtin.C_bls12'45'381'45'G1'45'add_118)
                                                                                                                                                                                                         (coe
                                                                                                                                                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               MAlonzo.Code.Builtin.C_bls12'45'381'45'G1'45'neg_120)
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  MAlonzo.Code.Builtin.C_bls12'45'381'45'G1'45'scalarMul_122)
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     MAlonzo.Code.Builtin.C_bls12'45'381'45'G1'45'equal_124)
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                        MAlonzo.Code.Builtin.C_bls12'45'381'45'G1'45'hashToGroup_126)
                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                           MAlonzo.Code.Builtin.C_bls12'45'381'45'G1'45'compress_128)
                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                              MAlonzo.Code.Builtin.C_bls12'45'381'45'G1'45'uncompress_130)
                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                 MAlonzo.Code.Builtin.C_bls12'45'381'45'G2'45'add_132)
                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                    MAlonzo.Code.Builtin.C_bls12'45'381'45'G2'45'neg_134)
                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                       MAlonzo.Code.Builtin.C_bls12'45'381'45'G2'45'scalarMul_136)
                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                          MAlonzo.Code.Builtin.C_bls12'45'381'45'G2'45'equal_138)
                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                             MAlonzo.Code.Builtin.C_bls12'45'381'45'G2'45'hashToGroup_140)
                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                MAlonzo.Code.Builtin.C_bls12'45'381'45'G2'45'compress_142)
                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                                   MAlonzo.Code.Builtin.C_bls12'45'381'45'G2'45'uncompress_144)
                                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                                      MAlonzo.Code.Builtin.C_bls12'45'381'45'millerLoop_146)
                                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                                         MAlonzo.Code.Builtin.C_bls12'45'381'45'mulMlResult_148)
                                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                            MAlonzo.Code.Builtin.C_bls12'45'381'45'finalVerify_150)
                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                                                               MAlonzo.Code.Builtin.C_keccak'45'256_152)
                                                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                                  MAlonzo.Code.Builtin.C_blake2b'45'224_154)
                                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                     MAlonzo.Code.Builtin.C_byteStringToInteger_156)
                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                                        MAlonzo.Code.Builtin.C_integerToByteString_158)
                                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                                                                           MAlonzo.Code.Builtin.C_andByteString_160)
                                                                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                                                                              MAlonzo.Code.Builtin.C_orByteString_162)
                                                                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                                                 MAlonzo.Code.Builtin.C_xorByteString_164)
                                                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                                                                    MAlonzo.Code.Builtin.C_complementByteString_166)
                                                                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                                                                       MAlonzo.Code.Builtin.C_readBit_168)
                                                                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                                                                          MAlonzo.Code.Builtin.C_writeBits_170)
                                                                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                                                             MAlonzo.Code.Builtin.C_replicateByte_172)
                                                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                                                                MAlonzo.Code.Builtin.C_shiftByteString_174)
                                                                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                                                                                   MAlonzo.Code.Builtin.C_rotateByteString_176)
                                                                                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                                                                                      MAlonzo.Code.Builtin.C_countSetBits_178)
                                                                                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                                                                                         MAlonzo.Code.Builtin.C_findFirstSetBit_180)
                                                                                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                                                                            MAlonzo.Code.Builtin.C_ripemd'45'160_182)
                                                                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                                                                                                               MAlonzo.Code.Builtin.C_expModInteger_184)
                                                                                                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                                                                                  MAlonzo.Code.Builtin.C_dropList_186)
                                                                                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                                                                     MAlonzo.Code.Builtin.C_bls12'45'381'45'G1'45'multiScalarMul_188)
                                                                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                                                                                        MAlonzo.Code.Builtin.C_bls12'45'381'45'G2'45'multiScalarMul_190)
                                                                                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Utils.du_eitherBind_42
                       (coe
                          MAlonzo.Code.Utils.du_withE_282
                          (coe MAlonzo.Code.Evaluator.Base.C_scopeError_18)
                          (coe
                             MAlonzo.Code.Untyped.d_scopeCheckU0_326 (coe d_convTmU_46 v1)))
                       (coe
                          (\ v6 ->
                             coe
                               MAlonzo.Code.Utils.du_eitherBind_42
                               (coe
                                  MAlonzo.Code.Utils.du_withE_282
                                  (coe MAlonzo.Code.Evaluator.Base.C_runtimeError_20)
                                  (coe
                                     MAlonzo.Code.Utils.d_wrvalue_314
                                     (coe
                                        MAlonzo.Code.Untyped.CEKWithCost.du_stepperC_338
                                        (coe
                                           MAlonzo.Code.Cost.d_machineParameters_140
                                           (coe MAlonzo.Code.Utils.C__'44'__380 (coe v2) (coe v5)))
                                        (coe MAlonzo.Code.Evaluator.Base.d_maxsteps_72)
                                        (coe
                                           MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222
                                           (coe MAlonzo.Code.Untyped.CEK.C_ε_10)
                                           (coe MAlonzo.Code.Untyped.CEK.C_'91''93'_18) v6))))
                               (coe
                                  (\ v7 ->
                                     let v8
                                           = coe
                                               MAlonzo.Code.Utils.C_inj'8321'_12
                                               (coe
                                                  MAlonzo.Code.Evaluator.Base.C_runtimeError_20
                                                  (coe MAlonzo.Code.Utils.C_gasError_350)) in
                                     coe
                                       (case coe v7 of
                                          MAlonzo.Code.Untyped.CEK.C_'9633'_226 v9
                                            -> coe
                                                 MAlonzo.Code.Utils.C_inj'8322'_14
                                                 (coe
                                                    MAlonzo.Code.Utils.C__'44'__380
                                                    (coe
                                                       d_unconvTmU_48
                                                       (MAlonzo.Code.Untyped.d_extricateU0_240
                                                          (coe
                                                             MAlonzo.Code.Untyped.CEK.d_discharge_126
                                                             (coe v9))))
                                                    (coe
                                                       MAlonzo.Code.Utils.C__'44'__380
                                                       (coe
                                                          MAlonzo.Code.Cost.d_ExCPU_58
                                                          (coe
                                                             MAlonzo.Code.Utils.d_accum_316
                                                             (coe
                                                                MAlonzo.Code.Untyped.CEKWithCost.du_stepperC_338
                                                                (coe
                                                                   MAlonzo.Code.Cost.d_machineParameters_140
                                                                   (coe
                                                                      MAlonzo.Code.Utils.C__'44'__380
                                                                      (coe v2) (coe v5)))
                                                                (coe
                                                                   MAlonzo.Code.Evaluator.Base.d_maxsteps_72)
                                                                (coe
                                                                   MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222
                                                                   (coe
                                                                      MAlonzo.Code.Untyped.CEK.C_ε_10)
                                                                   (coe
                                                                      MAlonzo.Code.Untyped.CEK.C_'91''93'_18)
                                                                   v6))))
                                                       (coe
                                                          MAlonzo.Code.Cost.d_ExMem_60
                                                          (coe
                                                             MAlonzo.Code.Utils.d_accum_316
                                                             (coe
                                                                MAlonzo.Code.Untyped.CEKWithCost.du_stepperC_338
                                                                (coe
                                                                   MAlonzo.Code.Cost.d_machineParameters_140
                                                                   (coe
                                                                      MAlonzo.Code.Utils.C__'44'__380
                                                                      (coe v2) (coe v5)))
                                                                (coe
                                                                   MAlonzo.Code.Evaluator.Base.d_maxsteps_72)
                                                                (coe
                                                                   MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222
                                                                   (coe
                                                                      MAlonzo.Code.Untyped.CEK.C_ε_10)
                                                                   (coe
                                                                      MAlonzo.Code.Untyped.CEK.C_'91''93'_18)
                                                                   v6))))))
                                          MAlonzo.Code.Untyped.CEK.C_'9670'_228
                                            -> coe
                                                 MAlonzo.Code.Utils.C_inj'8321'_12
                                                 (coe
                                                    MAlonzo.Code.Evaluator.Base.C_runtimeError_20
                                                    (coe MAlonzo.Code.Utils.C_userError_352))
                                          _ -> coe v8)))))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Utils.C_inj'8321'_12
                       (coe
                          MAlonzo.Code.Evaluator.Base.C_jsonError_22
                          (coe ("while processing parameters." :: Data.Text.Text)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Evaluator.Term.blah
blah ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
blah = coe d_blah_240
d_blah_240 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_blah_240 v0 v1
  = let v2 = coe d_parseTm_26 v0 in
    coe
      (let v3 = coe d_parseTm_26 v1 in
       coe
         (case coe v2 of
            MAlonzo.Code.Utils.C_inj'8322'_14 v4
              -> case coe v3 of
                   MAlonzo.Code.Utils.C_inj'8322'_14 v5
                     -> let v6 = coe d_deBruijnifyTm_32 v4 in
                        coe
                          (let v7 = coe d_deBruijnifyTm_32 v5 in
                           coe
                             (case coe v6 of
                                MAlonzo.Code.Utils.C_inj'8322'_14 v8
                                  -> case coe v7 of
                                       MAlonzo.Code.Utils.C_inj'8322'_14 v9
                                         -> coe
                                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                              (MAlonzo.Code.Raw.d_rawPrinter_346
                                                 (coe d_convTm_38 v8))
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                 (" || " :: Data.Text.Text)
                                                 (MAlonzo.Code.Raw.d_rawPrinter_346
                                                    (coe d_convTm_38 v9)))
                                       _ -> coe ("deBruijnifying failed" :: Data.Text.Text)
                                _ -> coe ("deBruijnifying failed" :: Data.Text.Text)))
                   _ -> coe ("parsing failed" :: Data.Text.Text)
            _ -> coe ("parsing failed" :: Data.Text.Text)))
-- Evaluator.Term.printTy
printTy ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
printTy = coe d_printTy_286
d_printTy_286 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_printTy_286 v0
  = let v1 = coe d_parseTy_30 v0 in
    coe
      (case coe v1 of
         MAlonzo.Code.Utils.C_inj'8321'_12 v2
           -> coe ("parseTy error" :: Data.Text.Text)
         MAlonzo.Code.Utils.C_inj'8322'_14 v2
           -> let v3 = coe d_deBruijnifyTy_34 v2 in
              coe
                (case coe v3 of
                   MAlonzo.Code.Utils.C_inj'8321'_12 v4
                     -> coe ("deBruinjifyTy error" :: Data.Text.Text)
                   MAlonzo.Code.Utils.C_inj'8322'_14 v4
                     -> coe MAlonzo.Code.Raw.d_rawTyPrinter_296 (coe d_convTy_42 v4)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Evaluator.Term.alphaTy
alphaTy ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
alphaTy = coe d_alphaTy_314
d_alphaTy_314 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_alphaTy_314 v0 v1
  = let v2 = coe d_parseTy_30 v0 in
    coe
      (let v3 = coe d_parseTy_30 v1 in
       coe
         (case coe v2 of
            MAlonzo.Code.Utils.C_inj'8322'_14 v4
              -> case coe v3 of
                   MAlonzo.Code.Utils.C_inj'8322'_14 v5
                     -> let v6 = coe d_deBruijnifyTy_34 v4 in
                        coe
                          (let v7 = coe d_deBruijnifyTy_34 v5 in
                           coe
                             (case coe v6 of
                                MAlonzo.Code.Utils.C_inj'8322'_14 v8
                                  -> case coe v7 of
                                       MAlonzo.Code.Utils.C_inj'8322'_14 v9
                                         -> coe
                                              MAlonzo.Code.Raw.d_decRTy_102 (coe d_convTy_42 v8)
                                              (coe d_convTy_42 v9)
                                       _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                   _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
            _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
-- Evaluator.Term.alphaTm
alphaTm ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
alphaTm = coe d_alphaTm_360
d_alphaTm_360 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_alphaTm_360 v0 v1
  = let v2 = coe d_parseTm_26 v0 in
    coe
      (let v3 = coe d_parseTm_26 v1 in
       coe
         (case coe v2 of
            MAlonzo.Code.Utils.C_inj'8322'_14 v4
              -> case coe v3 of
                   MAlonzo.Code.Utils.C_inj'8322'_14 v5
                     -> let v6 = coe d_deBruijnifyTm_32 v4 in
                        coe
                          (let v7 = coe d_deBruijnifyTm_32 v5 in
                           coe
                             (case coe v6 of
                                MAlonzo.Code.Utils.C_inj'8322'_14 v8
                                  -> case coe v7 of
                                       MAlonzo.Code.Utils.C_inj'8322'_14 v9
                                         -> coe
                                              MAlonzo.Code.Raw.d_decRTm_188 (coe d_convTm_38 v8)
                                              (coe d_convTm_38 v9)
                                       _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                   _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
            _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
-- Evaluator.Term.alphaU
alphaU ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
alphaU = coe d_alphaU_406
d_alphaU_406 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_alphaU_406 v0 v1
  = let v2 = coe d_parseTmU_28 v0 in
    coe
      (let v3 = coe d_parseTmU_28 v1 in
       coe
         (case coe v2 of
            MAlonzo.Code.Utils.C_inj'8322'_14 v4
              -> case coe v3 of
                   MAlonzo.Code.Utils.C_inj'8322'_14 v5
                     -> let v6 = coe d_deBruijnifyTmU_36 v4 in
                        coe
                          (let v7 = coe d_deBruijnifyTmU_36 v5 in
                           coe
                             (case coe v6 of
                                MAlonzo.Code.Utils.C_inj'8322'_14 v8
                                  -> case coe v7 of
                                       MAlonzo.Code.Utils.C_inj'8322'_14 v9
                                         -> coe
                                              MAlonzo.Code.Untyped.d_decUTm_336
                                              (coe d_convTmU_46 v8) (coe d_convTmU_46 v9)
                                       _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                   _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
            _ -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
