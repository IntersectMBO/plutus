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

module MAlonzo.Code.Untyped.Equality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Builtin.Constant.AtomicType
import qualified MAlonzo.Code.Builtin.Signature
import qualified MAlonzo.Code.Data.Bool.Properties
import qualified MAlonzo.Code.Data.Fin.Properties
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.List.Properties
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Unit.Properties
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Utils

data HasEq a = Eq a => HasEq
-- Untyped.Equality.DecEq
d_DecEq_6 a0 = ()
newtype T_DecEq_6
  = C_constructor_14 (AgdaAny ->
                      AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20)
-- Untyped.Equality.DecEq._≟_
d__'8799'__12 ::
  T_DecEq_6 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__12 v0
  = case coe v0 of
      C_constructor_14 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Equality._._≟_
d__'8799'__18 ::
  T_DecEq_6 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__18 v0 = coe d__'8799'__12 (coe v0)
-- Untyped.Equality.HasEq
type T_HasEq_20 a0 = HasEq a0
d_HasEq_20
  = error
      "MAlonzo Runtime Error: postulate evaluated: Untyped.Equality.HasEq"
-- Untyped.Equality.hasEq-TyTag
d_hasEq'45'TyTag_24
  = error
      "MAlonzo Runtime Error: postulate evaluated: Untyped.Equality.hasEq-TyTag"
-- Untyped.Equality.HsEq
d_HsEq_28 a0 = ()
newtype T_HsEq_28 = C_constructor_36 (AgdaAny -> AgdaAny -> Bool)
-- Untyped.Equality.HsEq.hsEq
d_hsEq_34 :: T_HsEq_28 -> AgdaAny -> AgdaAny -> Bool
d_hsEq_34 v0
  = case coe v0 of
      C_constructor_36 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Equality._.hsEq
d_hsEq_40 :: T_HsEq_28 -> AgdaAny -> AgdaAny -> Bool
d_hsEq_40 v0 = coe d_hsEq_34 (coe v0)
-- Untyped.Equality.eqArray
d_eqArray_46 ::
  forall xA.
    () ->
    T_HasEq_20 xA ->
    MAlonzo.Code.Utils.T_Array_602 xA ->
    MAlonzo.Code.Utils.T_Array_602 xA -> Bool
d_eqArray_46 = \ _ HasEq -> (==)
-- Untyped.Equality.decEq-TmCon
d_decEq'45'TmCon_48 ::
  MAlonzo.Code.RawU.T_TmCon_204 ->
  MAlonzo.Code.RawU.T_TmCon_204 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decEq'45'TmCon_48 v0 v1
  = case coe v0 of
      MAlonzo.Code.RawU.C_tmCon_208 v2 v3
        -> case coe v1 of
             MAlonzo.Code.RawU.C_tmCon_208 v4 v5
               -> let v6 = MAlonzo.Code.RawU.d_decTyTag_70 (coe v2) (coe v4) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe
                                     seq (coe v8)
                                     (let v9 = coe d_decEq'45''10214'_'10215'tag_52 v2 v3 v5 in
                                      coe
                                        (case coe v9 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                             -> if coe v10
                                                  then coe
                                                         seq (coe v11)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                            (coe v10)
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                               erased))
                                                  else coe
                                                         seq (coe v11)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                            (coe v10)
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                              else coe
                                     seq (coe v8)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v7)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Equality.decEq-⟦_⟧tag
d_decEq'45''10214'_'10215'tag_52 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decEq'45''10214'_'10215'tag_52 v0
  = case coe v0 of
      MAlonzo.Code.Builtin.Signature.C_'96'_8 v2
        -> coe (\ v3 v4 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Builtin.Signature.C_atomic_12 v2
        -> case coe v2 of
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
               -> coe MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBytestring_10
               -> coe du_builtinEq_488 (coe d_HsEqBytestring_428)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aString_12
               -> coe MAlonzo.Code.Data.String.Properties.d__'8799'__54
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14
               -> coe
                    (\ v3 v4 -> coe MAlonzo.Code.Data.Unit.Properties.du__'8799'__8)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16
               -> coe MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
               -> coe du_builtinEq_488 (coe d_HsEqDATA_460)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aValue_20
               -> coe du_builtinEq_488 (coe d_HsEqValue_462)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g1'45'element_22
               -> coe du_builtinEq_488 (coe d_HsEqBlsG1_454)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g2'45'element_24
               -> coe du_builtinEq_488 (coe d_HsEqBlsG2_456)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'mlresult_26
               -> coe du_builtinEq_488 (coe d_HsEqBlsMlResult_458)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Builtin.Signature.C_list_16 v2
        -> coe
             (\ v3 ->
                case coe v3 of
                  MAlonzo.Code.Utils.C_'91''93'_458
                    -> coe
                         (\ v4 ->
                            case coe v4 of
                              MAlonzo.Code.Utils.C_'91''93'_458
                                -> coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
                              MAlonzo.Code.Utils.C__'8759'__460 v5 v6
                                -> coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                     (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                              _ -> MAlonzo.RTE.mazUnreachableError)
                  MAlonzo.Code.Utils.C__'8759'__460 v4 v5
                    -> coe
                         (\ v6 ->
                            case coe v6 of
                              MAlonzo.Code.Utils.C_'91''93'_458
                                -> coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                     (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                              MAlonzo.Code.Utils.C__'8759'__460 v7 v8
                                -> let v9 = coe d_decEq'45''10214'_'10215'tag_52 v2 v4 v7 in
                                   coe
                                     (case coe v9 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                          -> if coe v10
                                               then coe
                                                      seq (coe v11)
                                                      (let v12
                                                             = coe
                                                                 d_decEq'45''10214'_'10215'tag_52
                                                                 (coe
                                                                    MAlonzo.Code.Builtin.Signature.C_list_16
                                                                    v2)
                                                                 v5 v8 in
                                                       coe
                                                         (case coe v12 of
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                              -> if coe v13
                                                                   then coe
                                                                          seq (coe v14)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                             (coe v13)
                                                                             (coe
                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                erased))
                                                                   else coe
                                                                          seq (coe v14)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                             (coe v13)
                                                                             (coe
                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                               else coe
                                                      seq (coe v11)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v10)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError)
                  _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Builtin.Signature.C_array_20 v2
        -> coe du_decEq'45'Array'45''10214'_'10215'tag_532
      MAlonzo.Code.Builtin.Signature.C_pair_24 v2 v3
        -> coe
             (\ v4 ->
                case coe v4 of
                  MAlonzo.Code.Utils.C__'44'__450 v5 v6
                    -> coe
                         (\ v7 ->
                            case coe v7 of
                              MAlonzo.Code.Utils.C__'44'__450 v8 v9
                                -> let v10
                                         = coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                                             (coe d_decEq'45''10214'_'10215'tag_52 v2 v5 v8)
                                             (coe d_decEq'45''10214'_'10215'tag_52 v3 v6 v9) in
                                   coe
                                     (case coe v10 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                          -> if coe v11
                                               then case coe v12 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                                                        -> coe
                                                             seq (coe v13)
                                                             (coe
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                (coe v11)
                                                                (coe
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                   erased))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               else coe
                                                      seq (coe v12)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v11)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError)
                  _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Equality.decEq-⊢
d_decEq'45''8866'_56 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decEq'45''8866'_56 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Untyped.C_'96'_18 v3
        -> case coe v2 of
             MAlonzo.Code.Untyped.C_'96'_18 v4
               -> let v5
                        = coe
                            MAlonzo.Code.Data.Fin.Properties.du__'8799'__50 (coe v3)
                            (coe v4) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then coe
                                     seq (coe v7)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v6)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v7)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v6)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C_ƛ_20 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C__'183'__22 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_force_24 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_delay_26 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_con_28 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_constr_34 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_case_40 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_builtin_44 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_error_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Untyped.C_ƛ_20 v3
        -> case coe v2 of
             MAlonzo.Code.Untyped.C_'96'_18 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_ƛ_20 v4
               -> let v5
                        = d_decEq'45''8866'_56
                            (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3) (coe v4) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then coe
                                     seq (coe v7)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v6)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v7)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v6)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C__'183'__22 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_force_24 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_delay_26 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_con_28 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_constr_34 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_case_40 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_builtin_44 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_error_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Untyped.C__'183'__22 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Untyped.C_'96'_18 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_ƛ_20 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C__'183'__22 v5 v6
               -> let v7
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                            (coe d__'8799'__12 (d_DecEq'45''8866'_154 (coe v0)) v3 v5)
                            (coe d__'8799'__12 (d_DecEq'45''8866'_154 (coe v0)) v4 v6) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                         -> if coe v8
                              then case coe v9 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                       -> coe
                                            seq (coe v10)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe v8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                  erased))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v9)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v8)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C_force_24 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_delay_26 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_con_28 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_constr_34 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_case_40 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_builtin_44 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_error_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Untyped.C_force_24 v3
        -> case coe v2 of
             MAlonzo.Code.Untyped.C_'96'_18 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_ƛ_20 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C__'183'__22 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_force_24 v4
               -> let v5 = d_decEq'45''8866'_56 (coe v0) (coe v3) (coe v4) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then coe
                                     seq (coe v7)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v6)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v7)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v6)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C_delay_26 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_con_28 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_constr_34 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_case_40 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_builtin_44 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_error_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Untyped.C_delay_26 v3
        -> case coe v2 of
             MAlonzo.Code.Untyped.C_'96'_18 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_ƛ_20 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C__'183'__22 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_force_24 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_delay_26 v4
               -> let v5 = d_decEq'45''8866'_56 (coe v0) (coe v3) (coe v4) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then coe
                                     seq (coe v7)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v6)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v7)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v6)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C_con_28 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_constr_34 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_case_40 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_builtin_44 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_error_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Untyped.C_con_28 v3
        -> case coe v2 of
             MAlonzo.Code.Untyped.C_'96'_18 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_ƛ_20 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C__'183'__22 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_force_24 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_delay_26 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_con_28 v4
               -> let v5 = d_decEq'45'TmCon_48 (coe v3) (coe v4) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then coe
                                     seq (coe v7)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v6)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v7)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v6)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C_constr_34 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_case_40 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_builtin_44 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_error_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Untyped.C_constr_34 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Untyped.C_'96'_18 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_ƛ_20 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C__'183'__22 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_force_24 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_delay_26 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_con_28 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_constr_34 v5 v6
               -> let v7
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                            (coe
                               MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v5))
                            (coe d_decEq'45''8866''8902'_60 (coe v0) (coe v4) (coe v6)) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                         -> if coe v8
                              then case coe v9 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                       -> coe
                                            seq (coe v10)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe v8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                  erased))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v9)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v8)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C_case_40 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_builtin_44 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_error_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Untyped.C_case_40 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Untyped.C_'96'_18 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_ƛ_20 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C__'183'__22 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_force_24 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_delay_26 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_con_28 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_constr_34 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_case_40 v5 v6
               -> let v7
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                            (coe d_decEq'45''8866'_56 (coe v0) (coe v3) (coe v5))
                            (coe d_decEq'45''8866''8902'_60 (coe v0) (coe v4) (coe v6)) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                         -> if coe v8
                              then case coe v9 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                       -> coe
                                            seq (coe v10)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe v8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                  erased))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v9)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v8)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C_builtin_44 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_error_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Untyped.C_builtin_44 v3
        -> case coe v2 of
             MAlonzo.Code.Untyped.C_'96'_18 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_ƛ_20 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C__'183'__22 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_force_24 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_delay_26 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_con_28 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_constr_34 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_case_40 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_builtin_44 v4
               -> let v5
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v5 ->
                               coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                 (coe MAlonzo.Code.Builtin.d_enumBuiltin_454 (coe v3)))
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                               (coe
                                  eqInt (coe MAlonzo.Code.Builtin.d_enumBuiltin_454 (coe v3))
                                  (coe MAlonzo.Code.Builtin.d_enumBuiltin_454 (coe v4)))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                  (coe
                                     eqInt (coe MAlonzo.Code.Builtin.d_enumBuiltin_454 (coe v3))
                                     (coe MAlonzo.Code.Builtin.d_enumBuiltin_454 (coe v4))))) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                         -> if coe v6
                              then let v8
                                         = seq
                                             (coe v7)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v6)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                   erased)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                          -> if coe v9
                                               then coe
                                                      seq (coe v10)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v9)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                            erased))
                                               else coe
                                                      seq (coe v10)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v9)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else (let v8
                                          = seq
                                              (coe v7)
                                              (coe
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                 (coe v6)
                                                 (coe
                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                    coe
                                      (case coe v8 of
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                           -> if coe v9
                                                then coe
                                                       seq (coe v10)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                          (coe v9)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                             erased))
                                                else coe
                                                       seq (coe v10)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                          (coe v9)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                         _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C_error_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Untyped.C_error_46
        -> case coe v2 of
             MAlonzo.Code.Untyped.C_'96'_18 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_ƛ_20 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C__'183'__22 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_force_24 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_delay_26 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_con_28 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_constr_34 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_case_40 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_builtin_44 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Untyped.C_error_46
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Equality.decEq-⊢⋆
d_decEq'45''8866''8902'_60 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decEq'45''8866''8902'_60 v0 v1 v2
  = case coe v1 of
      []
        -> case coe v2 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             (:) v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v3 v4
        -> case coe v2 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             (:) v5 v6
               -> let v7 = d_decEq'45''8866'_56 (coe v0) (coe v3) (coe v5) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                         -> if coe v8
                              then coe
                                     seq (coe v9)
                                     (let v10
                                            = d_decEq'45''8866''8902'_60
                                                (coe v0) (coe v4) (coe v6) in
                                      coe
                                        (case coe v10 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                             -> if coe v11
                                                  then coe
                                                         seq (coe v12)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                            (coe v11)
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                               erased))
                                                  else coe
                                                         seq (coe v12)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                            (coe v11)
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                              else coe
                                     seq (coe v9)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v8)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Equality.decPointwise
d_decPointwise_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decPointwise_72 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_decPointwise_72 v5 v6 v7
du_decPointwise_72 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_decPointwise_72 v0 v1 v2
  = case coe v1 of
      []
        -> case coe v2 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe
                          MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56))
             (:) v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v3 v4
        -> case coe v2 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             (:) v5 v6
               -> let v7 = coe v0 v3 v5 in
                  coe
                    (let v8 = coe du_decPointwise_72 (coe v0) (coe v4) (coe v6) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                            -> if coe v9
                                 then case coe v10 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                          -> case coe v8 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                 -> if coe v12
                                                      then case coe v13 of
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v14
                                                               -> coe
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                    (coe v12)
                                                                    (coe
                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                       (coe
                                                                          MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                                                          v11 v14))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      else coe
                                                             seq (coe v13)
                                                             (coe
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                (coe v12)
                                                                (coe
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v10)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                           (coe v9)
                                           (coe
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Equality.DecAtomicTyCon
d_DecAtomicTyCon_148 :: T_DecEq_6
d_DecAtomicTyCon_148
  = coe
      C_constructor_14
      (coe MAlonzo.Code.Builtin.Constant.AtomicType.d_decAtomicTyCon_28)
-- Untyped.Equality.DecEq-TmCon
d_DecEq'45'TmCon_150 :: T_DecEq_6
d_DecEq'45'TmCon_150
  = coe C_constructor_14 (coe d_decEq'45'TmCon_48)
-- Untyped.Equality.DecEq-⊢
d_DecEq'45''8866'_154 :: Integer -> T_DecEq_6
d_DecEq'45''8866'_154 v0
  = coe C_constructor_14 (coe d_decEq'45''8866'_56 (coe v0))
-- Untyped.Equality.DecEq-List
d_DecEq'45'List_160 :: () -> T_DecEq_6 -> T_DecEq_6
d_DecEq'45'List_160 ~v0 v1 = du_DecEq'45'List_160 v1
du_DecEq'45'List_160 :: T_DecEq_6 -> T_DecEq_6
du_DecEq'45'List_160 v0
  = coe
      C_constructor_14
      (coe
         MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
         (coe d__'8799'__12 (coe v0)))
-- Untyped.Equality.DecEq-Builtin
d_DecEq'45'Builtin_164 :: T_DecEq_6
d_DecEq'45'Builtin_164
  = coe C_constructor_14 (coe MAlonzo.Code.Builtin.d_decBuiltin_468)
-- Untyped.Equality.DecEq-ℕ
d_DecEq'45'ℕ_166 :: T_DecEq_6
d_DecEq'45'ℕ_166
  = coe
      C_constructor_14
      (coe MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796)
-- Untyped.Equality.DecEq-ℤ
d_DecEq'45'ℤ_168 :: T_DecEq_6
d_DecEq'45'ℤ_168
  = coe
      C_constructor_14
      (coe MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800)
-- Untyped.Equality.DecEq-Fin
d_DecEq'45'Fin_172 :: Integer -> T_DecEq_6
d_DecEq'45'Fin_172 ~v0 = du_DecEq'45'Fin_172
du_DecEq'45'Fin_172 :: T_DecEq_6
du_DecEq'45'Fin_172
  = coe
      C_constructor_14
      (coe MAlonzo.Code.Data.Fin.Properties.du__'8799'__50)
-- Untyped.Equality.DecEq-String
d_DecEq'45'String_174 :: T_DecEq_6
d_DecEq'45'String_174
  = coe
      C_constructor_14
      (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54)
-- Untyped.Equality.DecEq-Unit
d_DecEq'45'Unit_176 :: T_DecEq_6
d_DecEq'45'Unit_176
  = coe
      C_constructor_14
      (\ v0 v1 -> coe MAlonzo.Code.Data.Unit.Properties.du__'8799'__8)
-- Untyped.Equality.DecEq-Bool
d_DecEq'45'Bool_178 :: T_DecEq_6
d_DecEq'45'Bool_178
  = coe
      C_constructor_14
      (coe MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196)
-- Untyped.Equality.DecEq-TyTag
d_DecEq'45'TyTag_180 :: T_DecEq_6
d_DecEq'45'TyTag_180
  = coe C_constructor_14 (coe MAlonzo.Code.RawU.d_decTyTag_70)
-- Untyped.Equality.DecEq-⟦_⟧tag
d_DecEq'45''10214'_'10215'tag_184 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 -> T_DecEq_6
d_DecEq'45''10214'_'10215'tag_184 v0
  = coe
      C_constructor_14 (coe d_decEq'45''10214'_'10215'tag_52 (coe v0))
-- Untyped.Equality.listDec
d_listDec_190 ::
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Utils.T_List_454 AgdaAny ->
  MAlonzo.Code.Utils.T_List_454 AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_listDec_190 ~v0 v1 v2 v3 = du_listDec_190 v1 v2 v3
du_listDec_190 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Utils.T_List_454 AgdaAny ->
  MAlonzo.Code.Utils.T_List_454 AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_listDec_190 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Utils.C_'91''93'_458
        -> case coe v2 of
             MAlonzo.Code.Utils.C_'91''93'_458
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Utils.C__'8759'__460 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Utils.C__'8759'__460 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Utils.C_'91''93'_458
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Utils.C__'8759'__460 v5 v6
               -> let v7 = coe v0 v3 v5 in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                         -> if coe v8
                              then coe
                                     seq (coe v9)
                                     (let v10 = coe du_listDec_190 (coe v0) (coe v4) (coe v6) in
                                      coe
                                        (case coe v10 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                             -> if coe v11
                                                  then coe
                                                         seq (coe v12)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                            (coe v11)
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                               erased))
                                                  else coe
                                                         seq (coe v12)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                            (coe v11)
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                              else coe
                                     seq (coe v9)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v8)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Equality.pairDec
d_pairDec_270 ::
  () ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Utils.T__'215'__436 AgdaAny AgdaAny ->
  MAlonzo.Code.Utils.T__'215'__436 AgdaAny AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_pairDec_270 ~v0 ~v1 v2 v3 v4 v5 = du_pairDec_270 v2 v3 v4 v5
du_pairDec_270 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Utils.T__'215'__436 AgdaAny AgdaAny ->
  MAlonzo.Code.Utils.T__'215'__436 AgdaAny AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_pairDec_270 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Utils.C__'44'__450 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Utils.C__'44'__450 v6 v7
               -> let v8 = coe v0 v4 v6 in
                  coe
                    (let v9 = coe v1 v5 v7 in
                     coe
                       (let v10
                              = case coe v9 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                    -> coe
                                         seq (coe v10)
                                         (coe
                                            seq (coe v11)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                  _ -> MAlonzo.RTE.mazUnreachableError in
                        coe
                          (case coe v8 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                               -> let v13
                                        = case coe v9 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                              -> case coe v13 of
                                                   MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                     -> case coe v14 of
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                            -> coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v13)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                          _ -> coe v10
                                                   _ -> coe v10
                                            _ -> MAlonzo.RTE.mazUnreachableError in
                                  coe
                                    (if coe v11
                                       then case coe v12 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v14
                                                -> case coe v9 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                       -> case coe v15 of
                                                            MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                              -> case coe v16 of
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v17
                                                                     -> coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v15)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                             erased)
                                                                   _ -> coe v13
                                                            _ -> coe v13
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> coe v13
                                       else (case coe v12 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                 -> coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v11)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                               _ -> coe v13))
                             _ -> MAlonzo.RTE.mazUnreachableError)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Equality.DecEq-UList
d_DecEq'45'UList_400 :: () -> T_DecEq_6 -> T_DecEq_6
d_DecEq'45'UList_400 ~v0 v1 = du_DecEq'45'UList_400 v1
du_DecEq'45'UList_400 :: T_DecEq_6 -> T_DecEq_6
du_DecEq'45'UList_400 v0
  = coe
      C_constructor_14 (coe du_listDec_190 (coe d__'8799'__12 (coe v0)))
-- Untyped.Equality.DecEq-Pair
d_DecEq'45'Pair_412 ::
  () -> () -> T_DecEq_6 -> T_DecEq_6 -> T_DecEq_6
d_DecEq'45'Pair_412 ~v0 ~v1 v2 v3 = du_DecEq'45'Pair_412 v2 v3
du_DecEq'45'Pair_412 :: T_DecEq_6 -> T_DecEq_6 -> T_DecEq_6
du_DecEq'45'Pair_412 v0 v1
  = coe
      C_constructor_14
      (coe
         du_pairDec_270 (coe d__'8799'__12 (coe v0))
         (coe d__'8799'__12 (coe v1)))
-- Untyped.Equality.fromDec
d_fromDec_422 :: () -> T_DecEq_6 -> T_HsEq_28
d_fromDec_422 ~v0 v1 = du_fromDec_422 v1
du_fromDec_422 :: T_DecEq_6 -> T_HsEq_28
du_fromDec_422 v0
  = coe
      C_constructor_36
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
              (coe d__'8799'__12 v0 v1 v2)))
-- Untyped.Equality.HsEqBytestring
d_HsEqBytestring_428 :: T_HsEq_28
d_HsEqBytestring_428
  = coe C_constructor_36 (coe MAlonzo.Code.Utils.d_eqByteString_430)
-- Untyped.Equality.HsEqArray
d_HsEqArray_434 :: () -> T_HasEq_20 AgdaAny -> T_HsEq_28
d_HsEqArray_434 ~v0 ~v1 = du_HsEqArray_434
du_HsEqArray_434 :: T_HsEq_28
du_HsEqArray_434
  = coe
      C_constructor_36
      (coe (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10))
-- Untyped.Equality.HsEqList
d_HsEqList_442 :: () -> T_DecEq_6 -> T_HsEq_28
d_HsEqList_442 ~v0 v1 = du_HsEqList_442 v1
du_HsEqList_442 :: T_DecEq_6 -> T_HsEq_28
du_HsEqList_442 v0
  = coe du_fromDec_422 (coe du_DecEq'45'UList_400 (coe v0))
-- Untyped.Equality.HsEqPair
d_HsEqPair_452 :: () -> () -> T_DecEq_6 -> T_DecEq_6 -> T_HsEq_28
d_HsEqPair_452 ~v0 ~v1 v2 v3 = du_HsEqPair_452 v2 v3
du_HsEqPair_452 :: T_DecEq_6 -> T_DecEq_6 -> T_HsEq_28
du_HsEqPair_452 v0 v1
  = coe du_fromDec_422 (coe du_DecEq'45'Pair_412 (coe v0) (coe v1))
-- Untyped.Equality.HsEqBlsG1
d_HsEqBlsG1_454 :: T_HsEq_28
d_HsEqBlsG1_454
  = coe
      C_constructor_36
      (coe MAlonzo.Code.Utils.d_eqBls12'45'381'45'G1'45'Element_766)
-- Untyped.Equality.HsEqBlsG2
d_HsEqBlsG2_456 :: T_HsEq_28
d_HsEqBlsG2_456
  = coe
      C_constructor_36
      (coe MAlonzo.Code.Utils.d_eqBls12'45'381'45'G2'45'Element_770)
-- Untyped.Equality.HsEqBlsMlResult
d_HsEqBlsMlResult_458 :: T_HsEq_28
d_HsEqBlsMlResult_458
  = coe
      C_constructor_36
      (coe MAlonzo.Code.Utils.d_eqBls12'45'381'45'MlResult_774)
-- Untyped.Equality.HsEqDATA
d_HsEqDATA_460 :: T_HsEq_28
d_HsEqDATA_460
  = coe C_constructor_36 (coe MAlonzo.Code.Utils.d_eqDATA_630)
-- Untyped.Equality.HsEqValue
d_HsEqValue_462 :: T_HsEq_28
d_HsEqValue_462
  = coe C_constructor_36 (coe MAlonzo.Code.Utils.d_eqValue_778)
-- Untyped.Equality.HsEq-⟦_⟧tag
d_HsEq'45''10214'_'10215'tag_466 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 -> T_HsEq_28
d_HsEq'45''10214'_'10215'tag_466 v0
  = case coe v0 of
      MAlonzo.Code.Builtin.Signature.C_atomic_12 v2
        -> case coe v2 of
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
               -> coe du_fromDec_422 (coe d_DecEq'45'ℤ_168)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBytestring_10
               -> coe d_HsEqBytestring_428
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aString_12
               -> coe du_fromDec_422 (coe d_DecEq'45'String_174)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14
               -> coe du_fromDec_422 (coe d_DecEq'45'Unit_176)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16
               -> coe du_fromDec_422 (coe d_DecEq'45'Bool_178)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
               -> coe d_HsEqDATA_460
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aValue_20
               -> coe d_HsEqValue_462
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g1'45'element_22
               -> coe d_HsEqBlsG1_454
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g2'45'element_24
               -> coe d_HsEqBlsG2_456
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'mlresult_26
               -> coe d_HsEqBlsMlResult_458
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Builtin.Signature.C_list_16 v2
        -> coe
             du_HsEqList_442 (coe d_DecEq'45''10214'_'10215'tag_184 (coe v2))
      MAlonzo.Code.Builtin.Signature.C_array_20 v2
        -> coe du_HsEqArray_434
      MAlonzo.Code.Builtin.Signature.C_pair_24 v2 v3
        -> coe
             du_HsEqPair_452 (coe d_DecEq'45''10214'_'10215'tag_184 (coe v2))
             (coe d_DecEq'45''10214'_'10215'tag_184 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Equality.magicNeg
d_magicNeg_482
  = error
      "MAlonzo Runtime Error: postulate evaluated: Untyped.Equality.magicNeg"
-- Untyped.Equality.builtinEq
d_builtinEq_488 ::
  () ->
  T_HsEq_28 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_builtinEq_488 ~v0 v1 v2 v3 = du_builtinEq_488 v1 v2 v3
du_builtinEq_488 ::
  T_HsEq_28 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_builtinEq_488 v0 v1 v2
  = let v3 = coe d_hsEq_34 v0 v1 v2 in
    coe
      (if coe v3
         then coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe v3)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
         else coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe v3)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
-- Untyped.Equality.hsEqArrayHelper
d_hsEqArrayHelper_526 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 -> T_HsEq_28
d_hsEqArrayHelper_526 ~v0 = du_hsEqArrayHelper_526
du_hsEqArrayHelper_526 :: T_HsEq_28
du_hsEqArrayHelper_526 = coe du_HsEqArray_434
-- Untyped.Equality.decEq-Array-⟦_⟧tag
d_decEq'45'Array'45''10214'_'10215'tag_532 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  MAlonzo.Code.Utils.T_Array_602 AgdaAny ->
  MAlonzo.Code.Utils.T_Array_602 AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decEq'45'Array'45''10214'_'10215'tag_532 ~v0
  = du_decEq'45'Array'45''10214'_'10215'tag_532
du_decEq'45'Array'45''10214'_'10215'tag_532 ::
  MAlonzo.Code.Utils.T_Array_602 AgdaAny ->
  MAlonzo.Code.Utils.T_Array_602 AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_decEq'45'Array'45''10214'_'10215'tag_532
  = coe du_builtinEq_488 (coe du_hsEqArrayHelper_526)
