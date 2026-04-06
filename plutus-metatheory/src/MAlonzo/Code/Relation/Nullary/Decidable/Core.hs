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

module MAlonzo.Code.Relation.Nullary.Decidable.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Relation.Nullary.Decidable.Core.Dec
d_Dec_20 a0 a1 = ()
data T_Dec_20
  = C__because__32 Bool
                   MAlonzo.Code.Relation.Nullary.Reflects.T_Reflects_16
-- Relation.Nullary.Decidable.Core.Dec.does
d_does_28 :: T_Dec_20 -> Bool
d_does_28 v0
  = case coe v0 of
      C__because__32 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Decidable.Core.Dec.proof
d_proof_30 ::
  T_Dec_20 -> MAlonzo.Code.Relation.Nullary.Reflects.T_Reflects_16
d_proof_30 v0
  = case coe v0 of
      C__because__32 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Decidable.Core._.From-yes
d_From'45'yes_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> T_Dec_20 -> ()
d_From'45'yes_50 = erased
-- Relation.Nullary.Decidable.Core._.From-no
d_From'45'no_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> T_Dec_20 -> ()
d_From'45'no_52 = erased
-- Relation.Nullary.Decidable.Core.recompute
d_recompute_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Dec_20 -> AgdaAny -> AgdaAny
d_recompute_54 ~v0 ~v1 v2 = du_recompute_54 v2
du_recompute_54 :: T_Dec_20 -> AgdaAny -> AgdaAny
du_recompute_54 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Reflects.du_recompute_46
      (coe d_proof_30 (coe v0))
-- Relation.Nullary.Decidable.Core.recompute-constant
d_recompute'45'constant_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_Dec_20 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_recompute'45'constant_62 = erased
-- Relation.Nullary.Decidable.Core.recompute-irrelevant-id
d_recompute'45'irrelevant'45'id_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_Dec_20 ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_recompute'45'irrelevant'45'id_68 = erased
-- Relation.Nullary.Decidable.Core.T?
d_T'63'_72 :: Bool -> T_Dec_20
d_T'63'_72 v0
  = coe
      C__because__32 (coe v0)
      (coe
         MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70 (coe v0))
-- Relation.Nullary.Decidable.Core.¬?
d_'172''63'_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Dec_20 -> T_Dec_20
d_'172''63'_76 ~v0 ~v1 v2 = du_'172''63'_76 v2
du_'172''63'_76 :: T_Dec_20 -> T_Dec_20
du_'172''63'_76 v0
  = coe
      C__because__32
      (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe d_does_28 (coe v0)))
      (coe
         MAlonzo.Code.Relation.Nullary.Reflects.du_'172''45'reflects_74
         (coe d_proof_30 (coe v0)))
-- Relation.Nullary.Decidable.Core.⊤-dec
d_'8868''45'dec_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_Dec_20
d_'8868''45'dec_82 ~v0 = du_'8868''45'dec_82
du_'8868''45'dec_82 :: T_Dec_20
du_'8868''45'dec_82
  = coe
      C__because__32 (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (coe
         MAlonzo.Code.Relation.Nullary.Reflects.du_'8868''45'reflects_66)
-- Relation.Nullary.Decidable.Core._×-dec_
d__'215''45'dec__84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Dec_20 -> T_Dec_20 -> T_Dec_20
d__'215''45'dec__84 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du__'215''45'dec__84 v4 v5
du__'215''45'dec__84 :: T_Dec_20 -> T_Dec_20 -> T_Dec_20
du__'215''45'dec__84 v0 v1
  = coe
      C__because__32
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8743'__24 (coe d_does_28 (coe v0))
         (coe d_does_28 (coe v1)))
      (coe
         MAlonzo.Code.Relation.Nullary.Reflects.du__'215''45'reflects__86
         (coe d_does_28 (coe v1)) (coe d_proof_30 (coe v0))
         (coe d_proof_30 (coe v1)))
-- Relation.Nullary.Decidable.Core.⊥-dec
d_'8869''45'dec_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_Dec_20
d_'8869''45'dec_94 ~v0 = du_'8869''45'dec_94
du_'8869''45'dec_94 :: T_Dec_20
du_'8869''45'dec_94
  = coe
      C__because__32 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe
         MAlonzo.Code.Relation.Nullary.Reflects.du_'8869''45'reflects_64)
-- Relation.Nullary.Decidable.Core._⊎-dec_
d__'8846''45'dec__96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Dec_20 -> T_Dec_20 -> T_Dec_20
d__'8846''45'dec__96 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du__'8846''45'dec__96 v4 v5
du__'8846''45'dec__96 :: T_Dec_20 -> T_Dec_20 -> T_Dec_20
du__'8846''45'dec__96 v0 v1
  = coe
      C__because__32
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe d_does_28 (coe v0))
         (coe d_does_28 (coe v1)))
      (coe
         MAlonzo.Code.Relation.Nullary.Reflects.du__'8846''45'reflects__102
         (coe d_does_28 (coe v1)) (coe d_proof_30 (coe v0))
         (coe d_proof_30 (coe v1)))
-- Relation.Nullary.Decidable.Core._→-dec_
d__'8594''45'dec__106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Dec_20 -> T_Dec_20 -> T_Dec_20
d__'8594''45'dec__106 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du__'8594''45'dec__106 v4 v5
du__'8594''45'dec__106 :: T_Dec_20 -> T_Dec_20 -> T_Dec_20
du__'8594''45'dec__106 v0 v1
  = coe
      C__because__32
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe d_does_28 (coe v0)))
         (coe d_does_28 (coe v1)))
      (coe
         MAlonzo.Code.Relation.Nullary.Reflects.du__'8594''45'reflects__118
         (coe d_does_28 (coe v1)) (coe d_proof_30 (coe v0))
         (coe d_proof_30 (coe v1)))
-- Relation.Nullary.Decidable.Core.dec⇒maybe
d_dec'8658'maybe_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Dec_20 -> Maybe AgdaAny
d_dec'8658'maybe_116 ~v0 ~v1 v2 = du_dec'8658'maybe_116 v2
du_dec'8658'maybe_116 :: T_Dec_20 -> Maybe AgdaAny
du_dec'8658'maybe_116 v0
  = case coe v0 of
      C__because__32 v1 v2
        -> if coe v1
             then coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38 (coe v2))
             else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Decidable.Core.toSum
d_toSum_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Dec_20 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_toSum_120 ~v0 ~v1 v2 = du_toSum_120 v2
du_toSum_120 ::
  T_Dec_20 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_toSum_120 v0
  = case coe v0 of
      C__because__32 v1 v2
        -> if coe v1
             then coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38 (coe v2))
             else coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Decidable.Core.fromSum
d_fromSum_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_Dec_20
d_fromSum_126 ~v0 ~v1 v2 = du_fromSum_126 v2
du_fromSum_126 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_Dec_20
du_fromSum_126 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe
             C__because__32 (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 (coe v1))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe
             C__because__32 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Decidable.Core.isYes
d_isYes_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> T_Dec_20 -> Bool
d_isYes_132 ~v0 ~v1 v2 = du_isYes_132 v2
du_isYes_132 :: T_Dec_20 -> Bool
du_isYes_132 v0
  = case coe v0 of
      C__because__32 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Decidable.Core.isNo
d_isNo_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> T_Dec_20 -> Bool
d_isNo_134 ~v0 ~v1 v2 = du_isNo_134 v2
du_isNo_134 :: T_Dec_20 -> Bool
du_isNo_134 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d_not_22 (coe du_isYes_132 (coe v0))
-- Relation.Nullary.Decidable.Core.True
d_True_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> T_Dec_20 -> ()
d_True_136 = erased
-- Relation.Nullary.Decidable.Core.False
d_False_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> T_Dec_20 -> ()
d_False_138 = erased
-- Relation.Nullary.Decidable.Core.⌊_⌋
d_'8970'_'8971'_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> T_Dec_20 -> Bool
d_'8970'_'8971'_140 v0 v1 v2 = coe du_isYes_132 v2
-- Relation.Nullary.Decidable.Core.toWitness
d_toWitness_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Dec_20 -> AgdaAny -> AgdaAny
d_toWitness_144 ~v0 ~v1 v2 ~v3 = du_toWitness_144 v2
du_toWitness_144 :: T_Dec_20 -> AgdaAny
du_toWitness_144 v0
  = case coe v0 of
      C__because__32 v1 v2
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Decidable.Core.fromWitness
d_fromWitness_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Dec_20 -> AgdaAny -> AgdaAny
d_fromWitness_150 ~v0 ~v1 v2 = du_fromWitness_150 v2
du_fromWitness_150 :: T_Dec_20 -> AgdaAny -> AgdaAny
du_fromWitness_150 v0
  = case coe v0 of
      C__because__32 v1 v2
        -> if coe v1
             then let v3 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8 in
                  coe (coe (\ v4 -> v3))
             else coe
                    MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Decidable.Core.toWitnessFalse
d_toWitnessFalse_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_Dec_20 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_toWitnessFalse_156 = erased
-- Relation.Nullary.Decidable.Core.fromWitnessFalse
d_fromWitnessFalse_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_Dec_20 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_fromWitnessFalse_162 ~v0 ~v1 v2 = du_fromWitnessFalse_162 v2
du_fromWitnessFalse_162 ::
  T_Dec_20 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
du_fromWitnessFalse_162 v0
  = case coe v0 of
      C__because__32 v1 v2
        -> if coe v1
             then coe
                    (\ v3 ->
                       coe
                         v3
                         (coe MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38 (coe v2)))
             else (let v3 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8 in
                   coe (coe (\ v4 -> v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Decidable.Core.from-yes
d_from'45'yes_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> T_Dec_20 -> AgdaAny
d_from'45'yes_168 ~v0 ~v1 v2 = du_from'45'yes_168 v2
du_from'45'yes_168 :: T_Dec_20 -> AgdaAny
du_from'45'yes_168 v0
  = case coe v0 of
      C__because__32 v1 v2
        -> if coe v1
             then coe
                    MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38 (coe v2)
             else coe
                    MAlonzo.Code.Level.C_lift_20
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Decidable.Core.from-no
d_from'45'no_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> T_Dec_20 -> AgdaAny
d_from'45'no_174 ~v0 ~v1 v2 = du_from'45'no_174 v2
du_from'45'no_174 :: T_Dec_20 -> AgdaAny
du_from'45'no_174 v0
  = case coe v0 of
      C__because__32 v1 v2
        -> if coe v1
             then coe
                    MAlonzo.Code.Level.C_lift_20
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             else coe
                    MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Decidable.Core.map′
d_map'8242'_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_Dec_20 -> T_Dec_20
d_map'8242'_178 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_map'8242'_178 v4 v5 v6
du_map'8242'_178 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_Dec_20 -> T_Dec_20
du_map'8242'_178 v0 v1 v2
  = coe
      C__because__32 (coe d_does_28 (coe v2))
      (case coe v2 of
         C__because__32 v3 v4
           -> if coe v3
                then coe
                       MAlonzo.Code.Relation.Nullary.Reflects.du_of_30
                       (coe d_does_28 (coe du_map'8242'_178 (coe v0) (coe v1) (coe v2)))
                       (coe
                          v0
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38 (coe v4)))
                else coe
                       MAlonzo.Code.Relation.Nullary.Reflects.du_of_30
                       (coe d_does_28 (coe du_map'8242'_178 (coe v0) (coe v1) (coe v2)))
                       (coe
                          (\ v5 ->
                             coe
                               MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38 v4
                               (coe v1 v5)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Relation.Nullary.Decidable.Core.decidable-stable
d_decidable'45'stable_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_Dec_20 ->
  ((AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_decidable'45'stable_198 ~v0 ~v1 v2 ~v3
  = du_decidable'45'stable_198 v2
du_decidable'45'stable_198 :: T_Dec_20 -> AgdaAny
du_decidable'45'stable_198 v0
  = case coe v0 of
      C__because__32 v1 v2
        -> if coe v1
             then coe
                    MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38 (coe v2)
             else coe
                    MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                    erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Decidable.Core.¬-drop-Dec
d_'172''45'drop'45'Dec_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Dec_20 -> T_Dec_20
d_'172''45'drop'45'Dec_208 ~v0 ~v1 v2
  = du_'172''45'drop'45'Dec_208 v2
du_'172''45'drop'45'Dec_208 :: T_Dec_20 -> T_Dec_20
du_'172''45'drop'45'Dec_208 v0
  = coe
      du_map'8242'_178 erased
      (\ v1 ->
         coe
           MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44)
      (coe du_'172''63'_76 (coe v0))
-- Relation.Nullary.Decidable.Core.¬¬-excluded-middle
d_'172''172''45'excluded'45'middle_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (T_Dec_20 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172''172''45'excluded'45'middle_212 = erased
-- Relation.Nullary.Decidable.Core.excluded-middle
d_excluded'45'middle_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (T_Dec_20 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_excluded'45'middle_218 = erased
-- Relation.Nullary.Decidable.Core.decToMaybe
d_decToMaybe_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Dec_20 -> Maybe AgdaAny
d_decToMaybe_220 v0 v1 v2 = coe du_dec'8658'maybe_116 v2
-- Relation.Nullary.Decidable.Core.fromDec
d_fromDec_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Dec_20 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_fromDec_222 v0 v1 v2 = coe du_toSum_120 v2
-- Relation.Nullary.Decidable.Core.toDec
d_toDec_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_Dec_20
d_toDec_224 v0 v1 v2 = coe du_fromSum_126 v2
