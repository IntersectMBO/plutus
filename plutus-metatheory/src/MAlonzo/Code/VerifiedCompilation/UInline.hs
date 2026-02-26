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

module MAlonzo.Code.VerifiedCompilation.UInline where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Fin.Properties
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Equality
import qualified MAlonzo.Code.Untyped.RenamingSubstitution
import qualified MAlonzo.Code.VerifiedCompilation.Certificate

-- VerifiedCompilation.UInline._↝
d__'8605'_28 a0 = ()
data T__'8605'_28
  = C_'9633'_32 |
    C__'183'__34 T__'8605'_28 MAlonzo.Code.Untyped.T__'8866'_14
-- VerifiedCompilation.UInline._↑ᶻ
d__'8593''7611'_40 :: Integer -> T__'8605'_28 -> T__'8605'_28
d__'8593''7611'_40 v0 v1
  = case coe v1 of
      C_'9633'_32 -> coe v1
      C__'183'__34 v2 v3
        -> coe
             C__'183'__34 (coe d__'8593''7611'_40 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88 (coe v0)
                (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.UInline.injᶻˡ
d_inj'7611''737'_46 ::
  Integer ->
  T__'8605'_28 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T__'8605'_28 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj'7611''737'_46 = erased
-- VerifiedCompilation.UInline.injᶻʳ
d_inj'7611''691'_48 ::
  Integer ->
  T__'8605'_28 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T__'8605'_28 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj'7611''691'_48 = erased
-- VerifiedCompilation.UInline._≟ᶻ_
d__'8799''7611'__50 ::
  Integer ->
  T__'8605'_28 ->
  T__'8605'_28 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''7611'__50 v0 v1 v2
  = case coe v1 of
      C_'9633'_32
        -> case coe v2 of
             C_'9633'_32
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C__'183'__34 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'183'__34 v3 v4
        -> case coe v2 of
             C_'9633'_32
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C__'183'__34 v5 v6
               -> let v7 = d__'8799''7611'__50 (coe v0) (coe v3) (coe v5) in
                  coe
                    (let v8
                           = MAlonzo.Code.Untyped.Equality.d_decEq'45''8866'_52
                               (coe v0) (coe v4) (coe v6) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                            -> if coe v9
                                 then coe
                                        seq (coe v10)
                                        (case coe v8 of
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
                                           _ -> MAlonzo.RTE.mazUnreachableError)
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
-- VerifiedCompilation.UInline._≽_
d__'8829'__102 a0 a1 a2 = ()
data T__'8829'__102
  = C_'9633'_106 | C_keep_114 T__'8829'__102 |
    C_drop_122 T__'8829'__102
-- VerifiedCompilation.UInline._↑ᶻᶻ
d__'8593''7611''7611'_126 ::
  Integer ->
  T__'8605'_28 -> T__'8605'_28 -> T__'8829'__102 -> T__'8829'__102
d__'8593''7611''7611'_126 ~v0 v1 v2 v3
  = du__'8593''7611''7611'_126 v1 v2 v3
du__'8593''7611''7611'_126 ::
  T__'8605'_28 -> T__'8605'_28 -> T__'8829'__102 -> T__'8829'__102
du__'8593''7611''7611'_126 v0 v1 v2
  = case coe v2 of
      C_'9633'_106 -> coe v2
      C_keep_114 v6
        -> case coe v0 of
             C__'183'__34 v7 v8
               -> case coe v1 of
                    C__'183'__34 v9 v10
                      -> coe
                           C_keep_114
                           (coe du__'8593''7611''7611'_126 (coe v7) (coe v9) (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_drop_122 v6
        -> case coe v0 of
             C__'183'__34 v7 v8
               -> case coe v1 of
                    C__'183'__34 v9 v10
                      -> coe
                           C_drop_122
                           (coe du__'8593''7611''7611'_126 (coe v7) (coe v9) (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.UInline.idᶻᶻ
d_id'7611''7611'_138 :: Integer -> T__'8605'_28 -> T__'8829'__102
d_id'7611''7611'_138 ~v0 v1 = du_id'7611''7611'_138 v1
du_id'7611''7611'_138 :: T__'8605'_28 -> T__'8829'__102
du_id'7611''7611'_138 v0
  = case coe v0 of
      C_'9633'_32 -> coe C_'9633'_106
      C__'183'__34 v1 v2
        -> coe C_keep_114 (coe du_id'7611''7611'_138 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.UInline._≟ᶻᶻ_
d__'8799''7611''7611'__148 ::
  Integer ->
  T__'8605'_28 ->
  T__'8605'_28 ->
  T__'8829'__102 ->
  T__'8829'__102 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d__'8799''7611''7611'__148 v0 v1 v2 v3 v4
  = let v5 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v3 of
         C_'9633'_106
           -> case coe v4 of
                C_'9633'_106
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
                _ -> coe v5
         C_keep_114 v9
           -> case coe v1 of
                C__'183'__34 v10 v11
                  -> case coe v2 of
                       C__'183'__34 v12 v13
                         -> case coe v4 of
                              C_keep_114 v17
                                -> let v18
                                         = MAlonzo.Code.Untyped.Equality.d_decEq'45''8866'_52
                                             (coe v0) (coe v11) (coe v11) in
                                   coe
                                     (let v19
                                            = d__'8799''7611''7611'__148
                                                (coe v0) (coe v10) (coe v12) (coe v9) (coe v17) in
                                      coe
                                        (case coe v18 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                             -> case coe v20 of
                                                  MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                    -> case coe v21 of
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v22
                                                           -> case coe v19 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v23
                                                                  -> coe
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                       erased
                                                                _ -> coe
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         _ -> coe
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  _ -> coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                              _ -> coe v5
                       _ -> coe v5
                _ -> coe v5
         C_drop_122 v9
           -> case coe v1 of
                C__'183'__34 v10 v11
                  -> case coe v2 of
                       C__'183'__34 v12 v13
                         -> case coe v4 of
                              C_drop_122 v17
                                -> let v18
                                         = MAlonzo.Code.Untyped.Equality.d_decEq'45''8866'_52
                                             (coe v0) (coe v11) (coe v11) in
                                   coe
                                     (let v19
                                            = d__'8799''7611''7611'__148
                                                (coe v0) (coe v10) (coe v12) (coe v9) (coe v17) in
                                      coe
                                        (case coe v18 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                             -> case coe v20 of
                                                  MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                    -> case coe v21 of
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v22
                                                           -> case coe v19 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v23
                                                                  -> coe
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                       erased
                                                                _ -> coe
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                         _ -> coe
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  _ -> coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                              _ -> coe v5
                       _ -> coe v5
                _ -> coe v5
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UInline.Inline
d_Inline_224 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Inline_224
  = C_'96'_230 | C_'96''8595'_234 T_Inline_224 |
    C_ƛ'9633'_236 T_Inline_224 | C_ƛ_240 T_Inline_224 |
    C_ƛ'8595'_244 T_Inline_224 |
    C__'183'__250 T_Inline_224 T_Inline_224 |
    C__'183''8595'_254 T_Inline_224 | C_force_258 T_Inline_224 |
    C_delay_262 T_Inline_224 | C_con_266 | C_builtin_270 |
    C_constr_280 MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 |
    C_case_290 T_Inline_224
               MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 |
    C_error_292
-- VerifiedCompilation.UInline.checkPointwise
d_checkPointwise_304 ::
  Integer ->
  T__'8605'_28 ->
  T__'8605'_28 ->
  [MAlonzo.Code.VerifiedCompilation.Certificate.T_InlineHints_20] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  T__'8829'__102 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_Proof'63'_106
d_checkPointwise_304 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe
              MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_118
              (coe MAlonzo.Code.VerifiedCompilation.Certificate.C_inlineT_16) v6
              v7 in
    coe
      (case coe v3 of
         []
           -> case coe v6 of
                []
                  -> case coe v7 of
                       []
                         -> coe
                              MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56)
                       _ -> coe v8
                _ -> coe v8
         (:) v9 v10
           -> case coe v6 of
                (:) v11 v12
                  -> case coe v7 of
                       (:) v13 v14
                         -> coe
                              MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                              (coe
                                 d_check_316 (coe v0) (coe v1) (coe v2) (coe v9) (coe v4) (coe v5)
                                 (coe v11) (coe v13))
                              (coe
                                 (\ v15 ->
                                    coe
                                      MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                      (coe
                                         d_checkPointwise_304 (coe v0) (coe v1) (coe v2) (coe v10)
                                         (coe v4) (coe v5) (coe v12) (coe v14))
                                      (coe
                                         (\ v16 ->
                                            coe
                                              MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                              (coe
                                                 MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                                 v15 v16)))))
                       _ -> coe v8
                _ -> coe v8
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UInline.check
d_check_316 ::
  Integer ->
  T__'8605'_28 ->
  T__'8605'_28 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_InlineHints_20 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  T__'8829'__102 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_Proof'63'_106
d_check_316 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = let v8
                  = coe
                      MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_118
                      (coe MAlonzo.Code.VerifiedCompilation.Certificate.C_inlineT_16) v6
                      v7 in
            coe
              (case coe v5 of
                 C_drop_122 v12
                   -> case coe v6 of
                        MAlonzo.Code.Untyped.C_ƛ_20 v13
                          -> case coe v1 of
                               C__'183'__34 v14 v15
                                 -> case coe v2 of
                                      C__'183'__34 v16 v17
                                        -> coe
                                             MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                             (coe
                                                d_check_316
                                                (coe addInt (coe (1 :: Integer)) (coe v0))
                                                (coe d__'8593''7611'_40 (coe v0) (coe v14))
                                                (coe d__'8593''7611'_40 (coe v0) (coe v16)) (coe v3)
                                                (coe
                                                   MAlonzo.Code.Untyped.RenamingSubstitution.du_extend_454
                                                   (coe
                                                      MAlonzo.Code.Untyped.RenamingSubstitution.du__'8593''738'_470
                                                      (coe v0) (coe v4))
                                                   (coe
                                                      MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                      (coe v0) (coe v15)))
                                                (coe
                                                   du__'8593''7611''7611'_126 (coe v14) (coe v16)
                                                   (coe v12))
                                                (coe v13)
                                                (coe
                                                   MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                   (coe v0) (coe v7)))
                                             (coe
                                                (\ v18 ->
                                                   coe
                                                     MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                     (coe C_ƛ'8595'_244 v18)))
                                      _ -> coe v8
                               _ -> coe v8
                        _ -> coe v8
                 _ -> coe v8) in
    coe
      (case coe v3 of
         MAlonzo.Code.VerifiedCompilation.Certificate.C_var_22
           -> case coe v6 of
                MAlonzo.Code.Untyped.C_'96'_18 v9
                  -> case coe v7 of
                       MAlonzo.Code.Untyped.C_'96'_18 v10
                         -> let v11
                                  = coe
                                      MAlonzo.Code.Data.Fin.Properties.du__'8799'__50 (coe v9)
                                      (coe v10) in
                            coe
                              (let v12 = d__'8799''7611'__50 (coe v0) (coe v1) (coe v2) in
                               coe
                                 (case coe v11 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                      -> let v15
                                               = coe
                                                   MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_118
                                                   (coe
                                                      MAlonzo.Code.VerifiedCompilation.Certificate.C_inlineT_16)
                                                   v6 v7 in
                                         coe
                                           (case coe v13 of
                                              MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                -> case coe v14 of
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                                       -> case coe v12 of
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                              -> case coe v17 of
                                                                   MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                     -> case coe v18 of
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v19
                                                                            -> let v20
                                                                                     = d__'8799''7611''7611'__148
                                                                                         (coe v0)
                                                                                         (coe v1)
                                                                                         (coe v1)
                                                                                         (coe v5)
                                                                                         (coe
                                                                                            du_id'7611''7611'_138
                                                                                            (coe
                                                                                               v1)) in
                                                                               coe
                                                                                 (case coe v20 of
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
                                                                                      -> coe
                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                                                           (coe
                                                                                              C_'96'_230)
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                      -> coe
                                                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_118
                                                                                           (coe
                                                                                              MAlonzo.Code.VerifiedCompilation.Certificate.C_inlineT_16)
                                                                                           v6 v6
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          _ -> coe v15
                                                                   _ -> coe v15
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> coe v15
                                              _ -> coe v15)
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> coe v8
                _ -> coe v8
         MAlonzo.Code.VerifiedCompilation.Certificate.C_expand_24 v9
           -> case coe v6 of
                MAlonzo.Code.Untyped.C_'96'_18 v10
                  -> coe
                       MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                       (coe
                          d_check_316 (coe v0) (coe v1) (coe v2) (coe v9) (coe v4) (coe v5)
                          (coe v4 v10) (coe v7))
                       (coe
                          (\ v11 ->
                             coe
                               MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                               (coe C_'96''8595'_234 v11)))
                _ -> coe v8
         MAlonzo.Code.VerifiedCompilation.Certificate.C_ƛ_26 v9
           -> case coe v5 of
                C_'9633'_106
                  -> case coe v6 of
                       MAlonzo.Code.Untyped.C_ƛ_20 v10
                         -> case coe v7 of
                              MAlonzo.Code.Untyped.C_ƛ_20 v11
                                -> coe
                                     MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                     (coe
                                        d_check_316 (coe addInt (coe (1 :: Integer)) (coe v0))
                                        (coe C_'9633'_32) (coe C_'9633'_32) (coe v9)
                                        (coe
                                           MAlonzo.Code.Untyped.RenamingSubstitution.du_lifts_378
                                           (coe v0) (coe v4))
                                        (coe v5) (coe v10) (coe v11))
                                     (coe
                                        (\ v12 ->
                                           coe
                                             MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                             (coe C_ƛ'9633'_236 v12)))
                              _ -> coe v8
                       _ -> coe v8
                C_keep_114 v13
                  -> case coe v1 of
                       C__'183'__34 v14 v15
                         -> case coe v2 of
                              C__'183'__34 v16 v17
                                -> case coe v6 of
                                     MAlonzo.Code.Untyped.C_ƛ_20 v18
                                       -> case coe v7 of
                                            MAlonzo.Code.Untyped.C_ƛ_20 v19
                                              -> coe
                                                   MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                                   (coe
                                                      d_check_316
                                                      (coe addInt (coe (1 :: Integer)) (coe v0))
                                                      (coe d__'8593''7611'_40 (coe v0) (coe v14))
                                                      (coe d__'8593''7611'_40 (coe v0) (coe v16))
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Untyped.RenamingSubstitution.du_extend_454
                                                         (coe
                                                            MAlonzo.Code.Untyped.RenamingSubstitution.du__'8593''738'_470
                                                            (coe v0) (coe v4))
                                                         (coe
                                                            MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                            (coe v0) (coe v15)))
                                                      (coe
                                                         du__'8593''7611''7611'_126 (coe v14)
                                                         (coe v16) (coe v13))
                                                      (coe v18) (coe v19))
                                                   (coe
                                                      (\ v20 ->
                                                         coe
                                                           MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                           (coe C_ƛ_240 v20)))
                                            _ -> coe v8
                                     _ -> coe v8
                              _ -> coe v8
                       _ -> coe v8
                _ -> coe v8
         MAlonzo.Code.VerifiedCompilation.Certificate.C__'183'__28 v9 v10
           -> let v11
                    = case coe v6 of
                        MAlonzo.Code.Untyped.C__'183'__22 v11 v12
                          -> case coe v7 of
                               MAlonzo.Code.Untyped.C__'183'__22 v13 v14
                                 -> coe
                                      MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                      (coe
                                         d_check_316 (coe v0) (coe C__'183'__34 (coe v1) (coe v12))
                                         (coe C__'183'__34 (coe v2) (coe v12)) (coe v9) (coe v4)
                                         (coe C_keep_114 v5) (coe v11) (coe v13))
                                      (coe
                                         (\ v15 ->
                                            coe
                                              MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                              (coe
                                                 d_check_316 (coe v0) (coe C_'9633'_32)
                                                 (coe C_'9633'_32) (coe v10) (coe v4)
                                                 (coe C_'9633'_106) (coe v12) (coe v14))
                                              (coe
                                                 (\ v16 ->
                                                    coe
                                                      MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                      (coe C__'183'__250 v15 v16)))))
                               _ -> coe v8
                        _ -> coe v8 in
              coe
                (case coe v5 of
                   C_drop_122 v15
                     -> case coe v1 of
                          C__'183'__34 v16 v17
                            -> case coe v2 of
                                 C__'183'__34 v18 v19
                                   -> case coe v6 of
                                        MAlonzo.Code.Untyped.C_ƛ_20 v20
                                          -> coe
                                               MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                               (coe
                                                  d_check_316
                                                  (coe addInt (coe (1 :: Integer)) (coe v0))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v16))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v18))
                                                  (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.du_extend_454
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.du__'8593''738'_470
                                                        (coe v0) (coe v4))
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                        (coe v0) (coe v17)))
                                                  (coe
                                                     du__'8593''7611''7611'_126 (coe v16) (coe v18)
                                                     (coe v15))
                                                  (coe v20)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                     (coe v0) (coe v7)))
                                               (coe
                                                  (\ v21 ->
                                                     coe
                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                       (coe C_ƛ'8595'_244 v21)))
                                        MAlonzo.Code.Untyped.C__'183'__22 v20 v21
                                          -> case coe v7 of
                                               MAlonzo.Code.Untyped.C__'183'__22 v22 v23
                                                 -> coe
                                                      MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                                      (coe
                                                         d_check_316 (coe v0)
                                                         (coe C__'183'__34 (coe v1) (coe v21))
                                                         (coe C__'183'__34 (coe v2) (coe v21))
                                                         (coe v9) (coe v4)
                                                         (coe C_keep_114 (coe C_drop_122 v15))
                                                         (coe v20) (coe v22))
                                                      (coe
                                                         (\ v24 ->
                                                            coe
                                                              MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                                              (coe
                                                                 d_check_316 (coe v0)
                                                                 (coe C_'9633'_32) (coe C_'9633'_32)
                                                                 (coe v10) (coe v4)
                                                                 (coe C_'9633'_106) (coe v21)
                                                                 (coe v23))
                                                              (coe
                                                                 (\ v25 ->
                                                                    coe
                                                                      MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                                      (coe
                                                                         C__'183'__250 v24 v25)))))
                                               _ -> coe v8
                                        _ -> coe v8
                                 _ -> coe v11
                          _ -> coe v11
                   _ -> coe v11)
         MAlonzo.Code.VerifiedCompilation.Certificate.C__'183''8595'_30 v9
           -> let v10
                    = case coe v6 of
                        MAlonzo.Code.Untyped.C__'183'__22 v10 v11
                          -> coe
                               MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                               (coe
                                  d_check_316 (coe v0) (coe C__'183'__34 (coe v1) (coe v11))
                                  (coe C__'183'__34 (coe v2) (coe v11)) (coe v9) (coe v4)
                                  (coe C_drop_122 v5) (coe v10) (coe v7))
                               (coe
                                  (\ v12 ->
                                     coe
                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                       (coe C__'183''8595'_254 v12)))
                        _ -> coe v8 in
              coe
                (case coe v5 of
                   C_drop_122 v14
                     -> case coe v1 of
                          C__'183'__34 v15 v16
                            -> case coe v2 of
                                 C__'183'__34 v17 v18
                                   -> case coe v6 of
                                        MAlonzo.Code.Untyped.C_ƛ_20 v19
                                          -> coe
                                               MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                               (coe
                                                  d_check_316
                                                  (coe addInt (coe (1 :: Integer)) (coe v0))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v15))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v17))
                                                  (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.du_extend_454
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.du__'8593''738'_470
                                                        (coe v0) (coe v4))
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                        (coe v0) (coe v16)))
                                                  (coe
                                                     du__'8593''7611''7611'_126 (coe v15) (coe v17)
                                                     (coe v14))
                                                  (coe v19)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                     (coe v0) (coe v7)))
                                               (coe
                                                  (\ v20 ->
                                                     coe
                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                       (coe C_ƛ'8595'_244 v20)))
                                        MAlonzo.Code.Untyped.C__'183'__22 v19 v20
                                          -> coe
                                               MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                               (coe
                                                  d_check_316 (coe v0)
                                                  (coe C__'183'__34 (coe v1) (coe v20))
                                                  (coe C__'183'__34 (coe v2) (coe v20)) (coe v9)
                                                  (coe v4) (coe C_drop_122 (coe C_drop_122 v14))
                                                  (coe v19) (coe v7))
                                               (coe
                                                  (\ v21 ->
                                                     coe
                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                       (coe C__'183''8595'_254 v21)))
                                        _ -> coe v8
                                 _ -> coe v10
                          _ -> coe v10
                   _ -> coe v10)
         MAlonzo.Code.VerifiedCompilation.Certificate.C_force_32 v9
           -> let v10
                    = case coe v6 of
                        MAlonzo.Code.Untyped.C_force_24 v10
                          -> case coe v7 of
                               MAlonzo.Code.Untyped.C_force_24 v11
                                 -> coe
                                      MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                      (coe
                                         d_check_316 (coe v0) (coe C_'9633'_32) (coe C_'9633'_32)
                                         (coe v9) (coe v4) (coe C_'9633'_106) (coe v10) (coe v11))
                                      (coe
                                         (\ v12 ->
                                            coe
                                              MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                              (coe C_force_258 v12)))
                               _ -> coe v8
                        _ -> coe v8 in
              coe
                (case coe v5 of
                   C_drop_122 v14
                     -> case coe v1 of
                          C__'183'__34 v15 v16
                            -> case coe v2 of
                                 C__'183'__34 v17 v18
                                   -> case coe v6 of
                                        MAlonzo.Code.Untyped.C_ƛ_20 v19
                                          -> coe
                                               MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                               (coe
                                                  d_check_316
                                                  (coe addInt (coe (1 :: Integer)) (coe v0))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v15))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v17))
                                                  (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.du_extend_454
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.du__'8593''738'_470
                                                        (coe v0) (coe v4))
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                        (coe v0) (coe v16)))
                                                  (coe
                                                     du__'8593''7611''7611'_126 (coe v15) (coe v17)
                                                     (coe v14))
                                                  (coe v19)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                     (coe v0) (coe v7)))
                                               (coe
                                                  (\ v20 ->
                                                     coe
                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                       (coe C_ƛ'8595'_244 v20)))
                                        MAlonzo.Code.Untyped.C_force_24 v19
                                          -> case coe v7 of
                                               MAlonzo.Code.Untyped.C_force_24 v20
                                                 -> coe
                                                      MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                                      (coe
                                                         d_check_316 (coe v0) (coe C_'9633'_32)
                                                         (coe C_'9633'_32) (coe v9) (coe v4)
                                                         (coe C_'9633'_106) (coe v19) (coe v20))
                                                      (coe
                                                         (\ v21 ->
                                                            coe
                                                              MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                              (coe C_force_258 v21)))
                                               _ -> coe v8
                                        _ -> coe v8
                                 _ -> coe v10
                          _ -> coe v10
                   _ -> coe v10)
         MAlonzo.Code.VerifiedCompilation.Certificate.C_delay_34 v9
           -> let v10
                    = case coe v6 of
                        MAlonzo.Code.Untyped.C_delay_26 v10
                          -> case coe v7 of
                               MAlonzo.Code.Untyped.C_delay_26 v11
                                 -> coe
                                      MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                      (coe
                                         d_check_316 (coe v0) (coe C_'9633'_32) (coe C_'9633'_32)
                                         (coe v9) (coe v4) (coe C_'9633'_106) (coe v10) (coe v11))
                                      (coe
                                         (\ v12 ->
                                            coe
                                              MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                              (coe C_delay_262 v12)))
                               _ -> coe v8
                        _ -> coe v8 in
              coe
                (case coe v5 of
                   C_drop_122 v14
                     -> case coe v1 of
                          C__'183'__34 v15 v16
                            -> case coe v2 of
                                 C__'183'__34 v17 v18
                                   -> case coe v6 of
                                        MAlonzo.Code.Untyped.C_ƛ_20 v19
                                          -> coe
                                               MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                               (coe
                                                  d_check_316
                                                  (coe addInt (coe (1 :: Integer)) (coe v0))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v15))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v17))
                                                  (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.du_extend_454
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.du__'8593''738'_470
                                                        (coe v0) (coe v4))
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                        (coe v0) (coe v16)))
                                                  (coe
                                                     du__'8593''7611''7611'_126 (coe v15) (coe v17)
                                                     (coe v14))
                                                  (coe v19)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                     (coe v0) (coe v7)))
                                               (coe
                                                  (\ v20 ->
                                                     coe
                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                       (coe C_ƛ'8595'_244 v20)))
                                        MAlonzo.Code.Untyped.C_delay_26 v19
                                          -> case coe v7 of
                                               MAlonzo.Code.Untyped.C_delay_26 v20
                                                 -> coe
                                                      MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                                      (coe
                                                         d_check_316 (coe v0) (coe C_'9633'_32)
                                                         (coe C_'9633'_32) (coe v9) (coe v4)
                                                         (coe C_'9633'_106) (coe v19) (coe v20))
                                                      (coe
                                                         (\ v21 ->
                                                            coe
                                                              MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                              (coe C_delay_262 v21)))
                                               _ -> coe v8
                                        _ -> coe v8
                                 _ -> coe v10
                          _ -> coe v10
                   _ -> coe v10)
         MAlonzo.Code.VerifiedCompilation.Certificate.C_con_36
           -> let v9
                    = case coe v6 of
                        MAlonzo.Code.Untyped.C_con_28 v9
                          -> case coe v7 of
                               MAlonzo.Code.Untyped.C_con_28 v10
                                 -> let v11
                                          = MAlonzo.Code.Untyped.Equality.d_decEq'45'TmCon_44
                                              (coe v9) (coe v10) in
                                    coe
                                      (case coe v11 of
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                           -> if coe v12
                                                then coe
                                                       seq (coe v13)
                                                       (coe
                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                          (coe C_con_266))
                                                else coe
                                                       seq (coe v13)
                                                       (coe
                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_118
                                                          (coe
                                                             MAlonzo.Code.VerifiedCompilation.Certificate.C_inlineT_16)
                                                          v6 v7)
                                         _ -> MAlonzo.RTE.mazUnreachableError)
                               _ -> coe v8
                        _ -> coe v8 in
              coe
                (case coe v5 of
                   C_drop_122 v13
                     -> case coe v1 of
                          C__'183'__34 v14 v15
                            -> case coe v2 of
                                 C__'183'__34 v16 v17
                                   -> case coe v6 of
                                        MAlonzo.Code.Untyped.C_ƛ_20 v18
                                          -> coe
                                               MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                               (coe
                                                  d_check_316
                                                  (coe addInt (coe (1 :: Integer)) (coe v0))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v14))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v16))
                                                  (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.du_extend_454
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.du__'8593''738'_470
                                                        (coe v0) (coe v4))
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                        (coe v0) (coe v15)))
                                                  (coe
                                                     du__'8593''7611''7611'_126 (coe v14) (coe v16)
                                                     (coe v13))
                                                  (coe v18)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                     (coe v0) (coe v7)))
                                               (coe
                                                  (\ v19 ->
                                                     coe
                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                       (coe C_ƛ'8595'_244 v19)))
                                        MAlonzo.Code.Untyped.C_con_28 v18
                                          -> case coe v7 of
                                               MAlonzo.Code.Untyped.C_con_28 v19
                                                 -> let v20
                                                          = MAlonzo.Code.Untyped.Equality.d_decEq'45'TmCon_44
                                                              (coe v18) (coe v19) in
                                                    coe
                                                      (case coe v20 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                           -> if coe v21
                                                                then coe
                                                                       seq (coe v22)
                                                                       (coe
                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                                          (coe C_con_266))
                                                                else coe
                                                                       seq (coe v22)
                                                                       (coe
                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_118
                                                                          (coe
                                                                             MAlonzo.Code.VerifiedCompilation.Certificate.C_inlineT_16)
                                                                          v6 v7)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> coe v8
                                        _ -> coe v8
                                 _ -> coe v9
                          _ -> coe v9
                   _ -> coe v9)
         MAlonzo.Code.VerifiedCompilation.Certificate.C_builtin_38
           -> let v9
                    = case coe v6 of
                        MAlonzo.Code.Untyped.C_builtin_44 v9
                          -> case coe v7 of
                               MAlonzo.Code.Untyped.C_builtin_44 v10
                                 -> let v11
                                          = MAlonzo.Code.Builtin.d_decBuiltin_426
                                              (coe v9) (coe v10) in
                                    coe
                                      (case coe v11 of
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                           -> if coe v12
                                                then coe
                                                       seq (coe v13)
                                                       (coe
                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                          (coe C_builtin_270))
                                                else coe
                                                       seq (coe v13)
                                                       (coe
                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_118
                                                          (coe
                                                             MAlonzo.Code.VerifiedCompilation.Certificate.C_inlineT_16)
                                                          v6 v7)
                                         _ -> MAlonzo.RTE.mazUnreachableError)
                               _ -> coe v8
                        _ -> coe v8 in
              coe
                (case coe v5 of
                   C_drop_122 v13
                     -> case coe v1 of
                          C__'183'__34 v14 v15
                            -> case coe v2 of
                                 C__'183'__34 v16 v17
                                   -> case coe v6 of
                                        MAlonzo.Code.Untyped.C_ƛ_20 v18
                                          -> coe
                                               MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                               (coe
                                                  d_check_316
                                                  (coe addInt (coe (1 :: Integer)) (coe v0))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v14))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v16))
                                                  (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.du_extend_454
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.du__'8593''738'_470
                                                        (coe v0) (coe v4))
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                        (coe v0) (coe v15)))
                                                  (coe
                                                     du__'8593''7611''7611'_126 (coe v14) (coe v16)
                                                     (coe v13))
                                                  (coe v18)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                     (coe v0) (coe v7)))
                                               (coe
                                                  (\ v19 ->
                                                     coe
                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                       (coe C_ƛ'8595'_244 v19)))
                                        MAlonzo.Code.Untyped.C_builtin_44 v18
                                          -> case coe v7 of
                                               MAlonzo.Code.Untyped.C_builtin_44 v19
                                                 -> let v20
                                                          = MAlonzo.Code.Builtin.d_decBuiltin_426
                                                              (coe v18) (coe v19) in
                                                    coe
                                                      (case coe v20 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                           -> if coe v21
                                                                then coe
                                                                       seq (coe v22)
                                                                       (coe
                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                                          (coe C_builtin_270))
                                                                else coe
                                                                       seq (coe v22)
                                                                       (coe
                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_118
                                                                          (coe
                                                                             MAlonzo.Code.VerifiedCompilation.Certificate.C_inlineT_16)
                                                                          v6 v7)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> coe v8
                                        _ -> coe v8
                                 _ -> coe v9
                          _ -> coe v9
                   _ -> coe v9)
         MAlonzo.Code.VerifiedCompilation.Certificate.C_error_40
           -> let v9
                    = case coe v6 of
                        MAlonzo.Code.Untyped.C_error_46
                          -> case coe v7 of
                               MAlonzo.Code.Untyped.C_error_46
                                 -> coe
                                      MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                      (coe C_error_292)
                               _ -> coe v8
                        _ -> coe v8 in
              coe
                (case coe v5 of
                   C_drop_122 v13
                     -> case coe v1 of
                          C__'183'__34 v14 v15
                            -> case coe v2 of
                                 C__'183'__34 v16 v17
                                   -> case coe v6 of
                                        MAlonzo.Code.Untyped.C_ƛ_20 v18
                                          -> coe
                                               MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                               (coe
                                                  d_check_316
                                                  (coe addInt (coe (1 :: Integer)) (coe v0))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v14))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v16))
                                                  (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.du_extend_454
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.du__'8593''738'_470
                                                        (coe v0) (coe v4))
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                        (coe v0) (coe v15)))
                                                  (coe
                                                     du__'8593''7611''7611'_126 (coe v14) (coe v16)
                                                     (coe v13))
                                                  (coe v18)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                     (coe v0) (coe v7)))
                                               (coe
                                                  (\ v19 ->
                                                     coe
                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                       (coe C_ƛ'8595'_244 v19)))
                                        MAlonzo.Code.Untyped.C_error_46
                                          -> case coe v7 of
                                               MAlonzo.Code.Untyped.C_error_46
                                                 -> coe
                                                      MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                      (coe C_error_292)
                                               _ -> coe v8
                                        _ -> coe v8
                                 _ -> coe v9
                          _ -> coe v9
                   _ -> coe v9)
         MAlonzo.Code.VerifiedCompilation.Certificate.C_constr_42 v9
           -> let v10
                    = case coe v6 of
                        MAlonzo.Code.Untyped.C_constr_34 v10 v11
                          -> case coe v7 of
                               MAlonzo.Code.Untyped.C_constr_34 v12 v13
                                 -> let v14
                                          = coe
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                                              erased
                                              (\ v14 ->
                                                 coe
                                                   MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2678
                                                   (coe v10))
                                              (coe
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_66
                                                 (coe eqInt (coe v10) (coe v12))) in
                                    coe
                                      (case coe v14 of
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                           -> if coe v15
                                                then coe
                                                       seq (coe v16)
                                                       (coe
                                                          MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                                          (coe
                                                             d_checkPointwise_304 (coe v0)
                                                             (coe C_'9633'_32) (coe C_'9633'_32)
                                                             (coe v9) (coe v4) (coe C_'9633'_106)
                                                             (coe v11) (coe v13))
                                                          (coe
                                                             (\ v17 ->
                                                                coe
                                                                  MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                                  (coe C_constr_280 v17))))
                                                else coe
                                                       seq (coe v16)
                                                       (coe
                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_118
                                                          (coe
                                                             MAlonzo.Code.VerifiedCompilation.Certificate.C_inlineT_16)
                                                          v6 v7)
                                         _ -> MAlonzo.RTE.mazUnreachableError)
                               _ -> coe v8
                        _ -> coe v8 in
              coe
                (case coe v5 of
                   C_drop_122 v14
                     -> case coe v1 of
                          C__'183'__34 v15 v16
                            -> case coe v2 of
                                 C__'183'__34 v17 v18
                                   -> case coe v6 of
                                        MAlonzo.Code.Untyped.C_ƛ_20 v19
                                          -> coe
                                               MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                               (coe
                                                  d_check_316
                                                  (coe addInt (coe (1 :: Integer)) (coe v0))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v15))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v17))
                                                  (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.du_extend_454
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.du__'8593''738'_470
                                                        (coe v0) (coe v4))
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                        (coe v0) (coe v16)))
                                                  (coe
                                                     du__'8593''7611''7611'_126 (coe v15) (coe v17)
                                                     (coe v14))
                                                  (coe v19)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                     (coe v0) (coe v7)))
                                               (coe
                                                  (\ v20 ->
                                                     coe
                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                       (coe C_ƛ'8595'_244 v20)))
                                        MAlonzo.Code.Untyped.C_constr_34 v19 v20
                                          -> case coe v7 of
                                               MAlonzo.Code.Untyped.C_constr_34 v21 v22
                                                 -> let v23
                                                          = coe
                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                                                              erased
                                                              (\ v23 ->
                                                                 coe
                                                                   MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2678
                                                                   (coe v19))
                                                              (coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_66
                                                                 (coe eqInt (coe v19) (coe v21))) in
                                                    coe
                                                      (case coe v23 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                           -> if coe v24
                                                                then coe
                                                                       seq (coe v25)
                                                                       (coe
                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                                                          (coe
                                                                             d_checkPointwise_304
                                                                             (coe v0)
                                                                             (coe C_'9633'_32)
                                                                             (coe C_'9633'_32)
                                                                             (coe v9) (coe v4)
                                                                             (coe C_'9633'_106)
                                                                             (coe v20) (coe v22))
                                                                          (coe
                                                                             (\ v26 ->
                                                                                coe
                                                                                  MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                                                  (coe
                                                                                     C_constr_280
                                                                                     v26))))
                                                                else coe
                                                                       seq (coe v25)
                                                                       (coe
                                                                          MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_118
                                                                          (coe
                                                                             MAlonzo.Code.VerifiedCompilation.Certificate.C_inlineT_16)
                                                                          v6 v7)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> coe v8
                                        _ -> coe v8
                                 _ -> coe v10
                          _ -> coe v10
                   _ -> coe v10)
         MAlonzo.Code.VerifiedCompilation.Certificate.C_case_44 v9 v10
           -> let v11
                    = case coe v6 of
                        MAlonzo.Code.Untyped.C_case_40 v11 v12
                          -> case coe v7 of
                               MAlonzo.Code.Untyped.C_case_40 v13 v14
                                 -> coe
                                      MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                      (coe
                                         d_check_316 (coe v0) (coe C_'9633'_32) (coe C_'9633'_32)
                                         (coe v9) (coe v4) (coe C_'9633'_106) (coe v11) (coe v13))
                                      (coe
                                         (\ v15 ->
                                            coe
                                              MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                              (coe
                                                 d_checkPointwise_304 (coe v0) (coe C_'9633'_32)
                                                 (coe C_'9633'_32) (coe v10) (coe v4)
                                                 (coe C_'9633'_106) (coe v12) (coe v14))
                                              (coe
                                                 (\ v16 ->
                                                    coe
                                                      MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                      (coe C_case_290 v15 v16)))))
                               _ -> coe v8
                        _ -> coe v8 in
              coe
                (case coe v5 of
                   C_drop_122 v15
                     -> case coe v1 of
                          C__'183'__34 v16 v17
                            -> case coe v2 of
                                 C__'183'__34 v18 v19
                                   -> case coe v6 of
                                        MAlonzo.Code.Untyped.C_ƛ_20 v20
                                          -> coe
                                               MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                               (coe
                                                  d_check_316
                                                  (coe addInt (coe (1 :: Integer)) (coe v0))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v16))
                                                  (coe d__'8593''7611'_40 (coe v0) (coe v18))
                                                  (coe v3)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.du_extend_454
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.du__'8593''738'_470
                                                        (coe v0) (coe v4))
                                                     (coe
                                                        MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                        (coe v0) (coe v17)))
                                                  (coe
                                                     du__'8593''7611''7611'_126 (coe v16) (coe v18)
                                                     (coe v15))
                                                  (coe v20)
                                                  (coe
                                                     MAlonzo.Code.Untyped.RenamingSubstitution.d_weaken_88
                                                     (coe v0) (coe v7)))
                                               (coe
                                                  (\ v21 ->
                                                     coe
                                                       MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                       (coe C_ƛ'8595'_244 v21)))
                                        MAlonzo.Code.Untyped.C_case_40 v20 v21
                                          -> case coe v7 of
                                               MAlonzo.Code.Untyped.C_case_40 v22 v23
                                                 -> coe
                                                      MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                                      (coe
                                                         d_check_316 (coe v0) (coe C_'9633'_32)
                                                         (coe C_'9633'_32) (coe v9) (coe v4)
                                                         (coe C_'9633'_106) (coe v20) (coe v22))
                                                      (coe
                                                         (\ v24 ->
                                                            coe
                                                              MAlonzo.Code.VerifiedCompilation.Certificate.du__'62''62''61'__128
                                                              (coe
                                                                 d_checkPointwise_304 (coe v0)
                                                                 (coe C_'9633'_32) (coe C_'9633'_32)
                                                                 (coe v10) (coe v4)
                                                                 (coe C_'9633'_106) (coe v21)
                                                                 (coe v23))
                                                              (coe
                                                                 (\ v25 ->
                                                                    coe
                                                                      MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_112
                                                                      (coe C_case_290 v24 v25)))))
                                               _ -> coe v8
                                        _ -> coe v8
                                 _ -> coe v11
                          _ -> coe v11
                   _ -> coe v11)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UInline.top-check
d_top'45'check_718 ::
  MAlonzo.Code.VerifiedCompilation.Certificate.T_InlineHints_20 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_Proof'63'_106
d_top'45'check_718 v0 v1 v2
  = coe
      d_check_316 (coe (0 :: Integer)) (coe C_'9633'_32)
      (coe C_'9633'_32) (coe v0) erased (coe C_'9633'_106) (coe v1)
      (coe v2)
