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
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
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
-- VerifiedCompilation.UInline.top-check
d_top'45'check_300 ::
  MAlonzo.Code.VerifiedCompilation.Certificate.T_InlineHints_20 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_Proof'63'_106
d_top'45'check_300 ~v0 v1 v2 = du_top'45'check_300 v1 v2
du_top'45'check_300 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_Proof'63'_106
du_top'45'check_300 v0 v1
  = coe
      MAlonzo.Code.VerifiedCompilation.Certificate.C_abort_118
      (coe MAlonzo.Code.VerifiedCompilation.Certificate.C_inlineT_16) v0
      v1
