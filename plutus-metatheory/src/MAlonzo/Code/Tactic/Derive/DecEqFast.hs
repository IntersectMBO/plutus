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

module MAlonzo.Code.Tactic.Derive.DecEqFast where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Class.DecEq.Instances
import qualified MAlonzo.Code.Class.Functor.Core
import qualified MAlonzo.Code.Class.Functor.Instances
import qualified MAlonzo.Code.Class.Monad.Core
import qualified MAlonzo.Code.Class.Monad.Instances
import qualified MAlonzo.Code.Class.MonadError
import qualified MAlonzo.Code.Class.MonadTC
import qualified MAlonzo.Code.Class.Show.Core
import qualified MAlonzo.Code.Class.Show.Instances
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Meta.Prelude
import qualified MAlonzo.Code.Reflection.QQuotedDefinitions
import qualified MAlonzo.Code.Reflection.Utils.Args
import qualified MAlonzo.Code.Reflection.Utils.Core
import qualified MAlonzo.Code.Reflection.Utils.Debug
import qualified MAlonzo.Code.Reflection.Utils.Substitute
import qualified MAlonzo.Code.Reflection.Utils.TCI

-- Tactic.Derive.DecEqFast.allPairs
d_allPairs_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_allPairs_26 ~v0 ~v1 v2 = du_allPairs_26 v2
du_allPairs_26 ::
  [AgdaAny] -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_allPairs_26 v0
  = coe MAlonzo.Code.Data.List.Base.du_cartesianProduct_82 v0 v0
-- Tactic.Derive.DecEqFast.`λ∅∅
d_'96'λ'8709''8709'_30 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_'96'λ'8709''8709'_30
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Reflection.C_absurd'45'clause_278
            (coe
               MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe ("()" :: Data.Text.Text))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                     (coe
                        MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                        (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                           (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                           (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                     (coe MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216))))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                  (coe
                     MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                     (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                        (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                        (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Reflection.C_absurd_264
                     (coe (0 :: Integer))))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Tactic.Derive.DecEqFast._.mkPattern
d_mkPattern_38 :: Integer -> AgdaAny -> AgdaAny
d_mkPattern_38 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () () erased
      erased
      (coe
         MAlonzo.Code.Class.Monad.Core.du__'61''60''60'__32
         (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6) (coe ())
         (coe ()) (coe MAlonzo.Code.Agda.Builtin.Reflection.d_reduce_352)
         (coe MAlonzo.Code.Agda.Builtin.Reflection.d_getType_406 v1))
      (\ v2 ->
         coe
           MAlonzo.Code.Agda.Builtin.Reflection.d_returnTC_326 () erased
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Data.List.Base.du_drop_542 (coe v0)
                 (coe MAlonzo.Code.Reflection.Utils.Core.d_argTys_68 (coe v2)))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                 (coe
                    MAlonzo.Code.Data.List.Base.du_length_268
                    (coe
                       MAlonzo.Code.Data.List.Base.du_drop_542 (coe v0)
                       (coe MAlonzo.Code.Reflection.Utils.Core.d_argTys_68 (coe v2))))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Meta.Prelude.du_enumerate_44
                       (coe
                          MAlonzo.Code.Data.List.Base.du_drop_542 (coe v0)
                          (coe MAlonzo.Code.Reflection.Utils.Core.d_argTys_68 (coe v2))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 (coe v1)
                       (coe
                          MAlonzo.Code.Data.List.Base.du_map_22
                          (coe
                             (\ v3 ->
                                case coe v3 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                                    -> case coe v5 of
                                         MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v6 v7
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                (coe v6)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_var_252
                                                   (coe v4))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError))
                          (coe
                             MAlonzo.Code.Meta.Prelude.du_enumerate_44
                             (coe
                                MAlonzo.Code.Data.List.Base.du_drop_542 (coe v0)
                                (coe
                                   MAlonzo.Code.Reflection.Utils.Core.d_argTys_68 (coe v2))))))))))
-- Tactic.Derive.DecEqFast._.derive-DecEq′
d_derive'45'DecEq'8242'_62 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Definition_280 -> AgdaAny
d_derive'45'DecEq'8242'_62 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Reflection.Utils.Debug.du_error_6 (coe ())
              (coe
                 ("[not supported] not a data type or record" :: Data.Text.Text)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'type_290 v3 v4
           -> let v5
                    = coe
                        MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () () erased
                        erased
                        (coe
                           MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () () erased
                           erased
                           (coe
                              MAlonzo.Code.Class.Monad.Core.du_mapM_102
                              (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6) (coe ())
                              (coe du_f_100 (coe v0)) (coe du_allPairs_26 (coe v4)))
                           (\ v5 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Reflection.d_returnTC_326 () erased
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_concatMap_246
                                   (coe MAlonzo.Code.Data.List.Base.du_fromMaybe_274) (coe v5))))
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Reflection.d_returnTC_326 () erased
                             (coe
                                MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196 (coe v5)
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))) in
              coe
                (case coe v4 of
                   []
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Reflection.d_returnTC_326 () erased
                          d_'96'λ'8709''8709'_30
                   _ -> coe v5)
         MAlonzo.Code.Agda.Builtin.Reflection.C_record'45'type_296 v3 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Reflection.d_returnTC_326 () erased
                (coe
                   MAlonzo.Code.Agda.Builtin.Reflection.C_lam_190
                   (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122
                      (coe ("r" :: Data.Text.Text))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Reflection.C_lam_190
                         (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122
                            (coe ("r\8242" :: Data.Text.Text)) (coe du_go_156 (coe v4))))))
         _ -> coe v2)
-- Tactic.Derive.DecEqFast._._.go
d_go_72 ::
  Integer ->
  Integer ->
  [AgdaAny] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_go_72 ~v0 ~v1 ~v2 v3 v4 = du_go_72 v3 v4
du_go_72 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
du_go_72 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Reflection.QQuotedDefinitions.d_'96'yes_26
             (coe
                MAlonzo.Code.Agda.Builtin.Reflection.C_con_178
                (coe
                   (MAlonzo.RTE.QName
                      (20 :: Integer) (1335258922519917603 :: Integer)
                      "Agda.Builtin.Equality._\8801_.refl"
                      (MAlonzo.RTE.Fixity MAlonzo.RTE.NonAssoc MAlonzo.RTE.Unrelated)))
                (coe v1))
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Reflection.C_def_184
                    (coe
                       (MAlonzo.RTE.QName
                          (234 :: Integer) (10779521135412943468 :: Integer)
                          "Function.Base.case_of_"
                          (MAlonzo.RTE.Fixity
                             MAlonzo.RTE.NonAssoc (MAlonzo.RTE.Related (0.0 :: Double)))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                          (coe
                             MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                             (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Reflection.C_def_184
                             (coe
                                (MAlonzo.RTE.QName
                                   (36 :: Integer) (11870211246910590228 :: Integer)
                                   "Class.DecEq.Core._._\8799_"
                                   (MAlonzo.RTE.Fixity
                                      MAlonzo.RTE.NonAssoc (MAlonzo.RTE.Related (4.0 :: Double)))))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                      (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                         (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Reflection.C_var_172
                                      (coe
                                         addInt
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0
                                            (addInt (coe (1 :: Integer)) (coe v4)))
                                         (coe v0))
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                         (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                            (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Reflection.C_var_172
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0
                                            (addInt (coe (1 :: Integer)) (coe v4)))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                             (coe
                                MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                   (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                   (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
                                      (coe
                                         MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe ("\172p" :: Data.Text.Text))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216))))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Reflection.C_con_244
                                               (coe
                                                  (MAlonzo.RTE.QName
                                                     (32 :: Integer)
                                                     (16368259409245829246 :: Integer)
                                                     "Relation.Nullary.Decidable.Core._because_"
                                                     (MAlonzo.RTE.Fixity
                                                        MAlonzo.RTE.NonAssoc
                                                        (MAlonzo.RTE.Related (2.0 :: Double)))))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_con_244
                                                        (coe
                                                           (MAlonzo.RTE.QName
                                                              (8 :: Integer)
                                                              (4305008439024043551 :: Integer)
                                                              "Agda.Builtin.Bool.Bool.false"
                                                              (MAlonzo.RTE.Fixity
                                                                 MAlonzo.RTE.NonAssoc
                                                                 MAlonzo.RTE.Unrelated)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_con_244
                                                           (coe
                                                              (MAlonzo.RTE.QName
                                                                 (26 :: Integer)
                                                                 (5284306542668000596 :: Integer)
                                                                 "Relation.Nullary.Reflects.Reflects.of\8319"
                                                                 (MAlonzo.RTE.Fixity
                                                                    MAlonzo.RTE.NonAssoc
                                                                    MAlonzo.RTE.Unrelated)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Reflection.C_var_252
                                                                    (coe (0 :: Integer))))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                      (coe
                                         MAlonzo.Code.Reflection.QQuotedDefinitions.d_'96'no_28
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
                                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_con_244
                                                           (coe
                                                              (MAlonzo.RTE.QName
                                                                 (20 :: Integer)
                                                                 (1335258922519917603 :: Integer)
                                                                 "Agda.Builtin.Equality._\8801_.refl"
                                                                 (MAlonzo.RTE.Fixity
                                                                    MAlonzo.RTE.NonAssoc
                                                                    MAlonzo.RTE.Unrelated)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_var_172
                                                     (coe (0 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_con_178
                                                              (coe
                                                                 (MAlonzo.RTE.QName
                                                                    (20 :: Integer)
                                                                    (1335258922519917603 :: Integer)
                                                                    "Agda.Builtin.Equality._\8801_.refl"
                                                                    (MAlonzo.RTE.Fixity
                                                                       MAlonzo.RTE.NonAssoc
                                                                       MAlonzo.RTE.Unrelated)))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Reflection.C_con_244
                                                  (coe
                                                     (MAlonzo.RTE.QName
                                                        (32 :: Integer)
                                                        (16368259409245829246 :: Integer)
                                                        "Relation.Nullary.Decidable.Core._because_"
                                                        (MAlonzo.RTE.Fixity
                                                           MAlonzo.RTE.NonAssoc
                                                           (MAlonzo.RTE.Related (2.0 :: Double)))))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_con_244
                                                           (coe
                                                              (MAlonzo.RTE.QName
                                                                 (10 :: Integer)
                                                                 (4305008439024043551 :: Integer)
                                                                 "Agda.Builtin.Bool.Bool.true"
                                                                 (MAlonzo.RTE.Fixity
                                                                    MAlonzo.RTE.NonAssoc
                                                                    MAlonzo.RTE.Unrelated)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_con_244
                                                              (coe
                                                                 (MAlonzo.RTE.QName
                                                                    (22 :: Integer)
                                                                    (5284306542668000596 :: Integer)
                                                                    "Relation.Nullary.Reflects.Reflects.of\696"
                                                                    (MAlonzo.RTE.Fixity
                                                                       MAlonzo.RTE.NonAssoc
                                                                       MAlonzo.RTE.Unrelated)))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Reflection.C_con_244
                                                                       (coe
                                                                          (MAlonzo.RTE.QName
                                                                             (20 :: Integer)
                                                                             (1335258922519917603 ::
                                                                                Integer)
                                                                             "Agda.Builtin.Equality._\8801_.refl"
                                                                             (MAlonzo.RTE.Fixity
                                                                                MAlonzo.RTE.NonAssoc
                                                                                MAlonzo.RTE.Unrelated)))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                         (coe du_go_72 (coe v0) (coe v3)))
                                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.Derive.DecEqFast._._.bumpFreeVars
d_bumpFreeVars_82 ::
  Integer ->
  Integer ->
  [AgdaAny] ->
  (Integer -> Integer) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_bumpFreeVars_82 ~v0 ~v1 ~v2 v3 = du_bumpFreeVars_82 v3
du_bumpFreeVars_82 ::
  (Integer -> Integer) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_bumpFreeVars_82 v0
  = coe du_go'8242'_90 (coe v0) (coe (0 :: Integer))
-- Tactic.Derive.DecEqFast._._._.go′
d_go'8242'_90 ::
  Integer ->
  Integer ->
  [AgdaAny] ->
  (Integer -> Integer) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_go'8242'_90 ~v0 ~v1 ~v2 v3 v4 v5 = du_go'8242'_90 v3 v4 v5
du_go'8242'_90 ::
  (Integer -> Integer) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_go'8242'_90 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 v5)
                       (coe
                          MAlonzo.Code.Class.Functor.Core.du_fmap_22
                          MAlonzo.Code.Class.Functor.Instances.d_Functor'45'Arg_448 () erased
                          () erased
                          (MAlonzo.Code.Reflection.Utils.Substitute.d_mapFreeVars_110
                             (coe v0) (coe v1))
                          v6))
                    (coe
                       du_go'8242'_90 (coe v0) (coe addInt (coe (1 :: Integer)) (coe v1))
                       (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.Derive.DecEqFast._._.f
d_f_100 ::
  Integer ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_f_100 v0 ~v1 ~v2 v3 = du_f_100 v0 v3
du_f_100 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_f_100 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () () erased
             erased (d_mkPattern_38 (coe v0) (coe v2))
             (\ v4 ->
                case coe v4 of
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                    -> case coe v6 of
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                           -> case coe v8 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                  -> coe
                                       MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () ()
                                       erased erased (d_mkPattern_38 (coe v0) (coe v3))
                                       (\ v11 ->
                                          case coe v11 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                              -> case coe v13 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                     -> case coe v15 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336
                                                                 () () erased erased
                                                                 (coe
                                                                    MAlonzo.Code.Class.Monad.Core.du__'61''60''60'__32
                                                                    (coe
                                                                       MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
                                                                    (coe ()) (coe ())
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Reflection.d_reduce_352)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Reflection.d_getType_406
                                                                       v2))
                                                                 (\ v18 ->
                                                                    coe
                                                                      MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336
                                                                      () () erased erased
                                                                      (coe
                                                                         MAlonzo.Code.Class.Monad.Core.du__'61''60''60'__32
                                                                         (coe
                                                                            MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
                                                                         (coe ()) (coe ())
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Reflection.d_reduce_352)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Reflection.d_getType_406
                                                                            v3))
                                                                      (\ v19 ->
                                                                         coe
                                                                           MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336
                                                                           () () erased erased
                                                                           (coe
                                                                              MAlonzo.Code.Reflection.Utils.TCI.du_compatible'63'_242
                                                                              (coe
                                                                                 MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
                                                                              (coe
                                                                                 MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
                                                                              (coe
                                                                                 MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
                                                                              (coe
                                                                                 MAlonzo.Code.Reflection.Utils.Core.d_resultTy_70
                                                                                 (coe v18))
                                                                              (coe
                                                                                 MAlonzo.Code.Reflection.Utils.Core.d_resultTy_70
                                                                                 (coe v19)))
                                                                           (\ v20 ->
                                                                              coe
                                                                                MAlonzo.Code.Agda.Builtin.Reflection.d_returnTC_326
                                                                                () erased
                                                                                (coe
                                                                                   MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                                   (coe v20)
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
                                                                                         (coe
                                                                                            MAlonzo.Code.Data.List.Base.du_map_22
                                                                                            (coe
                                                                                               (\ v21 ->
                                                                                                  coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                                                                       ("v"
                                                                                                        ::
                                                                                                        Data.Text.Text)
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Class.Show.Core.d_show_16
                                                                                                          MAlonzo.Code.Class.Show.Instances.d_Show'45'ℕ_36
                                                                                                          (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                                                             (coe
                                                                                                                v21))))
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                                       (coe
                                                                                                          v21))))
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                               (coe
                                                                                                  v9)
                                                                                               (coe
                                                                                                  du_bumpFreeVars_82
                                                                                                  (\ v21 ->
                                                                                                     addInt
                                                                                                       (coe
                                                                                                          v7)
                                                                                                       (coe
                                                                                                          v21))
                                                                                                  v16)))
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                                               (coe
                                                                                                  MAlonzo.Code.Reflection.Utils.Substitute.d_mapVariables_272
                                                                                                  (coe
                                                                                                     (\ v21 ->
                                                                                                        coe
                                                                                                          MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                                                          (addInt
                                                                                                             (coe
                                                                                                                v7)
                                                                                                             (coe
                                                                                                                v14))
                                                                                                          (addInt
                                                                                                             (coe
                                                                                                                (1 ::
                                                                                                                   Integer))
                                                                                                             (coe
                                                                                                                v21))))
                                                                                                  (coe
                                                                                                     v10)))
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Reflection.Utils.Substitute.d_mapVariables_272
                                                                                                     (coe
                                                                                                        (\ v21 ->
                                                                                                           coe
                                                                                                             MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                                                             v14
                                                                                                             (addInt
                                                                                                                (coe
                                                                                                                   (1 ::
                                                                                                                      Integer))
                                                                                                                (coe
                                                                                                                   v21))))
                                                                                                     (coe
                                                                                                        v17)))
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                                         (coe
                                                                                            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                                            (coe
                                                                                               MAlonzo.Code.Class.DecEq.Core.du__'61''61'__18
                                                                                               (coe
                                                                                                  ())
                                                                                               (coe
                                                                                                  MAlonzo.Code.Class.DecEq.Instances.d_DecEq'45'Name_200)
                                                                                               (coe
                                                                                                  v2)
                                                                                               (coe
                                                                                                  v3))
                                                                                            (coe
                                                                                               du_go_72
                                                                                               (coe
                                                                                                  v7)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.List.Base.du_filter_648
                                                                                                  (coe
                                                                                                     (\ v21 ->
                                                                                                        coe
                                                                                                          MAlonzo.Code.Reflection.Utils.Args.du_isVisible'63'_40
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                                                             (coe
                                                                                                                v21))))
                                                                                                  (coe
                                                                                                     v9)))
                                                                                            (coe
                                                                                               MAlonzo.Code.Reflection.QQuotedDefinitions.d_'96'no_28
                                                                                               (coe
                                                                                                  d_'96'λ'8709''8709'_30)))))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))))
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                _ -> MAlonzo.RTE.mazUnreachableError
                         _ -> MAlonzo.RTE.mazUnreachableError
                  _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.Derive.DecEqFast._._.go
d_go_156 ::
  Integer ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_go_156 ~v0 ~v1 ~v2 v3 = du_go_156 v3
du_go_156 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
du_go_156 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Reflection.QQuotedDefinitions.d_'96'yes_26
             (coe
                MAlonzo.Code.Agda.Builtin.Reflection.C_con_178
                (coe
                   (MAlonzo.RTE.QName
                      (20 :: Integer) (1335258922519917603 :: Integer)
                      "Agda.Builtin.Equality._\8801_.refl"
                      (MAlonzo.RTE.Fixity MAlonzo.RTE.NonAssoc MAlonzo.RTE.Unrelated)))
                (coe v0))
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82 v5 v6
                      -> case coe v6 of
                           MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74 v7 v8
                             -> let v9 = coe du_go_156 (coe v2) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Reflection.C_def_184
                                            (coe
                                               (MAlonzo.RTE.QName
                                                  (234 :: Integer) (10779521135412943468 :: Integer)
                                                  "Function.Base.case_of_"
                                                  (MAlonzo.RTE.Fixity
                                                     MAlonzo.RTE.NonAssoc
                                                     (MAlonzo.RTE.Related (0.0 :: Double)))))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                        (coe v7)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_def_184
                                                     (coe
                                                        (MAlonzo.RTE.QName
                                                           (36 :: Integer)
                                                           (11870211246910590228 :: Integer)
                                                           "Class.DecEq.Core._._\8799_"
                                                           (MAlonzo.RTE.Fixity
                                                              MAlonzo.RTE.NonAssoc
                                                              (MAlonzo.RTE.Related
                                                                 (4.0 :: Double)))))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                 (coe v7)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_def_184
                                                              (coe v4)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                          (coe v7)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Reflection.C_var_172
                                                                       (coe (1 :: Integer))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                    (coe v7)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Reflection.C_def_184
                                                                 (coe v4)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                             (coe v7)
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Reflection.C_var_172
                                                                          (coe (0 :: Integer))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                           (coe v7)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       ("\172p" :: Data.Text.Text))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                             (coe v7)
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216))))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                          (coe v7)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Reflection.C_con_244
                                                                       (coe
                                                                          (MAlonzo.RTE.QName
                                                                             (32 :: Integer)
                                                                             (16368259409245829246 ::
                                                                                Integer)
                                                                             "Relation.Nullary.Decidable.Core._because_"
                                                                             (MAlonzo.RTE.Fixity
                                                                                MAlonzo.RTE.NonAssoc
                                                                                (MAlonzo.RTE.Related
                                                                                   (2.0 ::
                                                                                      Double)))))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                                   (coe v7)
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Reflection.C_con_244
                                                                                (coe
                                                                                   (MAlonzo.RTE.QName
                                                                                      (8 :: Integer)
                                                                                      (4305008439024043551 ::
                                                                                         Integer)
                                                                                      "Agda.Builtin.Bool.Bool.false"
                                                                                      (MAlonzo.RTE.Fixity
                                                                                         MAlonzo.RTE.NonAssoc
                                                                                         MAlonzo.RTE.Unrelated)))
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                                      (coe v7)
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_con_244
                                                                                   (coe
                                                                                      (MAlonzo.RTE.QName
                                                                                         (26 ::
                                                                                            Integer)
                                                                                         (5284306542668000596 ::
                                                                                            Integer)
                                                                                         "Relation.Nullary.Reflects.Reflects.of\8319"
                                                                                         (MAlonzo.RTE.Fixity
                                                                                            MAlonzo.RTE.NonAssoc
                                                                                            MAlonzo.RTE.Unrelated)))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                                               (coe
                                                                                                  v7)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_var_252
                                                                                            (coe
                                                                                               (0 ::
                                                                                                  Integer))))
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                              (coe
                                                                 MAlonzo.Code.Reflection.QQuotedDefinitions.d_'96'no_28
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                                      (coe v7)
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_con_244
                                                                                   (coe
                                                                                      (MAlonzo.RTE.QName
                                                                                         (20 ::
                                                                                            Integer)
                                                                                         (1335258922519917603 ::
                                                                                            Integer)
                                                                                         "Agda.Builtin.Equality._\8801_.refl"
                                                                                         (MAlonzo.RTE.Fixity
                                                                                            MAlonzo.RTE.NonAssoc
                                                                                            MAlonzo.RTE.Unrelated)))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Reflection.C_var_172
                                                                             (coe (0 :: Integer))
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                                         (coe v7)
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_con_178
                                                                                      (coe
                                                                                         (MAlonzo.RTE.QName
                                                                                            (20 ::
                                                                                               Integer)
                                                                                            (1335258922519917603 ::
                                                                                               Integer)
                                                                                            "Agda.Builtin.Equality._\8801_.refl"
                                                                                            (MAlonzo.RTE.Fixity
                                                                                               MAlonzo.RTE.NonAssoc
                                                                                               MAlonzo.RTE.Unrelated)))
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                             (coe v7)
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Reflection.C_con_244
                                                                          (coe
                                                                             (MAlonzo.RTE.QName
                                                                                (32 :: Integer)
                                                                                (16368259409245829246 ::
                                                                                   Integer)
                                                                                "Relation.Nullary.Decidable.Core._because_"
                                                                                (MAlonzo.RTE.Fixity
                                                                                   MAlonzo.RTE.NonAssoc
                                                                                   (MAlonzo.RTE.Related
                                                                                      (2.0 ::
                                                                                         Double)))))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                                      (coe v7)
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_con_244
                                                                                   (coe
                                                                                      (MAlonzo.RTE.QName
                                                                                         (10 ::
                                                                                            Integer)
                                                                                         (4305008439024043551 ::
                                                                                            Integer)
                                                                                         "Agda.Builtin.Bool.Bool.true"
                                                                                         (MAlonzo.RTE.Fixity
                                                                                            MAlonzo.RTE.NonAssoc
                                                                                            MAlonzo.RTE.Unrelated)))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                                         (coe v7)
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_con_244
                                                                                      (coe
                                                                                         (MAlonzo.RTE.QName
                                                                                            (22 ::
                                                                                               Integer)
                                                                                            (5284306542668000596 ::
                                                                                               Integer)
                                                                                            "Relation.Nullary.Reflects.Reflects.of\696"
                                                                                            (MAlonzo.RTE.Fixity
                                                                                               MAlonzo.RTE.NonAssoc
                                                                                               MAlonzo.RTE.Unrelated)))
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                                                  (coe
                                                                                                     v7)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Reflection.C_con_244
                                                                                               (coe
                                                                                                  (MAlonzo.RTE.QName
                                                                                                     (20 ::
                                                                                                        Integer)
                                                                                                     (1335258922519917603 ::
                                                                                                        Integer)
                                                                                                     "Agda.Builtin.Equality._\8801_.refl"
                                                                                                     (MAlonzo.RTE.Fixity
                                                                                                        MAlonzo.RTE.NonAssoc
                                                                                                        MAlonzo.RTE.Unrelated)))
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                                 (coe du_go_156 (coe v2)))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                     _ -> coe v9)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.Derive.DecEqFast.derive-DecEq
d_derive'45'DecEq_164 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_derive'45'DecEq_164 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () () erased
      erased
      (coe
         MAlonzo.Code.Agda.Builtin.Reflection.d_getDefinition_408
         (MAlonzo.RTE.QName
            (10 :: Integer) (11870211246910590228 :: Integer)
            "Class.DecEq.Core.DecEq"
            (MAlonzo.RTE.Fixity MAlonzo.RTE.NonAssoc MAlonzo.RTE.Unrelated)))
      (\ v1 ->
         let v2
               = coe
                   MAlonzo.Code.Reflection.Utils.Debug.du_error_6 (coe ())
                   (coe ("impossible" :: Data.Text.Text)) in
         coe
           (case coe v1 of
              MAlonzo.Code.Agda.Builtin.Reflection.C_record'45'type_296 v3 v4
                -> coe
                     MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () () erased
                     erased
                     (coe
                        MAlonzo.Code.Class.Monad.Core.du_forM_118
                        (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6) (coe ())
                        (coe v0)
                        (coe
                           (\ v5 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () () erased
                                erased
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Reflection.d_freshName_390
                                   (coe
                                      MAlonzo.Code.Class.Show.Core.d_show_16
                                      MAlonzo.Code.Class.Show.Instances.d_Show'45'Name_68
                                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))))
                                (\ v6 ->
                                   coe
                                     MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () () erased
                                     erased
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Reflection.d_getType_406
                                        (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
                                     (\ v7 ->
                                        coe
                                          MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () ()
                                          erased erased
                                          MAlonzo.Code.Agda.Builtin.Reflection.d_getContext_376
                                          (\ v8 ->
                                             coe
                                               MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 ()
                                               () erased erased
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Reflection.d_getDefinition_408
                                                  (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe v5)))
                                               (\ v9 ->
                                                  coe
                                                    MAlonzo.Code.Class.Monad.Core.du__'62''62'__24
                                                    (coe
                                                       MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
                                                    (coe ()) (coe ())
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Reflection.d_declareDef_392
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                          (coe v6))
                                                       (MAlonzo.Code.Reflection.Utils.Args.d_'8704'indices'8943'_78
                                                          (coe
                                                             MAlonzo.Code.Reflection.Utils.Core.d_argTys_68
                                                             (coe v7))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Reflection.C_def_184
                                                             (coe
                                                                (MAlonzo.RTE.QName
                                                                   (404 :: Integer)
                                                                   (5359185163178559078 :: Integer)
                                                                   "Relation.Binary.Definitions.Decidable"
                                                                   (MAlonzo.RTE.Fixity
                                                                      MAlonzo.RTE.NonAssoc
                                                                      MAlonzo.RTE.Unrelated)))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Reflection.C_hidden_52)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_hidden_52)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                      (coe
                                                                         MAlonzo.Code.Reflection.Utils.Args.d_apply'8943'_88
                                                                         (coe
                                                                            MAlonzo.Code.Reflection.Utils.Core.d_argTys_68
                                                                            (coe v7))
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                            (coe v5))))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_def_184
                                                                            (coe
                                                                               (MAlonzo.RTE.QName
                                                                                  (12 :: Integer)
                                                                                  (1335258922519917603 ::
                                                                                     Integer)
                                                                                  "Agda.Builtin.Equality._\8801_"
                                                                                  (MAlonzo.RTE.Fixity
                                                                                     MAlonzo.RTE.NonAssoc
                                                                                     (MAlonzo.RTE.Related
                                                                                        (4.0 ::
                                                                                           Double)))))
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
                                                    (coe
                                                       MAlonzo.Code.Class.Monad.Core.du__'62''62'__24
                                                       (coe
                                                          MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
                                                       (coe ()) (coe ())
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Reflection.d_declareDef_392
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_instance'8242'_54)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                (coe v5)))
                                                          (MAlonzo.Code.Reflection.Utils.Args.d_'8704'indices'8943'_78
                                                             (coe
                                                                MAlonzo.Code.Reflection.Utils.Core.d_argTys_68
                                                                (coe v7))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Reflection.C_def_184
                                                                (coe
                                                                   (MAlonzo.RTE.QName
                                                                      (10 :: Integer)
                                                                      (11870211246910590228 ::
                                                                         Integer)
                                                                      "Class.DecEq.Core.DecEq"
                                                                      (MAlonzo.RTE.Fixity
                                                                         MAlonzo.RTE.NonAssoc
                                                                         MAlonzo.RTE.Unrelated)))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                      (coe
                                                                         MAlonzo.Code.Reflection.Utils.Args.d_apply'8943'_88
                                                                         (coe
                                                                            MAlonzo.Code.Reflection.Utils.Core.d_argTys_68
                                                                            (coe v7))
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                            (coe v5))))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                                                       (coe
                                                          MAlonzo.Code.Class.Monad.Core.du__'62''62'__24
                                                          (coe
                                                             MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
                                                          (coe ()) (coe ())
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Reflection.d_defineFun_404
                                                             (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                (coe v5))
                                                             (coe
                                                                MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
                                                                   (coe
                                                                      MAlonzo.Code.Data.List.Base.du_map_22
                                                                      (coe
                                                                         (\ v10 ->
                                                                            coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe
                                                                                 ("_"
                                                                                  ::
                                                                                  Data.Text.Text))
                                                                              (coe v10)))
                                                                      (coe
                                                                         MAlonzo.Code.Data.List.Base.du_take_530
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                            (MAlonzo.Code.Reflection.Utils.Core.d_parameters_114
                                                                               (coe v9))
                                                                            (coe
                                                                               MAlonzo.Code.Data.List.Base.du_length_268
                                                                               v8))
                                                                         (coe
                                                                            MAlonzo.Code.Reflection.Utils.Core.d_argTys_68
                                                                            (coe v7))))
                                                                   (coe
                                                                      MAlonzo.Code.Data.List.Base.du_map_22
                                                                      (coe
                                                                         (\ v10 ->
                                                                            case coe v10 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                                -> coe
                                                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_hidden_52)
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_var_252
                                                                                        (coe v11))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                      (coe
                                                                         MAlonzo.Code.Meta.Prelude.du_enumerate_44
                                                                         (coe
                                                                            MAlonzo.Code.Data.List.Base.du_take_530
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                               (MAlonzo.Code.Reflection.Utils.Core.d_parameters_114
                                                                                  (coe v9))
                                                                               (coe
                                                                                  MAlonzo.Code.Data.List.Base.du_length_268
                                                                                  v8))
                                                                            (coe
                                                                               MAlonzo.Code.Reflection.Utils.Core.d_argTys_68
                                                                               (coe v7)))))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_con_178
                                                                      (coe v3)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Reflection.C_def_184
                                                                               (coe v6)
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336
                                                             () () erased erased
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Reflection.d_inContext_388
                                                                () erased
                                                                (coe
                                                                   MAlonzo.Code.Data.List.Base.du_reverse_444
                                                                   (coe
                                                                      MAlonzo.Code.Data.List.Base.du_map_22
                                                                      (coe
                                                                         (\ v10 ->
                                                                            coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe
                                                                                 ("_"
                                                                                  ::
                                                                                  Data.Text.Text))
                                                                              (coe v10)))
                                                                      (coe
                                                                         MAlonzo.Code.Data.List.Base.du_take_530
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                            (MAlonzo.Code.Reflection.Utils.Core.d_parameters_114
                                                                               (coe v9))
                                                                            (coe
                                                                               MAlonzo.Code.Data.List.Base.du_length_268
                                                                               v8))
                                                                         (coe
                                                                            MAlonzo.Code.Reflection.Utils.Core.d_argTys_68
                                                                            (coe v7)))))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336
                                                                   () () erased erased
                                                                   MAlonzo.Code.Agda.Builtin.Reflection.d_getContext_376
                                                                   (\ v10 ->
                                                                      d_derive'45'DecEq'8242'_62
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Base.du_length_268
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Base.du_map_22
                                                                              (coe
                                                                                 (\ v11 ->
                                                                                    coe
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                      (coe
                                                                                         ("_"
                                                                                          ::
                                                                                          Data.Text.Text))
                                                                                      (coe v11)))
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Base.du_take_530
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                                    (MAlonzo.Code.Reflection.Utils.Core.d_parameters_114
                                                                                       (coe v9))
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.List.Base.du_length_268
                                                                                       v8))
                                                                                 (coe
                                                                                    MAlonzo.Code.Reflection.Utils.Core.d_argTys_68
                                                                                    (coe v7)))))
                                                                        (coe v9))))
                                                             (\ v10 ->
                                                                coe
                                                                  MAlonzo.Code.Agda.Builtin.Reflection.d_returnTC_326
                                                                  () erased
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe v6)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Base.du_map_22
                                                                              (coe
                                                                                 (\ v11 ->
                                                                                    case coe v11 of
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                                        -> coe
                                                                                             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_hidden_52)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.Reflection.C_var_252
                                                                                                (coe
                                                                                                   v12))
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                              (coe
                                                                                 MAlonzo.Code.Meta.Prelude.du_enumerate_44
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Base.du_take_530
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                                       (MAlonzo.Code.Reflection.Utils.Core.d_parameters_114
                                                                                          (coe v9))
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.List.Base.du_length_268
                                                                                          v8))
                                                                                    (coe
                                                                                       MAlonzo.Code.Reflection.Utils.Core.d_argTys_68
                                                                                       (coe v7)))))
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Base.du_map_22
                                                                              (coe
                                                                                 (\ v11 ->
                                                                                    coe
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                      (coe
                                                                                         ("_"
                                                                                          ::
                                                                                          Data.Text.Text))
                                                                                      (coe v11)))
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Base.du_take_530
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                                    (MAlonzo.Code.Reflection.Utils.Core.d_parameters_114
                                                                                       (coe v9))
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.List.Base.du_length_268
                                                                                       v8))
                                                                                 (coe
                                                                                    MAlonzo.Code.Reflection.Utils.Core.d_argTys_68
                                                                                    (coe v7)))))
                                                                        (coe v10))))))))))))))
                     (\ v5 ->
                        coe
                          MAlonzo.Code.Class.Monad.Core.du_return'8868'_132
                          (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6) (coe ())
                          (coe
                             MAlonzo.Code.Class.Monad.Core.du_forM_118
                             (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6) (coe ())
                             (coe v5)
                             (coe
                                (\ v6 ->
                                   coe
                                     MAlonzo.Code.Agda.Builtin.Reflection.d_defineFun_404
                                     (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6))
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                    (coe v6))))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                    (coe v6))))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                 (coe v6)))))))))
              _ -> coe v2))
-- Tactic.Derive.DecEqFast.R⁰
d_R'8304'_224 = ()
data T_R'8304'_224 = C_R'8304''46'constructor_38365
-- Tactic.Derive.DecEqFast.R¹
d_R'185'_228 = ()
newtype T_R'185'_228 = C_R'185''46'constructor_38423 Integer
-- Tactic.Derive.DecEqFast.R¹.x
d_x_232 :: T_R'185'_228 -> Integer
d_x_232 v0
  = case coe v0 of
      C_R'185''46'constructor_38423 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.Derive.DecEqFast.R²
d_R'178'_236 = ()
data T_R'178'_236
  = C_R'178''46'constructor_40035 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                                  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
-- Tactic.Derive.DecEqFast.R².x
d_x_242 :: T_R'178'_236 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_x_242 v0
  = case coe v0 of
      C_R'178''46'constructor_40035 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.Derive.DecEqFast.R².y
d_y_244 :: T_R'178'_236 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_y_244 v0
  = case coe v0 of
      C_R'178''46'constructor_40035 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.Derive.DecEqFast.X¹
d_X'185'_252 = ()
data T_X'185'_252 = C_x_254
-- Tactic.Derive.DecEqFast.X²
d_X'178'_258 = ()
data T_X'178'_258 = C_x_260 | C_y_262
-- Tactic.Derive.DecEqFast.XXX
d_XXX_274 = ()
data T_XXX_274
  = C_c'8322''8242'_276 [T_X'178'_258] |
    C__'8855''8855'__278 T_XXX_274 T_XXX_274
-- Tactic.Derive.DecEqFast.ℕ′
d_ℕ'8242'_282 = ()
data T_ℕ'8242'_282 = C_O_284 | C_S_286 T_ℕ'8242'_282
-- Tactic.Derive.DecEqFast.M₁
d_M'8321'_296 = ()
data T_M'8321'_296
  = C_m'8321'_300 | C_m'8322''8594''8321'_302 T_M'8322'_298
-- Tactic.Derive.DecEqFast.M₂
d_M'8322'_298 = ()
data T_M'8322'_298
  = C_m'8322'_304 | C_m'8321''8594''8322'_306 T_M'8321'_296
-- Tactic.Derive.DecEqFast.Fin′
d_Fin'8242'_316 a0 = ()
data T_Fin'8242'_316 = C_O_320 | C_S_324 T_Fin'8242'_316
-- Tactic.Derive.DecEqFast.Wrapℕ
d_Wrapℕ_368 = ()
newtype T_Wrapℕ_368 = C_Mk_370 Integer
-- Tactic.Derive.DecEqFast.Enum
d_Enum_388 = ()
data T_Enum_388 = C_I_390 | C_II_392
-- Tactic.Derive.DecEqFast.Time
d_Time_398 :: ()
d_Time_398 = erased
-- Tactic.Derive.DecEqFast.Exprℕ′
d_Exprℕ'8242'_400 a0 a1 = ()
data T_Exprℕ'8242'_400
  = C_var_402 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_'8245'_404 Integer |
    C__'96''43'__406 T_Exprℕ'8242'_400 T_Exprℕ'8242'_400 |
    C__'96''45'__408 T_Exprℕ'8242'_400 T_Exprℕ'8242'_400 |
    C__'96''61'__410 T_Exprℕ'8242'_400 T_Exprℕ'8242'_400 |
    C__'96''60'__412 T_Exprℕ'8242'_400 T_Exprℕ'8242'_400 |
    C_'96'if_then_else__414 T_Exprℕ'8242'_400 T_Exprℕ'8242'_400
                            T_Exprℕ'8242'_400 |
    C_'8739'_'8739'_416 T_Exprℕ'8242'_400 |
    C_hash_418 T_Exprℕ'8242'_400 |
    C_versig_420 [Integer] [MAlonzo.Code.Data.Fin.Base.T_Fin_10] |
    C_absAfter_'8658'__422 Integer T_Exprℕ'8242'_400 |
    C_relAfter_'8658'__424 Integer T_Exprℕ'8242'_400
-- Tactic.Derive.DecEqFast.Pos
d_Pos_430 a0 = ()
newtype T_Pos_430
  = C_Pos'46'constructor_291575 MAlonzo.Code.Data.Fin.Base.T_Fin_10
-- Tactic.Derive.DecEqFast.Pos.pos
d_pos_436 :: T_Pos_430 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_pos_436 v0
  = case coe v0 of
      C_Pos'46'constructor_291575 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.Derive.DecEqFast.Test₁.X
d_X_454 a0 a1 a2 a3 a4 = ()
data T_X_454
  = C_x'8320'_456 | C_y'8320'_458 | C_z'8320'_460 | C_x'8321'_462 |
    C_y'8321'_464 | C_z'8321'_466 | C_fromA_470 AgdaAny |
    C_fromB_474 AgdaAny
-- Tactic.Derive.DecEqFast.Test₁.R
d_R_482 a0 a1 a2 a3 = ()
data T_R_482 = C_R'46'constructor_342493 AgdaAny AgdaAny
-- Tactic.Derive.DecEqFast.Test₁.R.r₁
d_r'8321'_488 :: T_R_482 -> AgdaAny
d_r'8321'_488 v0
  = case coe v0 of
      C_R'46'constructor_342493 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.Derive.DecEqFast.Test₁.R.r₂
d_r'8322'_490 :: T_R_482 -> AgdaAny
d_r'8322'_490 v0
  = case coe v0 of
      C_R'46'constructor_342493 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.Derive.DecEqFast.Test₁.R′
d_R'8242'_496 a0 a1 a2 a3 = ()
data T_R'8242'_496
  = C_R'8242''46'constructor_351939 MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
                                    T_X_454
-- Tactic.Derive.DecEqFast.Test₁.R′.r₁
d_r'8321'_502 ::
  T_R'8242'_496 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_r'8321'_502 v0
  = case coe v0 of
      C_R'8242''46'constructor_351939 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.Derive.DecEqFast.Test₁.R′.r₂
d_r'8322'_504 :: T_R'8242'_496 -> T_X_454
d_r'8322'_504 v0
  = case coe v0 of
      C_R'8242''46'constructor_351939 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
