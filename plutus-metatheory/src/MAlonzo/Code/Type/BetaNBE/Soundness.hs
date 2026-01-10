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

module MAlonzo.Code.Type.BetaNBE.Soundness where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.BetaNBE
import qualified MAlonzo.Code.Type.BetaNormal
import qualified MAlonzo.Code.Type.Equality
import qualified MAlonzo.Code.Type.RenamingSubstitution
import qualified MAlonzo.Code.Utils

-- Type.BetaNBE.Soundness.SR
d_SR_10 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 -> AgdaAny -> ()
d_SR_10 = erased
-- Type.BetaNBE.Soundness.reflectSR
d_reflectSR_54 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Ne'8902'__6 ->
  MAlonzo.Code.Type.Equality.T__'8801'β__10 -> AgdaAny
d_reflectSR_54 ~v0 v1 ~v2 ~v3 v4 = du_reflectSR_54 v1 v4
du_reflectSR_54 ::
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.Equality.T__'8801'β__10 -> AgdaAny
du_reflectSR_54 v0 v1 = coe seq (coe v0) (coe v1)
-- Type.BetaNBE.Soundness.reifySR
d_reifySR_74 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Type.Equality.T__'8801'β__10
d_reifySR_74 v0 v1 ~v2 v3 v4 = du_reifySR_74 v0 v1 v3 v4
du_reifySR_74 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Type.Equality.T__'8801'β__10
du_reifySR_74 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Utils.C_'42'_704 -> coe v3
      MAlonzo.Code.Utils.C_'9839'_706 -> coe v3
      MAlonzo.Code.Utils.C__'8658'__708 v4 v5
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6 -> coe v3
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> case coe v8 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                             -> coe
                                  MAlonzo.Code.Type.Equality.C_trans'8801'β_18
                                  (coe MAlonzo.Code.Type.C_ƛ_28 v7) v9
                                  (coe
                                     MAlonzo.Code.Type.Equality.C_trans'8801'β_18
                                     (coe
                                        MAlonzo.Code.Type.C_ƛ_28
                                        (MAlonzo.Code.Type.RenamingSubstitution.d_sub_346
                                           (coe
                                              MAlonzo.Code.Type.C__'44''8902'__6
                                              (coe
                                                 MAlonzo.Code.Type.C__'44''8902'__6 (coe v0)
                                                 (coe v4))
                                              (coe v4))
                                           (coe
                                              MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v4))
                                           (coe
                                              MAlonzo.Code.Type.RenamingSubstitution.du_sub'45'cons_420
                                              (\ v11 v12 -> coe MAlonzo.Code.Type.C_'96'_22 v12)
                                              (coe
                                                 MAlonzo.Code.Type.C_'96'_22
                                                 (coe MAlonzo.Code.Type.C_Z_16)))
                                           (coe v5)
                                           (coe
                                              MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                                              (coe
                                                 MAlonzo.Code.Type.C__'44''8902'__6 (coe v0)
                                                 (coe v4))
                                              (coe
                                                 MAlonzo.Code.Type.C__'44''8902'__6
                                                 (coe
                                                    MAlonzo.Code.Type.C__'44''8902'__6 (coe v0)
                                                    (coe v4))
                                                 (coe v4))
                                              (coe
                                                 MAlonzo.Code.Type.RenamingSubstitution.du_ext_18
                                                 (coe (\ v11 -> coe MAlonzo.Code.Type.C_S_18)))
                                              (coe v5) (coe v7))))
                                     (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76)
                                     (coe
                                        MAlonzo.Code.Type.Equality.C_ƛ'8801'β_24
                                        (coe
                                           MAlonzo.Code.Type.Equality.C_trans'8801'β_18
                                           (coe
                                              MAlonzo.Code.Type.C__'183'__30 v4
                                              (coe
                                                 MAlonzo.Code.Type.C_ƛ_28
                                                 (MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                                                    (coe
                                                       MAlonzo.Code.Type.C__'44''8902'__6 (coe v0)
                                                       (coe v4))
                                                    (coe
                                                       MAlonzo.Code.Type.C__'44''8902'__6
                                                       (coe
                                                          MAlonzo.Code.Type.C__'44''8902'__6
                                                          (coe v0) (coe v4))
                                                       (coe v4))
                                                    (coe
                                                       MAlonzo.Code.Type.RenamingSubstitution.du_ext_18
                                                       (coe
                                                          (\ v11 -> coe MAlonzo.Code.Type.C_S_18)))
                                                    (coe v5) (coe v7)))
                                              (coe
                                                 MAlonzo.Code.Type.C_'96'_22
                                                 (coe MAlonzo.Code.Type.C_Z_16)))
                                           (coe
                                              MAlonzo.Code.Type.Equality.C_sym'8801'β_16
                                              (coe MAlonzo.Code.Type.Equality.C_β'8801'β_48))
                                           (coe
                                              du_reifySR_74
                                              (coe
                                                 MAlonzo.Code.Type.C__'44''8902'__6 (coe v0)
                                                 (coe v4))
                                              (coe v5)
                                              (coe
                                                 v6
                                                 (coe
                                                    MAlonzo.Code.Type.C__'44''8902'__6 (coe v0)
                                                    (coe v4))
                                                 (\ v11 -> coe MAlonzo.Code.Type.C_S_18)
                                                 (coe
                                                    MAlonzo.Code.Type.BetaNBE.du_fresh_38 (coe v4)))
                                              (coe
                                                 v10
                                                 (coe
                                                    MAlonzo.Code.Type.C__'44''8902'__6 (coe v0)
                                                    (coe v4))
                                                 (\ v11 -> coe MAlonzo.Code.Type.C_S_18)
                                                 (coe
                                                    MAlonzo.Code.Type.C_'96'_22
                                                    (coe MAlonzo.Code.Type.C_Z_16))
                                                 (coe
                                                    MAlonzo.Code.Type.BetaNBE.du_reflect_22 (coe v4)
                                                    (coe
                                                       MAlonzo.Code.Type.BetaNormal.C_'96'_8
                                                       (coe MAlonzo.Code.Type.C_Z_16)))
                                                 (coe
                                                    du_reflectSR_54 (coe v4)
                                                    (coe
                                                       MAlonzo.Code.Type.Equality.C_refl'8801'β_14)))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.Soundness.SREnv
d_SREnv_108 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  ()
d_SREnv_108 = erased
-- Type.BetaNBE.Soundness.SR,,⋆
d_SR'44''44''8902'_134 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny
d_SR'44''44''8902'_134 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_SR'44''44''8902'_134 v4 v8 v9 v10
du_SR'44''44''8902'_134 ::
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny
du_SR'44''44''8902'_134 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Type.C_Z_16 -> coe v1
      MAlonzo.Code.Type.C_S_18 v7 -> coe v0 v2 v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.Soundness.subSR
d_subSR_156 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.Equality.T__'8801'β__10 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_subSR_156 ~v0 v1 v2 ~v3 v4 v5 v6 = du_subSR_156 v1 v2 v4 v5 v6
du_subSR_156 ::
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.Equality.T__'8801'β__10 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_subSR_156 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Utils.C_'42'_704
        -> coe MAlonzo.Code.Type.Equality.C_trans'8801'β_18 v1 v2 v4
      MAlonzo.Code.Utils.C_'9839'_706
        -> coe MAlonzo.Code.Type.Equality.C_trans'8801'β_18 v1 v2 v4
      MAlonzo.Code.Utils.C__'8658'__708 v5 v6
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
               -> coe MAlonzo.Code.Type.Equality.C_trans'8801'β_18 v1 v2 v4
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v9 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe MAlonzo.Code.Type.Equality.C_trans'8801'β_18 v1 v2 v10)
                                     (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.Soundness.renSR
d_renSR_202 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_renSR_202 v0 v1 v2 v3 v4 v5 v6
  = case coe v3 of
      MAlonzo.Code.Utils.C_'42'_704
        -> coe
             MAlonzo.Code.Type.Equality.C_trans'8801'β_18
             (MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe
                   MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v3)
                   (coe v5)))
             (MAlonzo.Code.Type.Equality.d_ren'8801'β_80
                (coe v0) (coe v1) (coe v3) (coe v4)
                (coe
                   MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v3)
                   (coe v5))
                (coe v2) (coe v6))
             (coe
                MAlonzo.Code.Type.Equality.C_sym'8801'β_16
                (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76))
      MAlonzo.Code.Utils.C_'9839'_706
        -> coe
             MAlonzo.Code.Type.Equality.C_trans'8801'β_18
             (MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                (coe v0) (coe v1) (coe v2) (coe v3)
                (coe
                   MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v3)
                   (coe v5)))
             (MAlonzo.Code.Type.Equality.d_ren'8801'β_80
                (coe v0) (coe v1) (coe v3) (coe v4)
                (coe
                   MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v3)
                   (coe v5))
                (coe v2) (coe v6))
             (coe
                MAlonzo.Code.Type.Equality.C_sym'8801'β_16
                (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76))
      MAlonzo.Code.Utils.C__'8658'__708 v7 v8
        -> case coe v5 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
               -> coe
                    MAlonzo.Code.Type.Equality.C_trans'8801'β_18
                    (MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                       (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe MAlonzo.Code.Type.BetaNormal.du_embNe_134 (coe v0) (coe v9)))
                    (MAlonzo.Code.Type.Equality.d_ren'8801'β_80
                       (coe v0) (coe v1) (coe v3) (coe v4)
                       (coe MAlonzo.Code.Type.BetaNormal.du_embNe_134 (coe v0) (coe v9))
                       (coe v2) (coe v6))
                    (coe
                       MAlonzo.Code.Type.Equality.C_sym'8801'β_16
                       (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> case coe v11 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                                     (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v7))
                                     (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v7))
                                     (coe MAlonzo.Code.Type.RenamingSubstitution.du_ext_18 (coe v2))
                                     (coe v8) (coe v10))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        MAlonzo.Code.Type.Equality.d_ren'8801'β_80 (coe v0) (coe v1)
                                        (coe v3) (coe v4) (coe MAlonzo.Code.Type.C_ƛ_28 v10)
                                        (coe v2) (coe v12))
                                     (coe
                                        (\ v14 v15 v16 v17 v18 ->
                                           coe
                                             du_subSR_156 (coe v8)
                                             (coe
                                                MAlonzo.Code.Type.C__'183'__30 v7
                                                (coe
                                                   MAlonzo.Code.Type.C_ƛ_28
                                                   (MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                                                      (coe
                                                         MAlonzo.Code.Type.C__'44''8902'__6 (coe v0)
                                                         (coe v7))
                                                      (coe
                                                         MAlonzo.Code.Type.C__'44''8902'__6
                                                         (coe v14) (coe v7))
                                                      (coe
                                                         MAlonzo.Code.Type.RenamingSubstitution.du_ext_18
                                                         (coe
                                                            (\ v19 ->
                                                               let v20 = coe v2 v19 in
                                                               coe
                                                                 (\ v21 ->
                                                                    coe v15 v19 (coe v20 v21)))))
                                                      (coe v8) (coe v10)))
                                                v16)
                                             (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76)
                                             (coe
                                                MAlonzo.Code.Type.BetaNBE.d__'183'V__150 (coe v14)
                                                (coe v7) (coe v8)
                                                (coe
                                                   MAlonzo.Code.Type.BetaNBE.d_renVal_46 (coe v3)
                                                   (coe v0) (coe v14)
                                                   (coe (\ v19 v20 -> coe v15 v19 (coe v2 v19 v20)))
                                                   (coe v5))
                                                (coe v17))
                                             (coe
                                                v13 v14 (\ v19 v20 -> coe v15 v19 (coe v2 v19 v20))
                                                v16 v17 v18))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.Soundness.exts-sub-cons
d_exts'45'sub'45'cons_268 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_exts'45'sub'45'cons_268 = erased
-- Type.BetaNBE.Soundness.subSREnv
d_subSREnv_288 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny
d_subSREnv_288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_subSREnv_288 v6 v7 v8
du_subSREnv_288 ::
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny
du_subSREnv_288 v0 v1 v2 = coe v0 v1 v2
-- Type.BetaNBE.Soundness.SRweak
d_SRweak_310 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny
d_SRweak_310 ~v0 v1 v2 v3 v4 v5 v6
  = du_SRweak_310 v1 v2 v3 v4 v5 v6
du_SRweak_310 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny
du_SRweak_310 v0 v1 v2 v3 v4 v5
  = coe
      du_subSREnv_288
      (coe
         du_SR'44''44''8902'_134
         (coe
            (\ v6 v7 ->
               d_renSR_202
                 (coe v0) (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v4))
                 (coe (\ v8 -> coe MAlonzo.Code.Type.C_S_18)) (coe v6)
                 (coe v1 v6 v7) (coe v2 v6 v7) (coe v3 v6 v7)))
         (coe
            du_reflectSR_54 (coe v4)
            (coe MAlonzo.Code.Type.Equality.C_refl'8801'β_14)))
      (coe v5)
-- Type.BetaNBE.Soundness.SRApp
d_SRApp_328 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_SRApp_328 v0 v1 v2 ~v3 v4 v5 v6 v7 v8
  = du_SRApp_328 v0 v1 v2 v4 v5 v6 v7 v8
du_SRApp_328 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_SRApp_328 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
        -> coe
             du_reflectSR_54 (coe v2)
             (coe
                MAlonzo.Code.Type.Equality.C_'183''8801'β_26
                (coe
                   du_reflectSR_54
                   (coe MAlonzo.Code.Utils.C__'8658'__708 (coe v1) (coe v2)) (coe v4))
                (coe du_reifySR_74 (coe v0) (coe v1) (coe v6) (coe v7)))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> coe
                           du_subSR_156 (coe v2)
                           (coe
                              MAlonzo.Code.Type.C__'183'__30 v1
                              (coe
                                 MAlonzo.Code.Type.C_ƛ_28
                                 (MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                                    (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v1))
                                    (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v1))
                                    (coe
                                       MAlonzo.Code.Type.RenamingSubstitution.du_ext_18
                                       (coe (\ v13 v14 -> v14)))
                                    (coe v2) (coe v9)))
                              v5)
                           (coe
                              MAlonzo.Code.Type.Equality.C_'183''8801'β_26
                              (coe
                                 MAlonzo.Code.Type.Equality.C_trans'8801'β_18
                                 (coe MAlonzo.Code.Type.C_ƛ_28 v9) v11
                                 (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76))
                              (coe MAlonzo.Code.Type.Equality.C_refl'8801'β_14))
                           (coe
                              MAlonzo.Code.Type.BetaNBE.d__'183'V__150 (coe v0) (coe v1) (coe v2)
                              (coe
                                 MAlonzo.Code.Type.BetaNBE.d_renVal_46
                                 (coe MAlonzo.Code.Utils.C__'8658'__708 (coe v1) (coe v2)) (coe v0)
                                 (coe v0) (coe (\ v13 v14 -> v14)) (coe v3))
                              (coe v6))
                           (coe v12 v0 (\ v13 v14 -> v14) v5 v6 v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.Soundness.evalSR
d_evalSR_358 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  AgdaAny
d_evalSR_358 v0 v1 v2 v3 v4 v5 v6
  = case coe v3 of
      MAlonzo.Code.Type.C_'96'_22 v9 -> coe v6 v2 v9
      MAlonzo.Code.Type.C_Π_24 v8 v9
        -> coe
             MAlonzo.Code.Type.Equality.C_Π'8801'β_22
             (d_evalSR_358
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v8))
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v8))
                (coe MAlonzo.Code.Utils.C_'42'_704) (coe v9)
                (coe
                   MAlonzo.Code.Type.RenamingSubstitution.du_exts_336 (coe v1)
                   (coe v4) (coe v8))
                (coe
                   MAlonzo.Code.Type.BetaNBE.du__'44''44''8902'__122
                   (coe
                      (\ v10 ->
                         let v11 = coe v5 v10 in
                         coe
                           (\ v12 ->
                              MAlonzo.Code.Type.BetaNBE.d_renVal_46
                                (coe v10) (coe v1)
                                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v8))
                                (coe (\ v13 -> coe MAlonzo.Code.Type.C_S_18)) (coe v11 v12))))
                   (coe MAlonzo.Code.Type.BetaNBE.du_fresh_38 (coe v8)))
                (coe du_SRweak_310 (coe v1) (coe v4) (coe v5) (coe v6) (coe v8)))
      MAlonzo.Code.Type.C__'8658'__26 v8 v9
        -> coe
             MAlonzo.Code.Type.Equality.C_'8658''8801'β_20
             (d_evalSR_358
                (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'42'_704) (coe v8)
                (coe v4) (coe v5) (coe v6))
             (d_evalSR_358
                (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'42'_704) (coe v9)
                (coe v4) (coe v5) (coe v6))
      MAlonzo.Code.Type.C_ƛ_28 v10
        -> case coe v2 of
             MAlonzo.Code.Utils.C__'8658'__708 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Type.RenamingSubstitution.d_sub_346
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v11))
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v11))
                       (coe
                          MAlonzo.Code.Type.RenamingSubstitution.du_exts_336 (coe v1)
                          (coe v4) (coe v11))
                       (coe v12) (coe v10))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Type.Equality.C_refl'8801'β_14)
                       (coe
                          (\ v13 v14 v15 v16 v17 ->
                             coe
                               du_subSR_156 (coe v12)
                               (coe
                                  MAlonzo.Code.Type.RenamingSubstitution.d_sub_346
                                  (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v11))
                                  (coe v13)
                                  (coe
                                     MAlonzo.Code.Type.RenamingSubstitution.du_sub'45'cons_420
                                     (coe
                                        (\ v18 v19 ->
                                           MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                                             (coe v1) (coe v13) (coe v14) (coe v18)
                                             (coe v4 v18 v19)))
                                     (coe v15))
                                  (coe v12) (coe v10))
                               (coe
                                  MAlonzo.Code.Type.Equality.C_trans'8801'β_18
                                  (MAlonzo.Code.Type.RenamingSubstitution.d__'91'_'93'_432
                                     (coe v13) (coe v11) (coe v12)
                                     (coe
                                        MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                                        (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v11))
                                        (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v13) (coe v11))
                                        (coe
                                           MAlonzo.Code.Type.RenamingSubstitution.du_ext_18
                                           (coe v14))
                                        (coe v12)
                                        (coe
                                           MAlonzo.Code.Type.RenamingSubstitution.d_sub_346
                                           (coe
                                              MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v11))
                                           (coe
                                              MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v11))
                                           (coe
                                              MAlonzo.Code.Type.RenamingSubstitution.du_exts_336
                                              (coe v1) (coe v4) (coe v11))
                                           (coe v12) (coe v10)))
                                     (coe v15))
                                  (coe MAlonzo.Code.Type.Equality.C_β'8801'β_48)
                                  (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76))
                               (coe
                                  MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v13)
                                  (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v11))
                                  (coe v12) (coe v10)
                                  (coe
                                     MAlonzo.Code.Type.BetaNBE.du__'44''44''8902'__122
                                     (coe
                                        (\ v18 v19 ->
                                           MAlonzo.Code.Type.BetaNBE.d_renVal_46
                                             (coe v18) (coe v1) (coe v13) (coe v14)
                                             (coe v5 v18 v19)))
                                     (coe v16)))
                               (coe
                                  d_evalSR_358
                                  (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v11))
                                  (coe v13) (coe v12) (coe v10)
                                  (coe
                                     MAlonzo.Code.Type.RenamingSubstitution.du_sub'45'cons_420
                                     (coe
                                        (\ v18 v19 ->
                                           MAlonzo.Code.Type.RenamingSubstitution.d_ren_28
                                             (coe v1) (coe v13) (coe v14) (coe v18)
                                             (coe v4 v18 v19)))
                                     (coe v15))
                                  (coe
                                     MAlonzo.Code.Type.BetaNBE.du__'44''44''8902'__122
                                     (coe
                                        (\ v18 v19 ->
                                           MAlonzo.Code.Type.BetaNBE.d_renVal_46
                                             (coe v18) (coe v1) (coe v13) (coe v14)
                                             (coe v5 v18 v19)))
                                     (coe v16))
                                  (coe
                                     du_SR'44''44''8902'_134
                                     (coe
                                        (\ v18 v19 ->
                                           d_renSR_202
                                             (coe v1) (coe v13) (coe v14) (coe v18) (coe v4 v18 v19)
                                             (coe v5 v18 v19) (coe v6 v18 v19)))
                                     (coe v17))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Type.C__'183'__30 v8 v10 v11
        -> coe
             du_SRApp_328 (coe v1) (coe v8) (coe v2)
             (coe
                MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v1) (coe v0)
                (coe MAlonzo.Code.Utils.C__'8658'__708 (coe v8) (coe v2)) (coe v10)
                (coe v5))
             (coe
                d_evalSR_358 (coe v0) (coe v1)
                (coe MAlonzo.Code.Utils.C__'8658'__708 (coe v8) (coe v2)) (coe v10)
                (coe v4) (coe v5) (coe v6))
             (coe
                MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v0) (coe v1)
                (coe v4) (coe v8) (coe v11))
             (coe
                MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v1) (coe v0) (coe v8)
                (coe v11) (coe v5))
             (coe
                d_evalSR_358 (coe v0) (coe v1) (coe v8) (coe v11) (coe v4) (coe v5)
                (coe v6))
      MAlonzo.Code.Type.C_μ_32 v8 v9 v10
        -> coe
             MAlonzo.Code.Type.Equality.C_μ'8801'β_28
             (coe
                du_reifySR_74 (coe v1)
                (coe
                   MAlonzo.Code.Utils.C__'8658'__708
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__708 (coe v8)
                      (coe MAlonzo.Code.Utils.C_'42'_704))
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__708 (coe v8)
                      (coe MAlonzo.Code.Utils.C_'42'_704)))
                (coe
                   MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v1) (coe v0)
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__708
                      (coe
                         MAlonzo.Code.Utils.C__'8658'__708 (coe v8)
                         (coe MAlonzo.Code.Utils.C_'42'_704))
                      (coe
                         MAlonzo.Code.Utils.C__'8658'__708 (coe v8)
                         (coe MAlonzo.Code.Utils.C_'42'_704)))
                   (coe v9) (coe v5))
                (coe
                   d_evalSR_358 (coe v0) (coe v1)
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__708
                      (coe
                         MAlonzo.Code.Utils.C__'8658'__708 (coe v8)
                         (coe MAlonzo.Code.Utils.C_'42'_704))
                      (coe
                         MAlonzo.Code.Utils.C__'8658'__708 (coe v8)
                         (coe MAlonzo.Code.Utils.C_'42'_704)))
                   (coe v9) (coe v4) (coe v5) (coe v6)))
             (coe
                du_reifySR_74 (coe v1) (coe v8)
                (coe
                   MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v1) (coe v0) (coe v8)
                   (coe v10) (coe v5))
                (coe
                   d_evalSR_358 (coe v0) (coe v1) (coe v8) (coe v10) (coe v4) (coe v5)
                   (coe v6)))
      MAlonzo.Code.Type.C_'94'_34 v9
        -> coe
             du_reflectSR_54 (coe v2)
             (coe MAlonzo.Code.Type.Equality.C_refl'8801'β_14)
      MAlonzo.Code.Type.C_con_36 v8
        -> coe
             MAlonzo.Code.Type.Equality.C_con'8801'β_34
             (d_evalSR_358
                (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'9839'_706) (coe v8)
                (coe v4) (coe v5) (coe v6))
      MAlonzo.Code.Type.C_SOP_40 v8 v9
        -> coe
             MAlonzo.Code.Type.Equality.C_SOP'8801'β_42
             (coe
                du_evalSR'45'VecList_384 (coe v0) (coe v1) (coe v9) (coe v4)
                (coe v5) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.Soundness.evalSR-List
d_evalSR'45'List_370 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  MAlonzo.Code.Type.Equality.T__'91''8801''93'β__4
d_evalSR'45'List_370 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      [] -> coe MAlonzo.Code.Type.Equality.C_nil'91''8801''93'β_50
      (:) v6 v7
        -> coe
             MAlonzo.Code.Type.Equality.C_cons'91''8801''93'β_60
             (d_evalSR_358
                (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'42'_704) (coe v6)
                (coe v3) (coe v4) (coe v5))
             (d_evalSR'45'List_370
                (coe v0) (coe v1) (coe v7) (coe v3) (coe v4) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.Soundness.evalSR-VecList
d_evalSR'45'VecList_384 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  MAlonzo.Code.Type.Equality.T__'10216''91''8801''93''10217'β__8
d_evalSR'45'VecList_384 v0 v1 ~v2 v3 v4 v5 v6
  = du_evalSR'45'VecList_384 v0 v1 v3 v4 v5 v6
du_evalSR'45'VecList_384 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  MAlonzo.Code.Type.Equality.T__'10216''91''8801''93''10217'β__8
du_evalSR'45'VecList_384 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
        -> coe
             MAlonzo.Code.Type.Equality.C_nil'10216''91''8801''93''10217'β_62
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v7 v8
        -> coe
             MAlonzo.Code.Type.Equality.C_cons'10216''91''8801''93''10217'β_74
             (d_evalSR'45'List_370
                (coe v0) (coe v1) (coe v7) (coe v3) (coe v4) (coe v5))
             (coe
                du_evalSR'45'VecList_384 (coe v0) (coe v1) (coe v8) (coe v3)
                (coe v4) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.Soundness.idSR
d_idSR_462 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny
d_idSR_462 ~v0 v1 ~v2 = du_idSR_462 v1
du_idSR_462 :: MAlonzo.Code.Utils.T_Kind_702 -> AgdaAny
du_idSR_462 v0
  = coe
      du_reflectSR_54 (coe v0)
      (coe MAlonzo.Code.Type.Equality.C_refl'8801'β_14)
-- Type.BetaNBE.Soundness.soundness
d_soundness_470 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.Equality.T__'8801'β__10
d_soundness_470 v0 v1 v2
  = coe
      MAlonzo.Code.Type.Equality.C_trans'8801'β_18
      (MAlonzo.Code.Type.RenamingSubstitution.d_sub_346
         (coe v0) (coe v0) (\ v3 v4 -> coe MAlonzo.Code.Type.C_'96'_22 v4)
         (coe v1) (coe v2))
      (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76)
      (coe
         du_reifySR_74 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v0) (coe v0) (coe v1)
            (coe v2) (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250))
         (coe
            d_evalSR_358 (coe v0) (coe v0) (coe v1) (coe v2)
            (\ v3 v4 -> coe MAlonzo.Code.Type.C_'96'_22 v4)
            (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)
            (\ v3 v4 -> coe du_idSR_462 v3)))
