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

module MAlonzo.Code.Type.BetaNBE where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.BetaNormal
import qualified MAlonzo.Code.Utils

-- Type.BetaNBE.Val
d_Val_4 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 -> ()
d_Val_4 = erased
-- Type.BetaNBE.reflect
d_reflect_22 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Ne'8902'__6 -> AgdaAny
d_reflect_22 ~v0 v1 v2 = du_reflect_22 v1 v2
du_reflect_22 ::
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Ne'8902'__6 -> AgdaAny
du_reflect_22 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C_'42'_704
        -> coe MAlonzo.Code.Type.BetaNormal.C_ne_20 v1
      MAlonzo.Code.Utils.C_'9839'_706
        -> coe MAlonzo.Code.Type.BetaNormal.C_ne_20 v1
      MAlonzo.Code.Utils.C__'8658'__708 v2 v3
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.fresh
d_fresh_38 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 -> AgdaAny
d_fresh_38 ~v0 v1 = du_fresh_38 v1
du_fresh_38 :: MAlonzo.Code.Utils.T_Kind_702 -> AgdaAny
du_fresh_38 v0
  = coe
      du_reflect_22 (coe v0)
      (coe
         MAlonzo.Code.Type.BetaNormal.C_'96'_8
         (coe MAlonzo.Code.Type.C_Z_16))
-- Type.BetaNBE.renVal
d_renVal_46 ::
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  AgdaAny -> AgdaAny
d_renVal_46 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Utils.C_'42'_704
        -> coe
             MAlonzo.Code.Type.BetaNormal.d_renNf_46 (coe v1) (coe v2) (coe v3)
             (coe v0) (coe v4)
      MAlonzo.Code.Utils.C_'9839'_706
        -> coe
             MAlonzo.Code.Type.BetaNormal.d_renNf_46 (coe v1) (coe v2) (coe v3)
             (coe v0) (coe v4)
      MAlonzo.Code.Utils.C__'8658'__708 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe
                       MAlonzo.Code.Type.BetaNormal.d_renNe_48 (coe v1) (coe v2) (coe v3)
                       (coe v0) (coe v7))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       (\ v8 v9 -> coe v7 v8 (\ v10 v11 -> coe v9 v10 (coe v3 v10 v11))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.weakenVal
d_weakenVal_80 ::
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 -> AgdaAny -> AgdaAny
d_weakenVal_80 v0 v1 v2
  = coe
      d_renVal_46 (coe v0) (coe v1)
      (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v2))
      (coe (\ v3 -> coe MAlonzo.Code.Type.C_S_18))
-- Type.BetaNBE.reify
d_reify_86 ::
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  AgdaAny -> MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_reify_86 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Utils.C_'42'_704 -> coe v2
      MAlonzo.Code.Utils.C_'9839'_706 -> coe v2
      MAlonzo.Code.Utils.C__'8658'__708 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe MAlonzo.Code.Type.BetaNormal.C_ne_20 v5
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Type.BetaNormal.C_ƛ_18
                    (d_reify_86
                       (coe v4) (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v3))
                       (coe
                          v5 (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v3))
                          (\ v6 -> coe MAlonzo.Code.Type.C_S_18) (coe du_fresh_38 (coe v3))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.Env
d_Env_104 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 -> ()
d_Env_104 = erased
-- Type.BetaNBE._,,⋆_
d__'44''44''8902'__122 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  AgdaAny ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny
d__'44''44''8902'__122 ~v0 ~v1 v2 ~v3 v4 v5 v6
  = du__'44''44''8902'__122 v2 v4 v5 v6
du__'44''44''8902'__122 ::
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny
du__'44''44''8902'__122 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Type.C_Z_16 -> coe v1
      MAlonzo.Code.Type.C_S_18 v7 -> coe v0 v2 v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.exte
d_exte_140 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny
d_exte_140 ~v0 v1 v2 v3 v4 = du_exte_140 v1 v2 v3 v4
du_exte_140 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny
du_exte_140 v0 v1 v2 v3
  = coe
      du__'44''44''8902'__122
      (coe (\ v4 v5 -> coe d_weakenVal_80 v4 v0 v2 (coe v1 v4 v5)))
      (coe du_fresh_38 (coe v2)) (coe v3)
-- Type.BetaNBE._·V_
d__'183'V__150 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> AgdaAny
d__'183'V__150 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
        -> coe
             du_reflect_22 (coe v2)
             (coe
                MAlonzo.Code.Type.BetaNormal.C__'183'__10 v1 v5
                (d_reify_86 (coe v1) (coe v0) (coe v4)))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> coe v5 v0 (\ v6 v7 -> v7) v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.eval
d_eval_166 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  AgdaAny
d_eval_166 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Type.C_'96'_22 v7 -> coe v4 v2 v7
      MAlonzo.Code.Type.C_Π_24 v6 v7
        -> coe
             MAlonzo.Code.Type.BetaNormal.C_Π_14 v6
             (d_reify_86
                (coe MAlonzo.Code.Utils.C_'42'_704)
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v6))
                (coe
                   d_eval_166
                   (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v6))
                   (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v6))
                   (coe MAlonzo.Code.Utils.C_'42'_704) (coe v7)
                   (coe du_exte_140 (coe v0) (coe v4) (coe v6))))
      MAlonzo.Code.Type.C__'8658'__26 v6 v7
        -> coe
             MAlonzo.Code.Type.BetaNormal.C__'8658'__16
             (d_reify_86
                (coe MAlonzo.Code.Utils.C_'42'_704) (coe v0)
                (coe
                   d_eval_166 (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'42'_704)
                   (coe v6) (coe v4)))
             (d_reify_86
                (coe MAlonzo.Code.Utils.C_'42'_704) (coe v0)
                (coe
                   d_eval_166 (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'42'_704)
                   (coe v7) (coe v4)))
      MAlonzo.Code.Type.C_ƛ_28 v8
        -> case coe v2 of
             MAlonzo.Code.Utils.C__'8658'__708 v9 v10
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       (\ v11 v12 v13 ->
                          d_eval_166
                            (coe v11)
                            (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v9))
                            (coe v10) (coe v8)
                            (coe
                               du__'44''44''8902'__122
                               (coe
                                  (\ v14 v15 ->
                                     d_renVal_46
                                       (coe v14) (coe v0) (coe v11) (coe v12) (coe v4 v14 v15)))
                               (coe v13))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Type.C__'183'__30 v6 v8 v9
        -> coe
             d__'183'V__150 (coe v0) (coe v6) (coe v2)
             (coe
                d_eval_166 (coe v0) (coe v1)
                (coe MAlonzo.Code.Utils.C__'8658'__708 (coe v6) (coe v2)) (coe v8)
                (coe v4))
             (coe d_eval_166 (coe v0) (coe v1) (coe v6) (coe v9) (coe v4))
      MAlonzo.Code.Type.C_μ_32 v6 v7 v8
        -> coe
             MAlonzo.Code.Type.BetaNormal.C_μ_24 v6
             (d_reify_86
                (coe
                   MAlonzo.Code.Utils.C__'8658'__708
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__708 (coe v6)
                      (coe MAlonzo.Code.Utils.C_'42'_704))
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__708 (coe v6)
                      (coe MAlonzo.Code.Utils.C_'42'_704)))
                (coe v0)
                (coe
                   d_eval_166 (coe v0) (coe v1)
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__708
                      (coe
                         MAlonzo.Code.Utils.C__'8658'__708 (coe v6)
                         (coe MAlonzo.Code.Utils.C_'42'_704))
                      (coe
                         MAlonzo.Code.Utils.C__'8658'__708 (coe v6)
                         (coe MAlonzo.Code.Utils.C_'42'_704)))
                   (coe v7) (coe v4)))
             (d_reify_86
                (coe v6) (coe v0)
                (coe d_eval_166 (coe v0) (coe v1) (coe v6) (coe v8) (coe v4)))
      MAlonzo.Code.Type.C_'94'_34 v7
        -> coe
             du_reflect_22 (coe v2)
             (coe MAlonzo.Code.Type.BetaNormal.C_'94'_12 v7)
      MAlonzo.Code.Type.C_con_36 v6
        -> coe
             MAlonzo.Code.Type.BetaNormal.C_con_22
             (d_eval_166
                (coe v0) (coe v1) (coe MAlonzo.Code.Utils.C_'9839'_706) (coe v6)
                (coe v4))
      MAlonzo.Code.Type.C_SOP_40 v6 v7
        -> coe
             MAlonzo.Code.Type.BetaNormal.C_SOP_28 v6
             (coe
                du_eval'45'VecList_184 (coe v0) (coe v1)
                (coe MAlonzo.Code.Utils.C_'42'_704) (coe v7) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.eval-List
d_eval'45'List_174 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  [AgdaAny]
d_eval'45'List_174 v0 v1 v2 v3 v4
  = case coe v3 of
      [] -> coe v3
      (:) v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_eval_166 (coe v0) (coe v1) (coe v2) (coe v5) (coe v4))
             (coe
                d_eval'45'List_174 (coe v0) (coe v1) (coe v2) (coe v6) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.eval-VecList
d_eval'45'VecList_184 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_eval'45'VecList_184 v0 v1 v2 ~v3 v4 v5
  = du_eval'45'VecList_184 v0 v1 v2 v4 v5
du_eval'45'VecList_184 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_eval'45'VecList_184 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe v3
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
        -> coe
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38
             (d_eval'45'List_174 (coe v0) (coe v1) (coe v2) (coe v6) (coe v4))
             (coe
                du_eval'45'VecList_184 (coe v0) (coe v1) (coe v2) (coe v7)
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.idEnv
d_idEnv_250 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny
d_idEnv_250 ~v0 v1 v2 = du_idEnv_250 v1 v2
du_idEnv_250 ::
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny
du_idEnv_250 v0 v1
  = coe
      du_reflect_22 (coe v0)
      (coe MAlonzo.Code.Type.BetaNormal.C_'96'_8 v1)
-- Type.BetaNBE.nf
d_nf_258 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_nf_258 v0 v1 v2
  = coe
      d_reify_86 (coe v1) (coe v0)
      (coe
         d_eval_166 (coe v0) (coe v0) (coe v1) (coe v2) (coe du_idEnv_250))
-- Type.BetaNBE.nf-VecList
d_nf'45'VecList_268 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_nf'45'VecList_268 v0 v1 ~v2 v3 = du_nf'45'VecList_268 v0 v1 v3
du_nf'45'VecList_268 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_nf'45'VecList_268 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Vec.Base.du_map_178
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe d_reify_86 (coe v1) (coe v0)))
      (coe
         du_eval'45'VecList_184 (coe v0) (coe v0) (coe v1) (coe v2)
         (coe du_idEnv_250))
-- Type.BetaNBE._.lookup-eval-VecList
d_lookup'45'eval'45'VecList_288 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'eval'45'VecList_288 = erased
