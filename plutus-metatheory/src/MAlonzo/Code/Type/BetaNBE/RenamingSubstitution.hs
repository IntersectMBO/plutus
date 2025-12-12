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

module MAlonzo.Code.Type.BetaNBE.RenamingSubstitution where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.BetaNBE
import qualified MAlonzo.Code.Type.BetaNBE.Completeness
import qualified MAlonzo.Code.Type.BetaNormal
import qualified MAlonzo.Code.Type.Equality
import qualified MAlonzo.Code.Type.RenamingSubstitution
import qualified MAlonzo.Code.Utils

-- Type.BetaNBE.RenamingSubstitution.reify-reflect
d_reify'45'reflect_12 ::
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Ne'8902'__6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reify'45'reflect_12 = erased
-- Type.BetaNBE.RenamingSubstitution.evalCRSubst
d_evalCRSubst_38 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_evalCRSubst_38 v0 v1 v2 v3 v4 v5 v6 v7 ~v8
  = du_evalCRSubst_38 v0 v1 v2 v3 v4 v5 v6 v7
du_evalCRSubst_38 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 -> AgdaAny
du_evalCRSubst_38 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Type.BetaNBE.Completeness.d_fund_1482 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
      (coe MAlonzo.Code.Type.Equality.du_'8801'2β_76)
-- Type.BetaNBE.RenamingSubstitution.ren-nf
d_ren'45'nf_56 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'nf_56 = erased
-- Type.BetaNBE.RenamingSubstitution.ren-nf-μ
d_ren'45'nf'45'μ_74 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'nf'45'μ_74 = erased
-- Type.BetaNBE.RenamingSubstitution.SubNf
d_SubNf_90 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 -> ()
d_SubNf_90 = erased
-- Type.BetaNBE.RenamingSubstitution.subNf
d_subNf_104 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_subNf_104 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Type.BetaNBE.d_nf_258 (coe v1) (coe v3)
      (coe
         MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v0) (coe v1)
         (coe
            (\ v5 v6 ->
               MAlonzo.Code.Type.BetaNormal.d_embNf_128
                 (coe v1) (coe v5) (coe v2 v5 v6)))
         (coe v3)
         (coe
            MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0) (coe v3)
            (coe v4)))
-- Type.BetaNBE.RenamingSubstitution.subNf-id
d_subNf'45'id_116 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subNf'45'id_116 = erased
-- Type.BetaNBE.RenamingSubstitution.subNf-id'
d_subNf'45'id''_126 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subNf'45'id''_126 = erased
-- Type.BetaNBE.RenamingSubstitution.subNf-∋
d_subNf'45''8715'_142 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subNf'45''8715'_142 = erased
-- Type.BetaNBE.RenamingSubstitution.subNf-nf
d_subNf'45'nf_160 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subNf'45'nf_160 = erased
-- Type.BetaNBE.RenamingSubstitution.subNf-comp
d_subNf'45'comp_182 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subNf'45'comp_182 = erased
-- Type.BetaNBE.RenamingSubstitution.extsNf
d_extsNf_198 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_extsNf_198 ~v0 v1 v2 v3 v4 v5 = du_extsNf_198 v1 v2 v3 v4 v5
du_extsNf_198 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
du_extsNf_198 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Type.C_Z_16
        -> coe
             MAlonzo.Code.Type.BetaNormal.C_ne_20
             (coe
                MAlonzo.Code.Type.BetaNormal.C_'96'_8
                (coe MAlonzo.Code.Type.C_Z_16))
      MAlonzo.Code.Type.C_S_18 v8
        -> coe
             MAlonzo.Code.Type.BetaNormal.d_weakenNf_122 v0 v3 v2 (coe v1 v3 v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.RenamingSubstitution.subNf-cons
d_subNf'45'cons_218 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_subNf'45'cons_218 ~v0 ~v1 v2 ~v3 v4 v5 v6
  = du_subNf'45'cons_218 v2 v4 v5 v6
du_subNf'45'cons_218 ::
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.T__'8715''8902'__14 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
du_subNf'45'cons_218 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Type.C_Z_16 -> coe v1
      MAlonzo.Code.Type.C_S_18 v7 -> coe v0 v2 v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.RenamingSubstitution._[_]Nf
d__'91'_'93'Nf_236 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d__'91'_'93'Nf_236 v0 v1 v2 v3 v4
  = coe
      d_subNf_104
      (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v2)) (coe v0)
      (coe
         du_subNf'45'cons_218
         (coe
            (\ v5 v6 ->
               coe
                 MAlonzo.Code.Type.BetaNormal.C_ne_20
                 (coe MAlonzo.Code.Type.BetaNormal.C_'96'_8 v6)))
         (coe v4))
      (coe v1) (coe v3)
-- Type.BetaNBE.RenamingSubstitution.subNf-cong
d_subNf'45'cong_260 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subNf'45'cong_260 = erased
-- Type.BetaNBE.RenamingSubstitution.subNf-cong'
d_subNf'45'cong''_280 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subNf'45'cong''_280 = erased
-- Type.BetaNBE.RenamingSubstitution.renNf-subNf
d_renNf'45'subNf_300 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renNf'45'subNf_300 = erased
-- Type.BetaNBE.RenamingSubstitution.subNf-renNf
d_subNf'45'renNf_324 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subNf'45'renNf_324 = erased
-- Type.BetaNBE.RenamingSubstitution.ren[]Nf
d_ren'91''93'Nf_350 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'91''93'Nf_350 = erased
-- Type.BetaNBE.RenamingSubstitution.sub[]Nf
d_sub'91''93'Nf_378 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'91''93'Nf_378 = erased
-- Type.BetaNBE.RenamingSubstitution.subNf-lemma
d_subNf'45'lemma_404 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subNf'45'lemma_404 = erased
-- Type.BetaNBE.RenamingSubstitution.subNf-lemma'
d_subNf'45'lemma''_422 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subNf'45'lemma''_422 = erased
-- Type.BetaNBE.RenamingSubstitution.sub[]Nf'
d_sub'91''93'Nf''_446 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'91''93'Nf''_446 = erased
-- Type.BetaNBE.RenamingSubstitution.weakenNf-renNf
d_weakenNf'45'renNf_464 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_weakenNf'45'renNf_464 = erased
-- Type.BetaNBE.RenamingSubstitution.weakenNf-subNf
d_weakenNf'45'subNf_480 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_weakenNf'45'subNf_480 = erased
-- Type.BetaNBE.RenamingSubstitution.weakenNf[]
d_weakenNf'91''93'_494 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_weakenNf'91''93'_494 = erased
-- Type.BetaNBE.RenamingSubstitution.sub-nf-Π
d_sub'45'nf'45'Π_510 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'nf'45'Π_510 = erased
-- Type.BetaNBE.RenamingSubstitution.sub-nf-μ
d_sub'45'nf'45'μ_528 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sub'45'nf'45'μ_528 = erased
-- Type.BetaNBE.RenamingSubstitution.subNf-cons-[]Nf
d_subNf'45'cons'45''91''93'Nf_548 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subNf'45'cons'45''91''93'Nf_548 = erased
-- Type.BetaNBE.RenamingSubstitution.subNf∅
d_subNf'8709'_566 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_subNf'8709'_566 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Type.C_'8709'_4 -> coe v2
      MAlonzo.Code.Type.C__'44''8902'__6 v3 v4
        -> coe
             d_subNf_104 (coe MAlonzo.Code.Type.C_'8709'_4) (coe v0) erased
             (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNBE.RenamingSubstitution.subNf∅≡subNf
d_subNf'8709''8801'subNf_582 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subNf'8709''8801'subNf_582 = erased
-- Type.BetaNBE.RenamingSubstitution.subNf∅-renNf
d_subNf'8709''45'renNf_600 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subNf'8709''45'renNf_600 = erased
-- Type.BetaNBE.RenamingSubstitution.subNf∅-subNf
d_subNf'8709''45'subNf_616 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subNf'8709''45'subNf_616 = erased
