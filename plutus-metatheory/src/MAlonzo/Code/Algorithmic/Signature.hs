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

module MAlonzo.Code.Algorithmic.Signature where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Builtin.Signature
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.BetaNBE
import qualified MAlonzo.Code.Type.BetaNBE.RenamingSubstitution
import qualified MAlonzo.Code.Type.BetaNormal
import qualified MAlonzo.Code.Type.RenamingSubstitution
import qualified MAlonzo.Code.Utils

-- Algorithmic.Signature._.SigTy
d_SigTy_6 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Algorithmic.Signature._.convSigTy
d_convSigTy_8 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266
d_convSigTy_8 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 ~v14 v15
  = du_convSigTy_8 v15
du_convSigTy_8 ::
  MAlonzo.Code.Builtin.Signature.T_SigTy_266 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266
du_convSigTy_8 v0 = coe v0
-- Algorithmic.Signature._.mkTy
d_mkTy_10 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Builtin.Signature.T__'47'_'8866''8902'_26 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_mkTy_10
  = coe
      MAlonzo.Code.Builtin.Signature.du_mkTy_204
      (\ v0 v1 v2 -> coe MAlonzo.Code.Type.BetaNormal.C_ne_20 v2)
      (coe
         (\ v0 v1 v2 v3 -> coe MAlonzo.Code.Type.BetaNormal.C_'96'_8 v3))
      (\ v0 v1 v2 v3 v4 ->
         coe MAlonzo.Code.Type.BetaNormal.C__'183'__10 v1 v3 v4)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Type.BetaNormal.C_'94'_12))
      (\ v0 v1 -> coe MAlonzo.Code.Type.BetaNormal.C_con_22 v1)
-- Algorithmic.Signature._.sig2type
d_sig2type_12 ::
  MAlonzo.Code.Builtin.Signature.T_Sig_72 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_sig2type_12
  = coe
      MAlonzo.Code.Builtin.Signature.du_sig2type_242
      (\ v0 v1 v2 -> coe MAlonzo.Code.Type.BetaNormal.C_ne_20 v2)
      (coe
         (\ v0 v1 v2 v3 -> coe MAlonzo.Code.Type.BetaNormal.C_'96'_8 v3))
      (\ v0 v1 v2 v3 v4 ->
         coe MAlonzo.Code.Type.BetaNormal.C__'183'__10 v1 v3 v4)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Type.BetaNormal.C_'94'_12))
      (\ v0 v1 -> coe MAlonzo.Code.Type.BetaNormal.C_con_22 v1)
      (\ v0 v1 v2 ->
         coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v1 v2)
      (\ v0 v1 v2 -> coe MAlonzo.Code.Type.BetaNormal.C_Π_14 v1 v2)
-- Algorithmic.Signature._.sig2typeΠ
d_sig2typeΠ_14 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_sig2typeΠ_14
  = coe
      MAlonzo.Code.Builtin.Signature.du_sig2typeΠ_228
      (\ v0 v1 v2 -> coe MAlonzo.Code.Type.BetaNormal.C_Π_14 v1 v2)
-- Algorithmic.Signature._.sig2type⇒
d_sig2type'8658'_16 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Builtin.Signature.T__'47'_'8866''8902'_26] ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_sig2type'8658'_16
  = coe
      MAlonzo.Code.Builtin.Signature.du_sig2type'8658'_214
      (\ v0 v1 v2 -> coe MAlonzo.Code.Type.BetaNormal.C_ne_20 v2)
      (coe
         (\ v0 v1 v2 v3 -> coe MAlonzo.Code.Type.BetaNormal.C_'96'_8 v3))
      (\ v0 v1 v2 v3 v4 ->
         coe MAlonzo.Code.Type.BetaNormal.C__'183'__10 v1 v3 v4)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Type.BetaNormal.C_'94'_12))
      (\ v0 v1 -> coe MAlonzo.Code.Type.BetaNormal.C_con_22 v1)
      (\ v0 v1 v2 ->
         coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v1 v2)
-- Algorithmic.Signature._.sigTy2type
d_sigTy2type_18 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_sigTy2type_18 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_sigTy2type_18 v7
du_sigTy2type_18 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
du_sigTy2type_18 v0 = coe v0
-- Algorithmic.Signature._.⊢♯2TyNe♯
d_'8866''9839'2TyNe'9839'_20 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Ne'8902'__6
d_'8866''9839'2TyNe'9839'_20
  = coe
      MAlonzo.Code.Builtin.Signature.du_'8866''9839'2TyNe'9839'_186
      (\ v0 v1 v2 -> coe MAlonzo.Code.Type.BetaNormal.C_ne_20 v2)
      (coe
         (\ v0 v1 v2 v3 -> coe MAlonzo.Code.Type.BetaNormal.C_'96'_8 v3))
      (\ v0 v1 v2 v3 v4 ->
         coe MAlonzo.Code.Type.BetaNormal.C__'183'__10 v1 v3 v4)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Type.BetaNormal.C_'94'_12))
-- Algorithmic.Signature.btype
d_btype_30 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_btype_30 v0 v1
  = coe
      MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.d_subNf'8709'_566
      (coe v0) (coe MAlonzo.Code.Utils.C_'42'_704)
      (coe
         MAlonzo.Code.Builtin.Signature.du_sig2type_242
         (\ v2 v3 v4 -> coe MAlonzo.Code.Type.BetaNormal.C_ne_20 v4)
         (coe
            (\ v2 v3 v4 v5 -> coe MAlonzo.Code.Type.BetaNormal.C_'96'_8 v5))
         (\ v2 v3 v4 v5 v6 ->
            coe MAlonzo.Code.Type.BetaNormal.C__'183'__10 v3 v5 v6)
         (coe (\ v2 v3 -> coe MAlonzo.Code.Type.BetaNormal.C_'94'_12))
         (\ v2 v3 -> coe MAlonzo.Code.Type.BetaNormal.C_con_22 v3)
         (\ v2 v3 v4 ->
            coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v3 v4)
         (\ v2 v3 v4 -> coe MAlonzo.Code.Type.BetaNormal.C_Π_14 v3 v4)
         (coe MAlonzo.Code.Builtin.d_signature_302 (coe v1)))
-- Algorithmic.Signature.btype-ren
d_btype'45'ren_42 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_btype'45'ren_42 = erased
-- Algorithmic.Signature.btype-sub
d_btype'45'sub_56 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_btype'45'sub_56 = erased
-- Algorithmic.Signature.subNf-Π
d_subNf'45'Π_72 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subNf'45'Π_72 = erased
-- Algorithmic.Signature.subSigTy
d_subSigTy_108 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266
d_subSigTy_108 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
  = du_subSigTy_108 v0 v1 v2 v12
du_subSigTy_108 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_702 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4) ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266
du_subSigTy_108 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Builtin.Signature.C_bresult_280
        -> coe MAlonzo.Code.Builtin.Signature.C_bresult_280
      MAlonzo.Code.Builtin.Signature.C__B'8658'__302 v12 v13 v14
        -> coe
             MAlonzo.Code.Builtin.Signature.C__B'8658'__302
             (MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.d_subNf_104
                (coe v0) (coe v1) (coe v2) (coe MAlonzo.Code.Utils.C_'42'_704)
                (coe v12))
             (MAlonzo.Code.Type.BetaNBE.d_reify_86
                (coe MAlonzo.Code.Utils.C_'42'_704) (coe v1)
                (coe
                   MAlonzo.Code.Type.BetaNBE.d_eval_166 (coe v1) (coe v1)
                   (coe MAlonzo.Code.Utils.C_'42'_704)
                   (coe
                      MAlonzo.Code.Type.RenamingSubstitution.d_sub_346 (coe v0) (coe v1)
                      (coe
                         (\ v15 v16 ->
                            MAlonzo.Code.Type.BetaNormal.d_embNf_128
                              (coe v1) (coe v15) (coe v2 v15 v16)))
                      (coe MAlonzo.Code.Utils.C_'42'_704)
                      (coe
                         MAlonzo.Code.Type.BetaNormal.d_embNf_128 (coe v0)
                         (coe MAlonzo.Code.Utils.C_'42'_704) (coe v13)))
                   (coe MAlonzo.Code.Type.BetaNBE.du_idEnv_250)))
             (coe du_subSigTy_108 (coe v0) (coe v1) (coe v2) (coe v14))
      MAlonzo.Code.Builtin.Signature.C_sucΠ_326 v13 v14 v15
        -> coe
             MAlonzo.Code.Builtin.Signature.C_sucΠ_326 v13
             (MAlonzo.Code.Type.BetaNBE.d_eval_166
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v13))
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v13))
                (coe MAlonzo.Code.Utils.C_'42'_704)
                (coe
                   MAlonzo.Code.Type.RenamingSubstitution.d_sub_346
                   (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v13))
                   (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v13))
                   (coe
                      (\ v16 v17 ->
                         MAlonzo.Code.Type.BetaNormal.d_embNf_128
                           (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v13))
                           (coe v16)
                           (coe
                              MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.du_extsNf_198
                              (coe v1) (coe v2) (coe v13) (coe v16) (coe v17))))
                   (coe MAlonzo.Code.Utils.C_'42'_704)
                   (coe
                      MAlonzo.Code.Type.BetaNormal.d_embNf_128
                      (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v13))
                      (coe MAlonzo.Code.Utils.C_'42'_704) (coe v14)))
                (coe
                   (\ v16 v17 ->
                      coe
                        MAlonzo.Code.Type.BetaNBE.du_reflect_22 (coe v16)
                        (coe MAlonzo.Code.Type.BetaNormal.C_'96'_8 v17))))
             (coe
                du_subSigTy_108
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v13))
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v13))
                (coe
                   MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.du_extsNf_198
                   (coe v1) (coe v2) (coe v13))
                (coe v15))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.Signature._[_]SigTy
d__'91'_'93'SigTy_150 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266
d__'91'_'93'SigTy_150 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11 v12
  = du__'91'_'93'SigTy_150 v0 v1 v11 v12
du__'91'_'93'SigTy_150 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266
du__'91'_'93'SigTy_150 v0 v1 v2 v3
  = coe
      du_subSigTy_108
      (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v1)) (coe v0)
      (coe
         MAlonzo.Code.Type.BetaNBE.RenamingSubstitution.du_subNf'45'cons_218
         (coe
            (\ v4 v5 ->
               coe
                 MAlonzo.Code.Type.BetaNormal.C_ne_20
                 (coe MAlonzo.Code.Type.BetaNormal.C_'96'_8 v5)))
         (coe v3))
      (coe v2)
-- Algorithmic.Signature.uniqueSigTy
d_uniqueSigTy_180 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_266 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uniqueSigTy_180 = erased
