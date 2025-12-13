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

module MAlonzo.Code.Algorithmic where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Builtin.Constant.Type
import qualified MAlonzo.Code.Builtin.Signature
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.BetaNormal
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.Utils.List

-- Algorithmic.Ctx
d_Ctx_2 a0 = ()
data T_Ctx_2
  = C_'8709'_4 | C__'44''8902'__8 T_Ctx_2 |
    C__'44'__12 T_Ctx_2
                MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
-- Algorithmic._∋_
d__'8715'__16 a0 a1 a2 = ()
data T__'8715'__16
  = C_Z_22 | C_S_30 T__'8715'__16 |
    C_T_38 MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
           T__'8715'__16
-- Algorithmic.♯Kinded
d_'9839'Kinded_40 a0 = ()
data T_'9839'Kinded_40
  = C_'9839'_42 | C_K'9839'_48 T_'9839'Kinded_40
-- Algorithmic.lemma♯Kinded
d_lemma'9839'Kinded_58 ::
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  MAlonzo.Code.Utils.T_Kind_702 ->
  T_'9839'Kinded_40 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Ne'8902'__6 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_lemma'9839'Kinded_58 = erased
-- Algorithmic.ty2sty
d_ty2sty_64 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4
d_ty2sty_64 v0
  = case coe v0 of
      MAlonzo.Code.Type.BetaNormal.C_ne_20 v3
        -> case coe v3 of
             MAlonzo.Code.Type.BetaNormal.C__'183'__10 v5 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Type.BetaNormal.C__'183'__10 v10 v12 v13
                      -> case coe v12 of
                           MAlonzo.Code.Type.BetaNormal.C_'94'_12 v16
                             -> coe
                                  seq (coe v16)
                                  (coe
                                     MAlonzo.Code.Builtin.Signature.C_pair_24
                                     (d_ty2sty_64 (coe v13)) (d_ty2sty_64 (coe v8)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Type.BetaNormal.C_'94'_12 v11
                      -> case coe v11 of
                           MAlonzo.Code.Builtin.Constant.Type.C_list_10
                             -> coe
                                  MAlonzo.Code.Builtin.Signature.C_list_16 (d_ty2sty_64 (coe v8))
                           MAlonzo.Code.Builtin.Constant.Type.C_array_12
                             -> coe
                                  MAlonzo.Code.Builtin.Signature.C_array_20 (d_ty2sty_64 (coe v8))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Type.BetaNormal.C_'94'_12 v6
               -> case coe v6 of
                    MAlonzo.Code.Builtin.Constant.Type.C_atomic_8 v7
                      -> coe MAlonzo.Code.Builtin.Signature.C_atomic_12 v7
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.sty2ty
d_sty2ty_84 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_sty2ty_84 v0
  = coe
      MAlonzo.Code.Type.BetaNormal.C_ne_20
      (coe
         MAlonzo.Code.Builtin.Signature.du_'8866''9839'2TyNe'9839'_186
         (\ v1 v2 v3 -> coe MAlonzo.Code.Type.BetaNormal.C_ne_20 v3)
         (coe
            (\ v1 v2 v3 v4 -> coe MAlonzo.Code.Type.BetaNormal.C_'96'_8 v4))
         (\ v1 v2 v3 v4 v5 ->
            coe MAlonzo.Code.Type.BetaNormal.C__'183'__10 v2 v4 v5)
         (coe (\ v1 v2 -> coe MAlonzo.Code.Type.BetaNormal.C_'94'_12))
         (coe (0 :: Integer)) (coe (0 :: Integer)) (coe v0))
-- Algorithmic.ty≅sty₁
d_ty'8773'sty'8321'_90 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ty'8773'sty'8321'_90 = erased
-- Algorithmic.ty≅sty₂
d_ty'8773'sty'8322'_118 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ty'8773'sty'8322'_118 = erased
-- Algorithmic.⟦_⟧
d_'10214'_'10215'_132 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 -> ()
d_'10214'_'10215'_132 = erased
-- Algorithmic.mkCaseType
d_mkCaseType_156 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_mkCaseType_156 ~v0 v1 = du_mkCaseType_156 v1
du_mkCaseType_156 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
du_mkCaseType_156 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16) (coe v0)
-- Algorithmic.ConstrArgs
d_ConstrArgs_162 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  T_Ctx_2 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] -> ()
d_ConstrArgs_162 = erased
-- Algorithmic.Cases
d_Cases_172 a0 a1 a2 a3 a4 = ()
data T_Cases_172
  = C_'91''93'_278 | C__'8759'__290 T__'8866'__178 T_Cases_172
-- Algorithmic._⊢_
d__'8866'__178 a0 a1 a2 = ()
data T__'8866'__178
  = C_'96'_184 T__'8715'__16 | C_ƛ_190 T__'8866'__178 |
    C__'183'__196 MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
                  T__'8866'__178 T__'8866'__178 |
    C_Λ_202 T__'8866'__178 |
    C__'183''8902'_'47'__212 MAlonzo.Code.Utils.T_Kind_702
                             MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 T__'8866'__178
                             MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 |
    C_wrap_220 T__'8866'__178 |
    C_unwrap_230 MAlonzo.Code.Utils.T_Kind_702
                 MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
                 MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 T__'8866'__178 |
    C_constr_240 MAlonzo.Code.Data.Fin.Base.T_Fin_10
                 [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4]
                 MAlonzo.Code.Utils.List.T_IList_302 |
    C_case_252 Integer MAlonzo.Code.Data.Vec.Base.T_Vec_28
               T__'8866'__178 T_Cases_172 |
    C_con_258 MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
              AgdaAny |
    C_builtin_'47'__264 MAlonzo.Code.Builtin.T_Builtin_2 | C_error_268
-- Algorithmic.conv∋
d_conv'8715'_300 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  T_Ctx_2 ->
  T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8715'__16 -> T__'8715'__16
d_conv'8715'_300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_conv'8715'_300 v7
du_conv'8715'_300 :: T__'8715'__16 -> T__'8715'__16
du_conv'8715'_300 v0 = coe v0
-- Algorithmic.conv⊢
d_conv'8866'_312 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  T_Ctx_2 ->
  T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8866'__178 -> T__'8866'__178
d_conv'8866'_312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_conv'8866'_312 v7
du_conv'8866'_312 :: T__'8866'__178 -> T__'8866'__178
du_conv'8866'_312 v0 = coe v0
-- Algorithmic.lookupCase
d_lookupCase_328 ::
  Integer ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  T_Ctx_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  T_Cases_172 -> T__'8866'__178
d_lookupCase_328 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_lookupCase_328 v4 v5 v6
du_lookupCase_328 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  T_Cases_172 -> T__'8866'__178
du_lookupCase_328 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> case coe v2 of
             C__'8759'__290 v7 v8 -> coe v7
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
        -> case coe v2 of
             C__'8759'__290 v8 v9
               -> case coe v0 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12
                      -> coe du_lookupCase_328 (coe v12) (coe v4) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algorithmic.bwdMkCaseType
d_bwdMkCaseType_344 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.List.T_Bwd_6 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_bwdMkCaseType_344 ~v0 v1 v2 = du_bwdMkCaseType_344 v1 v2
du_bwdMkCaseType_344 ::
  MAlonzo.Code.Utils.List.T_Bwd_6 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
du_bwdMkCaseType_344 v0 v1
  = coe
      MAlonzo.Code.Utils.List.du_bwd'45'foldr_26
      (coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16) (coe v1) (coe v0)
-- Algorithmic.lemma-bwdfwdfunction'
d_lemma'45'bwdfwdfunction''_356 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma'45'bwdfwdfunction''_356 = erased
-- Algorithmic.constr-cong
d_constr'45'cong_382 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  T_Ctx_2 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_constr'45'cong_382 = erased
-- Algorithmic.constr-cong'
d_constr'45'cong''_410 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  T_Ctx_2 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Utils.List.T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_constr'45'cong''_410 = erased
