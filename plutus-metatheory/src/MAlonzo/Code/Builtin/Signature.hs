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

module MAlonzo.Code.Builtin.Signature where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Builtin.Constant.AtomicType
import qualified MAlonzo.Code.Builtin.Constant.Type
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.NonEmpty.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Utils

-- Builtin.Signature._⊢♯
d__'8866''9839'_4 a0 = ()
data T__'8866''9839'_4
  = C_'96'_8 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_atomic_12 MAlonzo.Code.Builtin.Constant.AtomicType.T_AtomicTyCon_6 |
    C_list_16 T__'8866''9839'_4 | C_array_20 T__'8866''9839'_4 |
    C_pair_24 T__'8866''9839'_4 T__'8866''9839'_4
-- Builtin.Signature._⊢⋆
d__'8866''8902'_26 a0 = ()
newtype T__'8866''8902'_26
  = C_'96'_30 MAlonzo.Code.Data.Fin.Base.T_Fin_10
-- Builtin.Signature._↑
d__'8593'_36 ::
  Integer ->
  Integer ->
  T__'8866''9839'_4 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d__'8593'_36 ~v0 ~v1 = du__'8593'_36
du__'8593'_36 ::
  T__'8866''9839'_4 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du__'8593'_36 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
-- Builtin.Signature.Args
d_Args_56 :: Integer -> Integer -> ()
d_Args_56 = erased
-- Builtin.Signature._/_⊢r⋆
d__'47'_'8866'r'8902'_62 a0 a1 = ()
newtype T__'47'_'8866'r'8902'_62
  = C_argtype_68 MAlonzo.Code.Data.Sum.Base.T__'8846'__30
-- Builtin.Signature.Sig
d_Sig_70 = ()
data T_Sig_70
  = C_sig_88 Integer Integer
             MAlonzo.Code.Data.List.NonEmpty.Base.T_List'8314'_22
             MAlonzo.Code.Data.Sum.Base.T__'8846'__30
-- Builtin.Signature.Sig.fv⋆
d_fv'8902'_80 :: T_Sig_70 -> Integer
d_fv'8902'_80 v0
  = case coe v0 of
      C_sig_88 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.Sig.fv♯
d_fv'9839'_82 :: T_Sig_70 -> Integer
d_fv'9839'_82 v0
  = case coe v0 of
      C_sig_88 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.Sig.args
d_args_84 ::
  T_Sig_70 -> MAlonzo.Code.Data.List.NonEmpty.Base.T_List'8314'_22
d_args_84 v0
  = case coe v0 of
      C_sig_88 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.Sig.result
d_result_86 :: T_Sig_70 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_result_86 v0
  = case coe v0 of
      C_sig_88 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.args♯
d_args'9839'_90 :: T_Sig_70 -> Integer
d_args'9839'_90 v0
  = coe
      MAlonzo.Code.Data.List.NonEmpty.Base.du_length_54
      (coe d_args_84 (coe v0))
-- Builtin.Signature.fv
d_fv_94 :: T_Sig_70 -> Integer
d_fv_94 v0
  = coe
      addInt (coe d_fv'9839'_82 (coe v0)) (coe d_fv'8902'_80 (coe v0))
-- Builtin.Signature.mkCtx⋆
d_mkCtx'8902'_102 ::
  Integer -> Integer -> MAlonzo.Code.Type.T_Ctx'8902'_2
d_mkCtx'8902'_102 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe MAlonzo.Code.Type.C_'8709'_4
             _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (coe
                       MAlonzo.Code.Type.C__'44''8902'__6
                       (coe d_mkCtx'8902'_102 (coe (0 :: Integer)) (coe v2))
                       (coe MAlonzo.Code.Utils.C_'9839'_780))
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Type.C__'44''8902'__6
                (coe d_mkCtx'8902'_102 (coe v2) (coe v1))
                (coe MAlonzo.Code.Utils.C_'42'_778))
-- Builtin.Signature.fin♯2∋⋆
d_fin'9839'2'8715''8902'_114 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Type.T__'8715''8902'__14
d_fin'9839'2'8715''8902'_114 v0 ~v1 v2
  = du_fin'9839'2'8715''8902'_114 v0 v2
du_fin'9839'2'8715''8902'_114 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Type.T__'8715''8902'__14
du_fin'9839'2'8715''8902'_114 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Type.C_Z_16
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
               -> coe
                    MAlonzo.Code.Type.C_S_18
                    (coe du_fin'9839'2'8715''8902'_114 (coe (0 :: Integer)) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Fin.Base.C_zero_12
                  -> coe
                       MAlonzo.Code.Type.C_S_18
                       (coe
                          du_fin'9839'2'8715''8902'_114 (coe v2)
                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
                  -> coe
                       MAlonzo.Code.Type.C_S_18
                       (coe
                          du_fin'9839'2'8715''8902'_114 (coe v2)
                          (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Builtin.Signature.fin⋆2∋⋆
d_fin'8902'2'8715''8902'_128 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Type.T__'8715''8902'__14
d_fin'8902'2'8715''8902'_128 ~v0 ~v1 v2
  = du_fin'8902'2'8715''8902'_128 v2
du_fin'8902'2'8715''8902'_128 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Type.T__'8715''8902'__14
du_fin'8902'2'8715''8902'_128 v0
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe MAlonzo.Code.Type.C_Z_16
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v2
        -> coe
             MAlonzo.Code.Type.C_S_18
             (coe du_fin'8902'2'8715''8902'_128 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.FromSig.⊢♯2TyNe♯
d_'8866''9839'2TyNe'9839'_184 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  Integer -> Integer -> T__'8866''9839'_4 -> AgdaAny
d_'8866''9839'2TyNe'9839'_184 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 v9
                              v10 v11
  = du_'8866''9839'2TyNe'9839'_184 v2 v3 v4 v5 v9 v10 v11
du_'8866''9839'2TyNe'9839'_184 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  Integer -> Integer -> T__'8866''9839'_4 -> AgdaAny
du_'8866''9839'2TyNe'9839'_184 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_'96'_8 v8
        -> coe
             v1 v4 v5 (coe MAlonzo.Code.Utils.C_'9839'_780)
             (coe du_fin'9839'2'8715''8902'_114 (coe v4) (coe v8))
      C_atomic_12 v8
        -> coe
             v3 (d_mkCtx'8902'_102 (coe v4) (coe v5))
             (coe MAlonzo.Code.Utils.C_'9839'_780)
             (coe MAlonzo.Code.Builtin.Constant.Type.C_atomic_8 (coe v8))
      C_list_16 v8
        -> coe
             v2 (d_mkCtx'8902'_102 (coe v4) (coe v5))
             (coe MAlonzo.Code.Utils.C_'9839'_780)
             (coe MAlonzo.Code.Utils.C_'9839'_780)
             (coe
                v3 (d_mkCtx'8902'_102 (coe v4) (coe v5))
                (coe
                   MAlonzo.Code.Utils.C__'8658'__782
                   (coe MAlonzo.Code.Utils.C_'9839'_780)
                   (coe MAlonzo.Code.Utils.C_'9839'_780))
                (coe MAlonzo.Code.Builtin.Constant.Type.C_list_10))
             (coe
                v0 (d_mkCtx'8902'_102 (coe v4) (coe v5))
                (coe MAlonzo.Code.Utils.C_'9839'_780)
                (coe
                   du_'8866''9839'2TyNe'9839'_184 (coe v0) (coe v1) (coe v2) (coe v3)
                   (coe v4) (coe v5) (coe v8)))
      C_array_20 v8
        -> coe
             v2 (d_mkCtx'8902'_102 (coe v4) (coe v5))
             (coe MAlonzo.Code.Utils.C_'9839'_780)
             (coe MAlonzo.Code.Utils.C_'9839'_780)
             (coe
                v3 (d_mkCtx'8902'_102 (coe v4) (coe v5))
                (coe
                   MAlonzo.Code.Utils.C__'8658'__782
                   (coe MAlonzo.Code.Utils.C_'9839'_780)
                   (coe MAlonzo.Code.Utils.C_'9839'_780))
                (coe MAlonzo.Code.Builtin.Constant.Type.C_array_12))
             (coe
                v0 (d_mkCtx'8902'_102 (coe v4) (coe v5))
                (coe MAlonzo.Code.Utils.C_'9839'_780)
                (coe
                   du_'8866''9839'2TyNe'9839'_184 (coe v0) (coe v1) (coe v2) (coe v3)
                   (coe v4) (coe v5) (coe v8)))
      C_pair_24 v8 v9
        -> coe
             v2 (d_mkCtx'8902'_102 (coe v4) (coe v5))
             (coe MAlonzo.Code.Utils.C_'9839'_780)
             (coe MAlonzo.Code.Utils.C_'9839'_780)
             (coe
                v2 (d_mkCtx'8902'_102 (coe v4) (coe v5))
                (coe MAlonzo.Code.Utils.C_'9839'_780)
                (coe
                   MAlonzo.Code.Utils.C__'8658'__782
                   (coe MAlonzo.Code.Utils.C_'9839'_780)
                   (coe MAlonzo.Code.Utils.C_'9839'_780))
                (coe
                   v3 (d_mkCtx'8902'_102 (coe v4) (coe v5))
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__782
                      (coe MAlonzo.Code.Utils.C_'9839'_780)
                      (coe
                         MAlonzo.Code.Utils.C__'8658'__782
                         (coe MAlonzo.Code.Utils.C_'9839'_780)
                         (coe MAlonzo.Code.Utils.C_'9839'_780)))
                   (coe MAlonzo.Code.Builtin.Constant.Type.C_pair_14))
                (coe
                   v0 (d_mkCtx'8902'_102 (coe v4) (coe v5))
                   (coe MAlonzo.Code.Utils.C_'9839'_780)
                   (coe
                      du_'8866''9839'2TyNe'9839'_184 (coe v0) (coe v1) (coe v2) (coe v3)
                      (coe v4) (coe v5) (coe v8))))
             (coe
                v0 (d_mkCtx'8902'_102 (coe v4) (coe v5))
                (coe MAlonzo.Code.Utils.C_'9839'_780)
                (coe
                   du_'8866''9839'2TyNe'9839'_184 (coe v0) (coe v1) (coe v2) (coe v3)
                   (coe v4) (coe v5) (coe v9)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.FromSig.mkTy
d_mkTy_202 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_mkTy_202 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9 v10 v11
  = du_mkTy_202 v2 v3 v4 v5 v6 v9 v10 v11
du_mkTy_202 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_mkTy_202 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
        -> case coe v8 of
             C_'96'_30 v10
               -> coe
                    v0 (d_mkCtx'8902'_102 (coe v5) (coe v6))
                    (coe MAlonzo.Code.Utils.C_'42'_778)
                    (coe
                       v1 v5 v6 (coe MAlonzo.Code.Utils.C_'42'_778)
                       (coe du_fin'8902'2'8715''8902'_128 (coe v10)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> coe
             v4 (d_mkCtx'8902'_102 (coe v5) (coe v6))
             (coe
                v0 (d_mkCtx'8902'_102 (coe v5) (coe v6))
                (coe MAlonzo.Code.Utils.C_'9839'_780)
                (coe
                   du_'8866''9839'2TyNe'9839'_184 (coe v0) (coe v1) (coe v2) (coe v3)
                   (coe v5) (coe v6) (coe v8)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.FromSig.sig2type⇒
d_sig2type'8658'_212 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] -> AgdaAny -> AgdaAny
d_sig2type'8658'_212 ~v0 ~v1 v2 v3 v4 v5 v6 v7 ~v8 v9 v10 v11 v12
  = du_sig2type'8658'_212 v2 v3 v4 v5 v6 v7 v9 v10 v11 v12
du_sig2type'8658'_212 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] -> AgdaAny -> AgdaAny
du_sig2type'8658'_212 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v8 of
      [] -> coe v9
      (:) v10 v11
        -> coe
             du_sig2type'8658'_212 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v11)
             (coe
                v5 (d_mkCtx'8902'_102 (coe v6) (coe v7))
                (coe
                   du_mkTy_202 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
                   (coe v7) (coe v10))
                v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.FromSig.sig2typeΠ
d_sig2typeΠ_226 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  Integer -> Integer -> AgdaAny -> AgdaAny
d_sig2typeΠ_226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11
  = du_sig2typeΠ_226 v8 v9 v10 v11
du_sig2typeΠ_226 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  Integer -> Integer -> AgdaAny -> AgdaAny
du_sig2typeΠ_226 v0 v1 v2 v3
  = case coe v1 of
      0 -> case coe v2 of
             0 -> coe v3
             _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
                  coe
                    (coe
                       du_sig2typeΠ_226 (coe v0) (coe (0 :: Integer)) (coe v4)
                       (coe
                          v0 (d_mkCtx'8902'_102 (coe (0 :: Integer)) (coe v4))
                          (coe MAlonzo.Code.Utils.C_'9839'_780) v3))
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                du_sig2typeΠ_226 (coe v0) (coe v4) (coe v2)
                (coe
                   v0 (d_mkCtx'8902'_102 (coe v4) (coe v2))
                   (coe MAlonzo.Code.Utils.C_'42'_778) v3))
-- Builtin.Signature.FromSig.sig2type
d_sig2type_240 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  T_Sig_70 -> AgdaAny
d_sig2type_240 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du_sig2type_240 v2 v3 v4 v5 v6 v7 v8 v9
du_sig2type_240 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  T_Sig_70 -> AgdaAny
du_sig2type_240 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_sig_88 v8 v9 v10 v11
        -> coe
             du_sig2typeΠ_226 (coe v6) (coe v8) (coe v9)
             (coe
                du_sig2type'8658'_212 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v8) (coe v9)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Data.List.NonEmpty.Base.d_head_30 (coe v10))
                   (coe MAlonzo.Code.Data.List.NonEmpty.Base.d_tail_32 (coe v10)))
                (coe
                   du_mkTy_202 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
                   (coe v9) (coe v11)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.FromSig.SigTy
d_SigTy_264 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
            a16 a17 a18
  = ()
data T_SigTy_264
  = C_bresult_278 | C__B'8658'__300 AgdaAny AgdaAny T_SigTy_264 |
    C_sucΠ_324 MAlonzo.Code.Utils.T_Kind_776 AgdaAny T_SigTy_264
-- Builtin.Signature.FromSig.sig2SigTy⇒
d_sig2SigTy'8658'_346 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__188 ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__188 ->
  AgdaAny -> T_SigTy_264 -> T_SigTy_264
d_sig2SigTy'8658'_346 ~v0 ~v1 v2 v3 v4 v5 v6 v7 ~v8 v9 v10 ~v11
                      ~v12 v13 ~v14 ~v15 v16 v17 v18
  = du_sig2SigTy'8658'_346 v2 v3 v4 v5 v6 v7 v9 v10 v13 v16 v17 v18
du_sig2SigTy'8658'_346 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__188 ->
  AgdaAny -> T_SigTy_264 -> T_SigTy_264
du_sig2SigTy'8658'_346 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v8 of
      [] -> coe seq (coe v9) (coe v11)
      (:) v12 v13
        -> case coe v9 of
             MAlonzo.Code.Utils.C_bubble_200 v17
               -> coe
                    du_sig2SigTy'8658'_346 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v13) (coe v17)
                    (coe
                       v5 (d_mkCtx'8902'_102 (coe v6) (coe v7))
                       (coe
                          du_mkTy_202 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
                          (coe v7) (coe v12))
                       v10)
                    (coe
                       C__B'8658'__300
                       (coe
                          du_mkTy_202 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
                          (coe v7) (coe v12))
                       v10 v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.FromSig.sig2SigTyΠ
d_sig2SigTyΠ_378 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__188 ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__188 ->
  AgdaAny -> T_SigTy_264 -> T_SigTy_264
d_sig2SigTyΠ_378 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 ~v11
                 ~v12 ~v13 ~v14 v15 ~v16 ~v17 v18 v19
  = du_sig2SigTyΠ_378 v8 v9 v10 v15 v18 v19
du_sig2SigTyΠ_378 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__188 ->
  AgdaAny -> T_SigTy_264 -> T_SigTy_264
du_sig2SigTyΠ_378 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      0 -> case coe v3 of
             MAlonzo.Code.Utils.C_start_192 -> coe v5
             MAlonzo.Code.Utils.C_bubble_200 v9
               -> let v10 = subInt (coe v2) (coe (1 :: Integer)) in
                  coe
                    (coe
                       du_sig2SigTyΠ_378 (coe v0) (coe (0 :: Integer)) (coe v10) (coe v9)
                       (coe
                          v0 (d_mkCtx'8902'_102 (coe (0 :: Integer)) (coe v10))
                          (coe MAlonzo.Code.Utils.C_'9839'_780) v4)
                       (coe C_sucΠ_324 (coe MAlonzo.Code.Utils.C_'9839'_780) v4 v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v6 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Utils.C_bubble_200 v10
                  -> coe
                       du_sig2SigTyΠ_378 (coe v0) (coe v6) (coe v2) (coe v10)
                       (coe
                          v0 (d_mkCtx'8902'_102 (coe v6) (coe v2))
                          (coe MAlonzo.Code.Utils.C_'42'_778) v4)
                       (coe C_sucΠ_324 (coe MAlonzo.Code.Utils.C_'42'_778) v4 v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Builtin.Signature.FromSig.sig2SigTy
d_sig2SigTy_396 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  T_Sig_70 -> T_SigTy_264
d_sig2SigTy_396 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du_sig2SigTy_396 v2 v3 v4 v5 v6 v7 v8 v9
du_sig2SigTy_396 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  T_Sig_70 -> T_SigTy_264
du_sig2SigTy_396 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_sig_88 v8 v9 v10 v11
        -> coe
             du_sig2SigTyΠ_378 (coe v6) (coe v8) (coe v9)
             (coe
                MAlonzo.Code.Utils.d_alldone_248 (coe addInt (coe v8) (coe v9)))
             (coe
                du_sig2type'8658'_212 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v8) (coe v9)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Data.List.NonEmpty.Base.d_head_30 (coe v10))
                   (coe MAlonzo.Code.Data.List.NonEmpty.Base.d_tail_32 (coe v10)))
                (coe
                   du_mkTy_202 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
                   (coe v9) (coe v11)))
             (coe
                du_sig2SigTy'8658'_346 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v8) (coe v9)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe MAlonzo.Code.Data.List.NonEmpty.Base.d_head_30 (coe v10))
                   (coe MAlonzo.Code.Data.List.NonEmpty.Base.d_tail_32 (coe v10)))
                (coe
                   MAlonzo.Code.Utils.d_alldone_248
                   (coe MAlonzo.Code.Data.List.NonEmpty.Base.du_length_54 (coe v10)))
                (coe
                   du_mkTy_202 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
                   (coe v9) (coe v11))
                (coe C_bresult_278))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.FromSig.sigTy2type
d_sigTy2type_426 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__188 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__188 -> T_SigTy_264 -> AgdaAny
d_sigTy2type_426 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19
  = du_sigTy2type_426 v16
du_sigTy2type_426 :: AgdaAny -> AgdaAny
du_sigTy2type_426 v0 = coe v0
-- Builtin.Signature.FromSig.saturatedSigTy
d_saturatedSigTy_434 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  T_Sig_70 -> AgdaAny -> ()
d_saturatedSigTy_434 = erased
-- Builtin.Signature.FromSig.convSigTy
d_convSigTy_468 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_776 -> AgdaAny -> AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__188 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__188 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__188 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__188 ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SigTy_264 -> T_SigTy_264
d_convSigTy_468 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24
  = du_convSigTy_468 v24
du_convSigTy_468 :: T_SigTy_264 -> T_SigTy_264
du_convSigTy_468 v0 = coe v0
