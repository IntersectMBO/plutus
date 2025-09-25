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
import qualified MAlonzo.Code.Builtin.Constant.AtomicType
import qualified MAlonzo.Code.Builtin.Constant.Type
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.NonEmpty.Base
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Utils

-- Builtin.Signature._⊢♯
d__'8866''9839'_4 a0 = ()
data T__'8866''9839'_4
  = C_'96'_8 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_atomic_12 MAlonzo.Code.Builtin.Constant.AtomicType.T_AtomicTyCon_6 |
    C_list_16 T__'8866''9839'_4 | C_array_20 T__'8866''9839'_4 |
    C_pair_24 T__'8866''9839'_4 T__'8866''9839'_4
-- Builtin.Signature._/_⊢⋆
d__'47'_'8866''8902'_26 a0 a1 = ()
data T__'47'_'8866''8902'_26
  = C_'96'_32 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C__'8593'_38 T__'8866''9839'_4
-- Builtin.Signature.Args
d_Args_60 :: Integer -> Integer -> ()
d_Args_60 = erased
-- Builtin.Signature._/_⊢r⋆
d__'47'_'8866'r'8902'_66 a0 a1 = ()
newtype T__'47'_'8866'r'8902'_66
  = C_argtype_72 T__'47'_'8866''8902'_26
-- Builtin.Signature.Sig
d_Sig_74 = ()
data T_Sig_74
  = C_sig_92 Integer Integer
             MAlonzo.Code.Data.List.NonEmpty.Base.T_List'8314'_22
             T__'47'_'8866''8902'_26
-- Builtin.Signature.Sig.fv⋆
d_fv'8902'_84 :: T_Sig_74 -> Integer
d_fv'8902'_84 v0
  = case coe v0 of
      C_sig_92 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.Sig.fv♯
d_fv'9839'_86 :: T_Sig_74 -> Integer
d_fv'9839'_86 v0
  = case coe v0 of
      C_sig_92 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.Sig.args
d_args_88 ::
  T_Sig_74 -> MAlonzo.Code.Data.List.NonEmpty.Base.T_List'8314'_22
d_args_88 v0
  = case coe v0 of
      C_sig_92 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.Sig.result
d_result_90 :: T_Sig_74 -> T__'47'_'8866''8902'_26
d_result_90 v0
  = case coe v0 of
      C_sig_92 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.args♯
d_args'9839'_94 :: T_Sig_74 -> Integer
d_args'9839'_94 v0
  = coe
      MAlonzo.Code.Data.List.NonEmpty.Base.du_length_54
      (coe d_args_88 (coe v0))
-- Builtin.Signature.fv
d_fv_98 :: T_Sig_74 -> Integer
d_fv_98 v0
  = coe
      addInt (coe d_fv'9839'_86 (coe v0)) (coe d_fv'8902'_84 (coe v0))
-- Builtin.Signature.mkCtx⋆
d_mkCtx'8902'_106 ::
  Integer -> Integer -> MAlonzo.Code.Type.T_Ctx'8902'_2
d_mkCtx'8902'_106 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe MAlonzo.Code.Type.C_'8709'_4
             _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (coe
                       MAlonzo.Code.Type.C__'44''8902'__6
                       (coe d_mkCtx'8902'_106 (coe (0 :: Integer)) (coe v2))
                       (coe MAlonzo.Code.Utils.C_'9839'_660))
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Type.C__'44''8902'__6
                (coe d_mkCtx'8902'_106 (coe v2) (coe v1))
                (coe MAlonzo.Code.Utils.C_'42'_658))
-- Builtin.Signature.fin♯2∋⋆
d_fin'9839'2'8715''8902'_118 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Type.T__'8715''8902'__14
d_fin'9839'2'8715''8902'_118 v0 ~v1 v2
  = du_fin'9839'2'8715''8902'_118 v0 v2
du_fin'9839'2'8715''8902'_118 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Type.T__'8715''8902'__14
du_fin'9839'2'8715''8902'_118 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Type.C_Z_16
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
               -> coe
                    MAlonzo.Code.Type.C_S_18
                    (coe du_fin'9839'2'8715''8902'_118 (coe (0 :: Integer)) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Fin.Base.C_zero_12
                  -> coe
                       MAlonzo.Code.Type.C_S_18
                       (coe
                          du_fin'9839'2'8715''8902'_118 (coe v2)
                          (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
                  -> coe
                       MAlonzo.Code.Type.C_S_18
                       (coe
                          du_fin'9839'2'8715''8902'_118 (coe v2)
                          (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Builtin.Signature.fin⋆2∋⋆
d_fin'8902'2'8715''8902'_132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Type.T__'8715''8902'__14
d_fin'8902'2'8715''8902'_132 ~v0 ~v1 v2
  = du_fin'8902'2'8715''8902'_132 v2
du_fin'8902'2'8715''8902'_132 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Type.T__'8715''8902'__14
du_fin'8902'2'8715''8902'_132 v0
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe MAlonzo.Code.Type.C_Z_16
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v2
        -> coe
             MAlonzo.Code.Type.C_S_18
             (coe du_fin'8902'2'8715''8902'_132 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.FromSig.⊢♯2TyNe♯
d_'8866''9839'2TyNe'9839'_188 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  Integer -> Integer -> T__'8866''9839'_4 -> AgdaAny
d_'8866''9839'2TyNe'9839'_188 ~v0 ~v1 v2 v3 v4 v5 ~v6 ~v7 ~v8 v9
                              v10 v11
  = du_'8866''9839'2TyNe'9839'_188 v2 v3 v4 v5 v9 v10 v11
du_'8866''9839'2TyNe'9839'_188 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  Integer -> Integer -> T__'8866''9839'_4 -> AgdaAny
du_'8866''9839'2TyNe'9839'_188 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_'96'_8 v8
        -> coe
             v1 v4 v5 (coe MAlonzo.Code.Utils.C_'9839'_660)
             (coe du_fin'9839'2'8715''8902'_118 (coe v4) (coe v8))
      C_atomic_12 v8
        -> coe
             v3 (d_mkCtx'8902'_106 (coe v4) (coe v5))
             (coe MAlonzo.Code.Utils.C_'9839'_660)
             (coe MAlonzo.Code.Builtin.Constant.Type.C_atomic_8 (coe v8))
      C_list_16 v8
        -> coe
             v2 (d_mkCtx'8902'_106 (coe v4) (coe v5))
             (coe MAlonzo.Code.Utils.C_'9839'_660)
             (coe MAlonzo.Code.Utils.C_'9839'_660)
             (coe
                v3 (d_mkCtx'8902'_106 (coe v4) (coe v5))
                (coe
                   MAlonzo.Code.Utils.C__'8658'__662
                   (coe MAlonzo.Code.Utils.C_'9839'_660)
                   (coe MAlonzo.Code.Utils.C_'9839'_660))
                (coe MAlonzo.Code.Builtin.Constant.Type.C_list_10))
             (coe
                v0 (d_mkCtx'8902'_106 (coe v4) (coe v5))
                (coe MAlonzo.Code.Utils.C_'9839'_660)
                (coe
                   du_'8866''9839'2TyNe'9839'_188 (coe v0) (coe v1) (coe v2) (coe v3)
                   (coe v4) (coe v5) (coe v8)))
      C_array_20 v8
        -> coe
             v2 (d_mkCtx'8902'_106 (coe v4) (coe v5))
             (coe MAlonzo.Code.Utils.C_'9839'_660)
             (coe MAlonzo.Code.Utils.C_'9839'_660)
             (coe
                v3 (d_mkCtx'8902'_106 (coe v4) (coe v5))
                (coe
                   MAlonzo.Code.Utils.C__'8658'__662
                   (coe MAlonzo.Code.Utils.C_'9839'_660)
                   (coe MAlonzo.Code.Utils.C_'9839'_660))
                (coe MAlonzo.Code.Builtin.Constant.Type.C_array_12))
             (coe
                v0 (d_mkCtx'8902'_106 (coe v4) (coe v5))
                (coe MAlonzo.Code.Utils.C_'9839'_660)
                (coe
                   du_'8866''9839'2TyNe'9839'_188 (coe v0) (coe v1) (coe v2) (coe v3)
                   (coe v4) (coe v5) (coe v8)))
      C_pair_24 v8 v9
        -> coe
             v2 (d_mkCtx'8902'_106 (coe v4) (coe v5))
             (coe MAlonzo.Code.Utils.C_'9839'_660)
             (coe MAlonzo.Code.Utils.C_'9839'_660)
             (coe
                v2 (d_mkCtx'8902'_106 (coe v4) (coe v5))
                (coe MAlonzo.Code.Utils.C_'9839'_660)
                (coe
                   MAlonzo.Code.Utils.C__'8658'__662
                   (coe MAlonzo.Code.Utils.C_'9839'_660)
                   (coe MAlonzo.Code.Utils.C_'9839'_660))
                (coe
                   v3 (d_mkCtx'8902'_106 (coe v4) (coe v5))
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__662
                      (coe MAlonzo.Code.Utils.C_'9839'_660)
                      (coe
                         MAlonzo.Code.Utils.C__'8658'__662
                         (coe MAlonzo.Code.Utils.C_'9839'_660)
                         (coe MAlonzo.Code.Utils.C_'9839'_660)))
                   (coe MAlonzo.Code.Builtin.Constant.Type.C_pair_14))
                (coe
                   v0 (d_mkCtx'8902'_106 (coe v4) (coe v5))
                   (coe MAlonzo.Code.Utils.C_'9839'_660)
                   (coe
                      du_'8866''9839'2TyNe'9839'_188 (coe v0) (coe v1) (coe v2) (coe v3)
                      (coe v4) (coe v5) (coe v8))))
             (coe
                v0 (d_mkCtx'8902'_106 (coe v4) (coe v5))
                (coe MAlonzo.Code.Utils.C_'9839'_660)
                (coe
                   du_'8866''9839'2TyNe'9839'_188 (coe v0) (coe v1) (coe v2) (coe v3)
                   (coe v4) (coe v5) (coe v9)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.FromSig.mkTy
d_mkTy_206 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  Integer -> Integer -> T__'47'_'8866''8902'_26 -> AgdaAny
d_mkTy_206 ~v0 ~v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9 v10 v11
  = du_mkTy_206 v2 v3 v4 v5 v6 v9 v10 v11
du_mkTy_206 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  Integer -> Integer -> T__'47'_'8866''8902'_26 -> AgdaAny
du_mkTy_206 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_'96'_32 v10
        -> coe
             v0 (d_mkCtx'8902'_106 (coe v5) (coe v6))
             (coe MAlonzo.Code.Utils.C_'42'_658)
             (coe
                v1 v5 v6 (coe MAlonzo.Code.Utils.C_'42'_658)
                (coe du_fin'8902'2'8715''8902'_132 (coe v10)))
      C__'8593'_38 v10
        -> coe
             v4 (d_mkCtx'8902'_106 (coe v5) (coe v6))
             (coe
                v0 (d_mkCtx'8902'_106 (coe v5) (coe v6))
                (coe MAlonzo.Code.Utils.C_'9839'_660)
                (coe
                   du_'8866''9839'2TyNe'9839'_188 (coe v0) (coe v1) (coe v2) (coe v3)
                   (coe v5) (coe v6) (coe v10)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.FromSig.sig2type⇒
d_sig2type'8658'_216 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  Integer ->
  Integer -> [T__'47'_'8866''8902'_26] -> AgdaAny -> AgdaAny
d_sig2type'8658'_216 ~v0 ~v1 v2 v3 v4 v5 v6 v7 ~v8 v9 v10 v11 v12
  = du_sig2type'8658'_216 v2 v3 v4 v5 v6 v7 v9 v10 v11 v12
du_sig2type'8658'_216 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  Integer ->
  Integer -> [T__'47'_'8866''8902'_26] -> AgdaAny -> AgdaAny
du_sig2type'8658'_216 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v8 of
      [] -> coe v9
      (:) v10 v11
        -> coe
             du_sig2type'8658'_216 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v11)
             (coe
                v5 (d_mkCtx'8902'_106 (coe v6) (coe v7))
                (coe
                   du_mkTy_206 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
                   (coe v7) (coe v10))
                v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.FromSig.sig2typeΠ
d_sig2typeΠ_230 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  Integer -> Integer -> AgdaAny -> AgdaAny
d_sig2typeΠ_230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11
  = du_sig2typeΠ_230 v8 v9 v10 v11
du_sig2typeΠ_230 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  Integer -> Integer -> AgdaAny -> AgdaAny
du_sig2typeΠ_230 v0 v1 v2 v3
  = case coe v1 of
      0 -> case coe v2 of
             0 -> coe v3
             _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
                  coe
                    (coe
                       du_sig2typeΠ_230 (coe v0) (coe (0 :: Integer)) (coe v4)
                       (coe
                          v0 (d_mkCtx'8902'_106 (coe (0 :: Integer)) (coe v4))
                          (coe MAlonzo.Code.Utils.C_'9839'_660) v3))
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                du_sig2typeΠ_230 (coe v0) (coe v4) (coe v2)
                (coe
                   v0 (d_mkCtx'8902'_106 (coe v4) (coe v2))
                   (coe MAlonzo.Code.Utils.C_'42'_658) v3))
-- Builtin.Signature.FromSig.sig2type
d_sig2type_244 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  T_Sig_74 -> AgdaAny
d_sig2type_244 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du_sig2type_244 v2 v3 v4 v5 v6 v7 v8 v9
du_sig2type_244 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  T_Sig_74 -> AgdaAny
du_sig2type_244 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_sig_92 v8 v9 v10 v11
        -> coe
             du_sig2typeΠ_230 (coe v6) (coe v8) (coe v9)
             (coe
                du_sig2type'8658'_216 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v8) (coe v9)
                (coe MAlonzo.Code.Data.List.NonEmpty.Base.du_toList_60 (coe v10))
                (coe
                   du_mkTy_206 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
                   (coe v9) (coe v11)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.FromSig.SigTy
d_SigTy_268 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
            a16 a17 a18
  = ()
data T_SigTy_268
  = C_bresult_282 | C__B'8658'__304 AgdaAny AgdaAny T_SigTy_268 |
    C_sucΠ_328 MAlonzo.Code.Utils.T_Kind_656 AgdaAny T_SigTy_268
-- Builtin.Signature.FromSig.sig2SigTy⇒
d_sig2SigTy'8658'_350 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  [T__'47'_'8866''8902'_26] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  AgdaAny -> T_SigTy_268 -> T_SigTy_268
d_sig2SigTy'8658'_350 ~v0 ~v1 v2 v3 v4 v5 v6 v7 ~v8 v9 v10 ~v11
                      ~v12 v13 ~v14 ~v15 v16 v17 v18
  = du_sig2SigTy'8658'_350 v2 v3 v4 v5 v6 v7 v9 v10 v13 v16 v17 v18
du_sig2SigTy'8658'_350 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  Integer ->
  Integer ->
  [T__'47'_'8866''8902'_26] ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  AgdaAny -> T_SigTy_268 -> T_SigTy_268
du_sig2SigTy'8658'_350 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v8 of
      [] -> coe seq (coe v9) (coe v11)
      (:) v12 v13
        -> case coe v9 of
             MAlonzo.Code.Utils.C_bubble_132 v17
               -> coe
                    du_sig2SigTy'8658'_350 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v13) (coe v17)
                    (coe
                       v5 (d_mkCtx'8902'_106 (coe v6) (coe v7))
                       (coe
                          du_mkTy_206 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
                          (coe v7) (coe v12))
                       v10)
                    (coe
                       C__B'8658'__304
                       (coe
                          du_mkTy_206 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v6)
                          (coe v7) (coe v12))
                       v10 v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.FromSig.sig2SigTyΠ
d_sig2SigTyΠ_382 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  AgdaAny -> T_SigTy_268 -> T_SigTy_268
d_sig2SigTyΠ_382 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 ~v11
                 ~v12 ~v13 ~v14 v15 ~v16 ~v17 v18 v19
  = du_sig2SigTyΠ_382 v8 v9 v10 v15 v18 v19
du_sig2SigTyΠ_382 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  AgdaAny -> T_SigTy_268 -> T_SigTy_268
du_sig2SigTyΠ_382 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      0 -> case coe v3 of
             MAlonzo.Code.Utils.C_start_124 -> coe v5
             MAlonzo.Code.Utils.C_bubble_132 v9
               -> let v10 = subInt (coe v2) (coe (1 :: Integer)) in
                  coe
                    (coe
                       du_sig2SigTyΠ_382 (coe v0) (coe (0 :: Integer)) (coe v10) (coe v9)
                       (coe
                          v0 (d_mkCtx'8902'_106 (coe (0 :: Integer)) (coe v10))
                          (coe MAlonzo.Code.Utils.C_'9839'_660) v4)
                       (coe C_sucΠ_328 (coe MAlonzo.Code.Utils.C_'9839'_660) v4 v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v6 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Utils.C_bubble_132 v10
                  -> coe
                       du_sig2SigTyΠ_382 (coe v0) (coe v6) (coe v2) (coe v10)
                       (coe
                          v0 (d_mkCtx'8902'_106 (coe v6) (coe v2))
                          (coe MAlonzo.Code.Utils.C_'42'_658) v4)
                       (coe C_sucΠ_328 (coe MAlonzo.Code.Utils.C_'42'_658) v4 v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Builtin.Signature.FromSig.sig2SigTy
d_sig2SigTy_400 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  T_Sig_74 -> T_SigTy_268
d_sig2SigTy_400 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du_sig2SigTy_400 v2 v3 v4 v5 v6 v7 v8 v9
du_sig2SigTy_400 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  T_Sig_74 -> T_SigTy_268
du_sig2SigTy_400 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_sig_92 v8 v9 v10 v11
        -> coe
             du_sig2SigTyΠ_382 (coe v6) (coe v8) (coe v9)
             (coe
                MAlonzo.Code.Utils.d_alldone_180 (coe addInt (coe v8) (coe v9)))
             (coe
                du_sig2type'8658'_216 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v8) (coe v9)
                (coe MAlonzo.Code.Data.List.NonEmpty.Base.du_toList_60 (coe v10))
                (coe
                   du_mkTy_206 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
                   (coe v9) (coe v11)))
             (coe
                du_sig2SigTy'8658'_350 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v8) (coe v9)
                (coe MAlonzo.Code.Data.List.NonEmpty.Base.du_toList_60 (coe v10))
                (coe
                   MAlonzo.Code.Utils.d_alldone_180
                   (coe MAlonzo.Code.Data.List.NonEmpty.Base.du_length_54 (coe v10)))
                (coe
                   du_mkTy_206 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v8)
                   (coe v9) (coe v11))
                (coe C_bresult_282))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.Signature.FromSig.sigTy2type
d_sigTy2type_430 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 -> T_SigTy_268 -> AgdaAny
d_sigTy2type_430 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19
  = du_sigTy2type_430 v16
du_sigTy2type_430 :: AgdaAny -> AgdaAny
du_sigTy2type_430 v0 = coe v0
-- Builtin.Signature.FromSig.saturatedSigTy
d_saturatedSigTy_438 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  T_Sig_74 -> AgdaAny -> ()
d_saturatedSigTy_438 = erased
-- Builtin.Signature.FromSig.convSigTy
d_convSigTy_472 ::
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> ()) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 ->
   MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Type.T_Ctx'8902'_2 ->
   MAlonzo.Code.Utils.T_Kind_656 -> AgdaAny -> AgdaAny) ->
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
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_SigTy_268 -> T_SigTy_268
d_convSigTy_472 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 v24
  = du_convSigTy_472 v24
du_convSigTy_472 :: T_SigTy_268 -> T_SigTy_268
du_convSigTy_472 v0 = coe v0
