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

module MAlonzo.Code.Declarative where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Algorithmic
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Builtin.Signature
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.BetaNBE
import qualified MAlonzo.Code.Type.Equality
import qualified MAlonzo.Code.Type.RenamingSubstitution
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.Utils.List

-- Declarative._.mkTy
d_mkTy_6 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Builtin.Signature.T__'47'_'8866''8902'_26 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
d_mkTy_6
  = coe
      MAlonzo.Code.Builtin.Signature.du_mkTy_204 (coe (\ v0 v1 v2 -> v2))
      (coe (\ v0 v1 v2 v3 -> coe MAlonzo.Code.Type.C_'96'_22 v3))
      (\ v0 v1 v2 v3 v4 -> coe MAlonzo.Code.Type.C__'183'__30 v1 v3 v4)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Type.C_'94'_34))
      (\ v0 v1 -> coe MAlonzo.Code.Type.C_con_36 v1)
-- Declarative._.sig2type
d_sig2type_8 ::
  MAlonzo.Code.Builtin.Signature.T_Sig_72 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
d_sig2type_8
  = coe
      MAlonzo.Code.Builtin.Signature.du_sig2type_242
      (coe (\ v0 v1 v2 -> v2))
      (coe (\ v0 v1 v2 v3 -> coe MAlonzo.Code.Type.C_'96'_22 v3))
      (\ v0 v1 v2 v3 v4 -> coe MAlonzo.Code.Type.C__'183'__30 v1 v3 v4)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Type.C_'94'_34))
      (\ v0 v1 -> coe MAlonzo.Code.Type.C_con_36 v1)
      (\ v0 v1 v2 -> coe MAlonzo.Code.Type.C__'8658'__26 v1 v2)
      (\ v0 v1 v2 -> coe MAlonzo.Code.Type.C_Π_24 v1 v2)
-- Declarative._.sig2typeΠ
d_sig2typeΠ_10 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
d_sig2typeΠ_10
  = coe
      MAlonzo.Code.Builtin.Signature.du_sig2typeΠ_228
      (\ v0 v1 v2 -> coe MAlonzo.Code.Type.C_Π_24 v1 v2)
-- Declarative._.sig2type⇒
d_sig2type'8658'_12 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Builtin.Signature.T__'47'_'8866''8902'_26] ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
d_sig2type'8658'_12
  = coe
      MAlonzo.Code.Builtin.Signature.du_sig2type'8658'_214
      (coe (\ v0 v1 v2 -> v2))
      (coe (\ v0 v1 v2 v3 -> coe MAlonzo.Code.Type.C_'96'_22 v3))
      (\ v0 v1 v2 v3 v4 -> coe MAlonzo.Code.Type.C__'183'__30 v1 v3 v4)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Type.C_'94'_34))
      (\ v0 v1 -> coe MAlonzo.Code.Type.C_con_36 v1)
      (\ v0 v1 v2 -> coe MAlonzo.Code.Type.C__'8658'__26 v1 v2)
-- Declarative._.⊢♯2TyNe♯
d_'8866''9839'2TyNe'9839'_14 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
d_'8866''9839'2TyNe'9839'_14
  = coe
      MAlonzo.Code.Builtin.Signature.du_'8866''9839'2TyNe'9839'_186
      (coe (\ v0 v1 v2 -> v2))
      (coe (\ v0 v1 v2 v3 -> coe MAlonzo.Code.Type.C_'96'_22 v3))
      (\ v0 v1 v2 v3 v4 -> coe MAlonzo.Code.Type.C__'183'__30 v1 v3 v4)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Type.C_'94'_34))
-- Declarative.Ctx
d_Ctx_16 a0 = ()
data T_Ctx_16
  = C_'8709'_18 | C__'44''8902'__22 T_Ctx_16 |
    C__'44'__26 T_Ctx_16 MAlonzo.Code.Type.T__'8866''8902'__20
-- Declarative._∋_
d__'8715'__34 a0 a1 a2 = ()
data T__'8715'__34
  = C_Z_36 | C_S_38 T__'8715'__34 |
    C_T_40 MAlonzo.Code.Type.T__'8866''8902'__20 T__'8715'__34
-- Declarative.btype
d_btype_42 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
d_btype_42 v0 v1
  = coe
      MAlonzo.Code.Type.RenamingSubstitution.d_sub'8709'_896 (coe v0)
      (coe MAlonzo.Code.Utils.C_'42'_654)
      (coe
         MAlonzo.Code.Builtin.Signature.du_sig2type_242
         (coe (\ v2 v3 v4 -> v4))
         (coe (\ v2 v3 v4 v5 -> coe MAlonzo.Code.Type.C_'96'_22 v5))
         (\ v2 v3 v4 v5 v6 -> coe MAlonzo.Code.Type.C__'183'__30 v3 v5 v6)
         (coe (\ v2 v3 -> coe MAlonzo.Code.Type.C_'94'_34))
         (\ v2 v3 -> coe MAlonzo.Code.Type.C_con_36 v3)
         (\ v2 v3 v4 -> coe MAlonzo.Code.Type.C__'8658'__26 v3 v4)
         (\ v2 v3 v4 -> coe MAlonzo.Code.Type.C_Π_24 v3 v4)
         (coe MAlonzo.Code.Builtin.d_signature_298 (coe v1)))
-- Declarative.btype-ren
d_btype'45'ren_50 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  (MAlonzo.Code.Utils.T_Kind_652 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_btype'45'ren_50 = erased
-- Declarative.btype-sub
d_btype'45'sub_60 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  (MAlonzo.Code.Utils.T_Kind_652 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8866''8902'__20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_btype'45'sub_60 = erased
-- Declarative.⟦_⟧d
d_'10214'_'10215'd_68 ::
  MAlonzo.Code.Type.T__'8866''8902'__20 -> ()
d_'10214'_'10215'd_68 = erased
-- Declarative.ty2TyTag
d_ty2TyTag_74 ::
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4
d_ty2TyTag_74 v0
  = coe
      MAlonzo.Code.Algorithmic.d_ty2sty_64
      (coe
         MAlonzo.Code.Type.BetaNBE.d_nf_258
         (coe MAlonzo.Code.Type.C_'8709'_4)
         (coe MAlonzo.Code.Utils.C_'9839'_656) (coe v0))
-- Declarative.mkCaseType
d_mkCaseType_82 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Type.T__'8866''8902'__20
d_mkCaseType_82 ~v0 v1 v2 = du_mkCaseType_82 v1 v2
du_mkCaseType_82 ::
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  [MAlonzo.Code.Type.T__'8866''8902'__20] ->
  MAlonzo.Code.Type.T__'8866''8902'__20
du_mkCaseType_82 v0 v1
  = case coe v1 of
      [] -> coe v0
      (:) v2 v3
        -> coe
             MAlonzo.Code.Type.C__'8658'__26 v2
             (coe du_mkCaseType_82 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Declarative.ConstrArgs
d_ConstrArgs_94 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  T_Ctx_16 -> [MAlonzo.Code.Type.T__'8866''8902'__20] -> ()
d_ConstrArgs_94 = erased
-- Declarative.Cases
d_Cases_104 a0 a1 a2 a3 a4 = ()
data T_Cases_104
  = C_'91''93'_180 | C__'8759'__192 T__'8866'__110 T_Cases_104
-- Declarative._⊢_
d__'8866'__110 a0 a1 a2 = ()
data T__'8866'__110
  = C_'96'_114 T__'8715'__34 | C_ƛ_116 T__'8866'__110 |
    C__'183'__118 MAlonzo.Code.Type.T__'8866''8902'__20 T__'8866'__110
                  T__'8866'__110 |
    C_Λ_120 T__'8866'__110 |
    C__'183''8902'__124 MAlonzo.Code.Utils.T_Kind_652
                        MAlonzo.Code.Type.T__'8866''8902'__20 T__'8866'__110
                        MAlonzo.Code.Type.T__'8866''8902'__20 |
    C_wrap_130 T__'8866'__110 | C_unwrap_132 T__'8866'__110 |
    C_constr_142 MAlonzo.Code.Data.Fin.Base.T_Fin_10
                 [MAlonzo.Code.Type.T__'8866''8902'__20]
                 MAlonzo.Code.Utils.List.T_IList_302 |
    C_case_154 Integer MAlonzo.Code.Data.Vec.Base.T_Vec_28
               T__'8866'__110 T_Cases_104 |
    C_conv_156 MAlonzo.Code.Type.T__'8866''8902'__20
               MAlonzo.Code.Type.Equality.T__'8801'β__10 T__'8866'__110 |
    C_con_162 MAlonzo.Code.Type.T__'8866''8902'__20 AgdaAny
              MAlonzo.Code.Type.Equality.T__'8801'β__10 |
    C_builtin_166 MAlonzo.Code.Builtin.T_Builtin_2 | C_error_170
-- Declarative.conv∋
d_conv'8715'_194 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  T_Ctx_16 ->
  T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8715'__34 -> T__'8715'__34
d_conv'8715'_194 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_conv'8715'_194 v7
du_conv'8715'_194 :: T__'8715'__34 -> T__'8715'__34
du_conv'8715'_194 v0 = coe v0
-- Declarative.conv⊢
d_conv'8866'_198 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  T_Ctx_16 ->
  T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8866'__110 -> T__'8866'__110
d_conv'8866'_198 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_conv'8866'_198 v7
du_conv'8866'_198 :: T__'8866'__110 -> T__'8866'__110
du_conv'8866'_198 v0 = coe v0
-- Declarative.typeOf
d_typeOf_204 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  T_Ctx_16 -> T__'8866'__110 -> MAlonzo.Code.Type.T__'8866''8902'__20
d_typeOf_204 ~v0 v1 ~v2 ~v3 = du_typeOf_204 v1
du_typeOf_204 ::
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
du_typeOf_204 v0 = coe v0
-- Declarative.typeOf∋
d_typeOf'8715'_210 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  T_Ctx_16 -> T__'8715'__34 -> MAlonzo.Code.Type.T__'8866''8902'__20
d_typeOf'8715'_210 ~v0 v1 ~v2 ~v3 = du_typeOf'8715'_210 v1
du_typeOf'8715'_210 ::
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
du_typeOf'8715'_210 v0 = coe v0
-- Declarative.piBody
d_piBody_216 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_652 ->
  T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  T__'8866'__110 -> MAlonzo.Code.Type.T__'8866''8902'__20
d_piBody_216 ~v0 ~v1 ~v2 v3 ~v4 = du_piBody_216 v3
du_piBody_216 ::
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
du_piBody_216 v0 = coe v0
-- Declarative.muPat
d_muPat_222 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_652 ->
  T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  T__'8866'__110 -> MAlonzo.Code.Type.T__'8866''8902'__20
d_muPat_222 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_muPat_222 v4
du_muPat_222 ::
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
du_muPat_222 v0 = coe v0
-- Declarative.muArg
d_muArg_228 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_652 ->
  T_Ctx_16 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  T__'8866'__110 -> MAlonzo.Code.Type.T__'8866''8902'__20
d_muArg_228 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_muArg_228 v4
du_muArg_228 ::
  MAlonzo.Code.Type.T__'8866''8902'__20 ->
  MAlonzo.Code.Type.T__'8866''8902'__20
du_muArg_228 v0 = coe v0
