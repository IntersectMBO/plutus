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

module MAlonzo.Code.Type.BetaNormal where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Builtin.Constant.Type
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.RenamingSubstitution
import qualified MAlonzo.Code.Utils

-- Type.BetaNormal._⊢Nf⋆_
d__'8866'Nf'8902'__4 a0 a1 = ()
data T__'8866'Nf'8902'__4
  = C_Π_14 MAlonzo.Code.Utils.T_Kind_682 T__'8866'Nf'8902'__4 |
    C__'8658'__16 T__'8866'Nf'8902'__4 T__'8866'Nf'8902'__4 |
    C_ƛ_18 T__'8866'Nf'8902'__4 | C_ne_20 T__'8866'Ne'8902'__6 |
    C_con_22 T__'8866'Nf'8902'__4 |
    C_μ_24 MAlonzo.Code.Utils.T_Kind_682 T__'8866'Nf'8902'__4
           T__'8866'Nf'8902'__4 |
    C_SOP_28 Integer MAlonzo.Code.Data.Vec.Base.T_Vec_28
-- Type.BetaNormal._⊢Ne⋆_
d__'8866'Ne'8902'__6 a0 a1 = ()
data T__'8866'Ne'8902'__6
  = C_'96'_8 MAlonzo.Code.Type.T__'8715''8902'__14 |
    C__'183'__10 MAlonzo.Code.Utils.T_Kind_682 T__'8866'Ne'8902'__6
                 T__'8866'Nf'8902'__4 |
    C_'94'_12 MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6
-- Type.BetaNormal.RenNf
d_RenNf_30 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 -> ()
d_RenNf_30 = erased
-- Type.BetaNormal.RenNe
d_RenNe_38 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 -> ()
d_RenNe_38 = erased
-- Type.BetaNormal.renNf
d_renNf_46 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  T__'8866'Nf'8902'__4 -> T__'8866'Nf'8902'__4
d_renNf_46 v0 v1 v2 v3 v4
  = case coe v4 of
      C_Π_14 v6 v7
        -> coe
             C_Π_14 v6
             (d_renNf_46
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v6))
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v6))
                (coe MAlonzo.Code.Type.RenamingSubstitution.du_ext_18 (coe v2))
                (coe MAlonzo.Code.Utils.C_'42'_684) (coe v7))
      C__'8658'__16 v6 v7
        -> coe
             C__'8658'__16
             (d_renNf_46
                (coe v0) (coe v1) (coe v2) (coe MAlonzo.Code.Utils.C_'42'_684)
                (coe v6))
             (d_renNf_46
                (coe v0) (coe v1) (coe v2) (coe MAlonzo.Code.Utils.C_'42'_684)
                (coe v7))
      C_ƛ_18 v8
        -> case coe v3 of
             MAlonzo.Code.Utils.C__'8658'__688 v9 v10
               -> coe
                    C_ƛ_18
                    (d_renNf_46
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v9))
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v1) (coe v9))
                       (coe MAlonzo.Code.Type.RenamingSubstitution.du_ext_18 (coe v2))
                       (coe v10) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ne_20 v7
        -> coe
             C_ne_20 (d_renNe_48 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7))
      C_con_22 v6
        -> coe
             C_con_22
             (d_renNf_46
                (coe v0) (coe v1) (coe v2) (coe MAlonzo.Code.Utils.C_'9839'_686)
                (coe v6))
      C_μ_24 v6 v7 v8
        -> coe
             C_μ_24 v6
             (d_renNf_46
                (coe v0) (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Utils.C__'8658'__688
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__688 (coe v6)
                      (coe MAlonzo.Code.Utils.C_'42'_684))
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__688 (coe v6)
                      (coe MAlonzo.Code.Utils.C_'42'_684)))
                (coe v7))
             (d_renNf_46 (coe v0) (coe v1) (coe v2) (coe v6) (coe v8))
      C_SOP_28 v6 v7
        -> coe
             C_SOP_28 v6
             (coe
                du_renNf'45'VecList_58 (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Utils.C_'42'_684) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNormal.renNe
d_renNe_48 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  T__'8866'Ne'8902'__6 -> T__'8866'Ne'8902'__6
d_renNe_48 v0 v1 v2 v3 v4
  = case coe v4 of
      C_'96'_8 v7 -> coe C_'96'_8 (coe v2 v3 v7)
      C__'183'__10 v6 v8 v9
        -> coe
             C__'183'__10 v6
             (d_renNe_48
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Utils.C__'8658'__688 (coe v6) (coe v3)) (coe v8))
             (d_renNf_46 (coe v0) (coe v1) (coe v2) (coe v6) (coe v9))
      C_'94'_12 v7 -> coe C_'94'_12 v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNormal.renNf-List
d_renNf'45'List_52 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  [T__'8866'Nf'8902'__4] -> [T__'8866'Nf'8902'__4]
d_renNf'45'List_52 v0 v1 v2 v3 v4
  = case coe v4 of
      [] -> coe v4
      (:) v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_renNf_46 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
             (coe
                d_renNf'45'List_52 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNormal.renNf-VecList
d_renNf'45'VecList_58 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  Integer ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_renNf'45'VecList_58 v0 v1 ~v2 v3 v4 v5
  = du_renNf'45'VecList_58 v0 v1 v3 v4 v5
du_renNf'45'VecList_58 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_renNf'45'VecList_58 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe v4
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
        -> coe
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38
             (d_renNf'45'List_52 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
             (coe
                du_renNf'45'VecList_58 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNormal.weakenNf
d_weakenNf_122 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  T__'8866'Nf'8902'__4 -> T__'8866'Nf'8902'__4
d_weakenNf_122 v0 v1 v2
  = coe
      d_renNf_46 (coe v0)
      (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v2))
      (coe (\ v3 -> coe MAlonzo.Code.Type.C_S_18)) (coe v1)
-- Type.BetaNormal.embNf
d_embNf_128 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  T__'8866'Nf'8902'__4 -> MAlonzo.Code.Type.T__'8866''8902'__20
d_embNf_128 v0 v1 v2
  = case coe v2 of
      C_Π_14 v4 v5
        -> coe
             MAlonzo.Code.Type.C_Π_24 v4
             (d_embNf_128
                (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v4))
                (coe MAlonzo.Code.Utils.C_'42'_684) (coe v5))
      C__'8658'__16 v4 v5
        -> coe
             MAlonzo.Code.Type.C__'8658'__26
             (d_embNf_128 (coe v0) (coe MAlonzo.Code.Utils.C_'42'_684) (coe v4))
             (d_embNf_128 (coe v0) (coe MAlonzo.Code.Utils.C_'42'_684) (coe v5))
      C_ƛ_18 v6
        -> case coe v1 of
             MAlonzo.Code.Utils.C__'8658'__688 v7 v8
               -> coe
                    MAlonzo.Code.Type.C_ƛ_28
                    (d_embNf_128
                       (coe MAlonzo.Code.Type.C__'44''8902'__6 (coe v0) (coe v7)) (coe v8)
                       (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ne_20 v5 -> coe du_embNe_134 (coe v0) (coe v5)
      C_con_22 v4
        -> coe
             MAlonzo.Code.Type.C_con_36
             (d_embNf_128
                (coe v0) (coe MAlonzo.Code.Utils.C_'9839'_686) (coe v4))
      C_μ_24 v4 v5 v6
        -> coe
             MAlonzo.Code.Type.C_μ_32 v4
             (d_embNf_128
                (coe v0)
                (coe
                   MAlonzo.Code.Utils.C__'8658'__688
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__688 (coe v4)
                      (coe MAlonzo.Code.Utils.C_'42'_684))
                   (coe
                      MAlonzo.Code.Utils.C__'8658'__688 (coe v4)
                      (coe MAlonzo.Code.Utils.C_'42'_684)))
                (coe v5))
             (d_embNf_128 (coe v0) (coe v4) (coe v6))
      C_SOP_28 v4 v5
        -> coe
             MAlonzo.Code.Type.C_SOP_40 v4
             (coe
                du_embNf'45'VecList_148 (coe v0)
                (coe MAlonzo.Code.Utils.C_'42'_684) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNormal.embNe
d_embNe_134 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  T__'8866'Ne'8902'__6 -> MAlonzo.Code.Type.T__'8866''8902'__20
d_embNe_134 v0 ~v1 v2 = du_embNe_134 v0 v2
du_embNe_134 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  T__'8866'Ne'8902'__6 -> MAlonzo.Code.Type.T__'8866''8902'__20
du_embNe_134 v0 v1
  = case coe v1 of
      C_'96'_8 v4 -> coe MAlonzo.Code.Type.C_'96'_22 v4
      C__'183'__10 v3 v5 v6
        -> coe
             MAlonzo.Code.Type.C__'183'__30 v3
             (coe du_embNe_134 (coe v0) (coe v5))
             (d_embNf_128 (coe v0) (coe v3) (coe v6))
      C_'94'_12 v4 -> coe MAlonzo.Code.Type.C_'94'_34 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNormal.embNf-List
d_embNf'45'List_140 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  [T__'8866'Nf'8902'__4] -> [MAlonzo.Code.Type.T__'8866''8902'__20]
d_embNf'45'List_140 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_embNf_128 (coe v0) (coe v1) (coe v3))
             (coe d_embNf'45'List_140 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNormal.embNf-VecList
d_embNf'45'VecList_148 ::
  Integer ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_embNf'45'VecList_148 ~v0 v1 v2 v3
  = du_embNf'45'VecList_148 v1 v2 v3
du_embNf'45'VecList_148 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_embNf'45'VecList_148 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32 -> coe v2
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v4 v5
        -> coe
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38
             (d_embNf'45'List_140 (coe v0) (coe v1) (coe v4))
             (coe du_embNf'45'VecList_148 (coe v0) (coe v1) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Type.BetaNormal.ren-embNf
d_ren'45'embNf_190 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'embNf_190 = erased
-- Type.BetaNormal.ren-embNe
d_ren'45'embNe_198 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  T__'8866'Ne'8902'__6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'embNe_198 = erased
-- Type.BetaNormal.ren-embNf-List
d_ren'45'embNf'45'List_206 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  [T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'embNf'45'List_206 = erased
-- Type.BetaNormal.ren-embNf-VecList
d_ren'45'embNf'45'VecList_216 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  Integer ->
  MAlonzo.Code.Utils.T_Kind_682 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'embNf'45'VecList_216 = erased
-- Type.BetaNormal._.lookup-renNf-VecList
d_lookup'45'renNf'45'VecList_296 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  Integer ->
  (MAlonzo.Code.Utils.T_Kind_682 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'renNf'45'VecList_296 = erased
-- Type.BetaNormal._.lookup-embNf-VecList
d_lookup'45'embNf'45'VecList_312 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'embNf'45'VecList_312 = erased
