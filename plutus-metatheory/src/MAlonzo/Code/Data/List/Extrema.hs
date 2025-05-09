{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Data.List.Extrema where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.List.Base qualified
import MAlonzo.Code.Data.List.Extrema.Core qualified
import MAlonzo.Code.Data.List.Membership.Propositional qualified
import MAlonzo.Code.Data.List.Membership.Propositional.Properties qualified
import MAlonzo.Code.Data.List.Membership.Setoid.Properties qualified
import MAlonzo.Code.Data.List.Properties qualified
import MAlonzo.Code.Data.List.Relation.Unary.All qualified
import MAlonzo.Code.Data.List.Relation.Unary.Any qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.List.Extrema._._<_
d__'60'__94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny -> ()
d__'60'__94 = erased
-- Data.List.Extrema.argmin
d_argmin_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
d_argmin_132 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 = du_argmin_132 v3 v6
du_argmin_132 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
du_argmin_132 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480'_344 v0 v1)
-- Data.List.Extrema.argmax
d_argmax_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
d_argmax_136 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 = du_argmax_136 v3 v6
du_argmax_136 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
du_argmax_136 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_346 v0 v1)
-- Data.List.Extrema.min
d_min_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> [AgdaAny] -> AgdaAny
d_min_140 ~v0 ~v1 ~v2 v3 = du_min_140 v3
du_min_140 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> [AgdaAny] -> AgdaAny
du_min_140 v0 = coe du_argmin_132 (coe v0) (coe (\ v1 -> v1))
-- Data.List.Extrema.max
d_max_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> [AgdaAny] -> AgdaAny
d_max_142 ~v0 ~v1 ~v2 v3 = du_max_142 v3
du_max_142 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> [AgdaAny] -> AgdaAny
du_max_142 v0 = coe du_argmax_136 (coe v0) (coe (\ v1 -> v1))
-- Data.List.Extrema._.f[argmin]≤v⁺
d_f'91'argmin'93''8804'v'8314'_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_f'91'argmin'93''8804'v'8314'_160 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_f'91'argmin'93''8804'v'8314'_160 v3 v6 v7
du_f'91'argmin'93''8804'v'8314'_160 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_f'91'argmin'93''8804'v'8314'_160 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'preserves'7506'_4252
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480'_344 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480''45'pres'7506''45''8804'v_362
         (coe v0) (coe v1) (coe v2))
-- Data.List.Extrema._.f[argmin]<v⁺
d_f'91'argmin'93''60'v'8314'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_f'91'argmin'93''60'v'8314'_170 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_f'91'argmin'93''60'v'8314'_170 v3 v6 v7
du_f'91'argmin'93''60'v'8314'_170 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_f'91'argmin'93''60'v'8314'_170 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'preserves'7506'_4252
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480'_344 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480''45'pres'7506''45''60'v_374
         (coe v0) (coe v1) (coe v2))
-- Data.List.Extrema._.v≤f[argmin]⁺
d_v'8804'f'91'argmin'93''8314'_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_v'8804'f'91'argmin'93''8314'_180 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 ~v7 v8
                                   v9
  = du_v'8804'f'91'argmin'93''8314'_180 v3 v6 v8 v9
du_v'8804'f'91'argmin'93''8314'_180 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_v'8804'f'91'argmin'93''8314'_180 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'preserves'7495'_4212
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480'_344 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480''45'pres'7495''45'v'8804'_386
         (coe v0) (coe v1))
      (coe v2) (coe v3)
-- Data.List.Extrema._.v<f[argmin]⁺
d_v'60'f'91'argmin'93''8314'_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_v'60'f'91'argmin'93''8314'_190 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 ~v7 v8
                                 v9
  = du_v'60'f'91'argmin'93''8314'_190 v3 v6 v8 v9
du_v'60'f'91'argmin'93''8314'_190 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_v'60'f'91'argmin'93''8314'_190 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'preserves'7495'_4212
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480'_344 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480''45'pres'7495''45'v'60'_402
         (coe v0) (coe v1))
      (coe v2) (coe v3)
-- Data.List.Extrema._.f[argmin]≤f[⊤]
d_f'91'argmin'93''8804'f'91''8868''93'_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
d_f'91'argmin'93''8804'f'91''8868''93'_196 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                           v6 v7 v8
  = du_f'91'argmin'93''8804'f'91''8868''93'_196 v3 v6 v7 v8
du_f'91'argmin'93''8804'f'91''8868''93'_196 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
du_f'91'argmin'93''8804'f'91''8868''93'_196 v0 v1 v2 v3
  = coe
      du_f'91'argmin'93''8804'v'8314'_160 v0 v1 (coe v1 v2) v2 v3
      (coe
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
         (let v4
                = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
          coe
            (let v5
                   = coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v4) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_refl_98
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v5))
                  (coe v1 v2)))))
-- Data.List.Extrema._.f[argmin]≤f[xs]
d_f'91'argmin'93''8804'f'91'xs'93'_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_f'91'argmin'93''8804'f'91'xs'93'_208 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
                                       v8
  = du_f'91'argmin'93''8804'f'91'xs'93'_208 v3 v6 v7 v8
du_f'91'argmin'93''8804'f'91'xs'93'_208 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_f'91'argmin'93''8804'f'91'xs'93'_208 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'forces'7495'_4190
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480'_344 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480''45'forces'7495''45'v'8804'_418
         (coe v0) (coe v1) (coe v1 (coe du_argmin_132 v0 v1 v2 v3)))
      (coe v2) (coe v3)
      (let v4
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
       coe
         (let v5
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_98
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v5))
               (coe v1 (coe du_argmin_132 v0 v1 v2 v3)))))
-- Data.List.Extrema._.f[argmin]≈f[v]⁺
d_f'91'argmin'93''8776'f'91'v'93''8314'_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
d_f'91'argmin'93''8776'f'91'v'93''8314'_222 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                            v6 v7 v8 v9 v10 v11 v12
  = du_f'91'argmin'93''8776'f'91'v'93''8314'_222
      v3 v6 v7 v8 v9 v10 v11 v12
du_f'91'argmin'93''8776'f'91'v'93''8314'_222 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
du_f'91'argmin'93''8776'f'91'v'93''8314'_222 v0 v1 v2 v3 v4 v5 v6
                                             v7
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_412
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_786 (coe v0)))
      (coe v1 (coe du_argmin_132 v0 v1 v3 v4)) (coe v1 v2)
      (coe
         du_f'91'argmin'93''8804'v'8314'_160 v0 v1 (coe v1 v2) v3 v4
         (coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            (coe
               MAlonzo.Code.Data.List.Membership.Propositional.du_lose_50 v2 v4 v5
               (let v8
                      = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
                coe
                  (let v9
                         = coe
                             MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v8) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_refl_98
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v9))
                        (coe v1 v2)))))))
      (coe du_v'8804'f'91'argmin'93''8314'_180 v0 v1 v3 v4 v7 v6)
-- Data.List.Extrema.argmin[xs]≤argmin[ys]⁺
d_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_248 ~v0 ~v1 ~v2 v3
                                                   ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_248
      v3 v6 v7 v8 v9 v10 v11 v12 v13
du_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_248 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_248 v0 v1 v2 v3 v4
                                                    v5 v6 v7 v8
  = coe
      du_v'8804'f'91'argmin'93''8314'_180 v0 v2 v4 v6
      (coe
         du_f'91'argmin'93''8804'v'8314'_160 v0 v1 (coe v2 v4) v3 v5 v7)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
         (coe
            (\ v9 ->
               coe du_f'91'argmin'93''8804'v'8314'_160 v0 v1 (coe v2 v9) v3 v5))
         (coe v6) (coe v8))
-- Data.List.Extrema.argmin[xs]<argmin[ys]⁺
d_argmin'91'xs'93''60'argmin'91'ys'93''8314'_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_argmin'91'xs'93''60'argmin'91'ys'93''8314'_276 ~v0 ~v1 ~v2 v3 ~v4
                                                 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du_argmin'91'xs'93''60'argmin'91'ys'93''8314'_276
      v3 v6 v7 v8 v9 v10 v11 v12 v13
du_argmin'91'xs'93''60'argmin'91'ys'93''8314'_276 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_argmin'91'xs'93''60'argmin'91'ys'93''8314'_276 v0 v1 v2 v3 v4 v5
                                                  v6 v7 v8
  = coe
      du_v'60'f'91'argmin'93''8314'_190 v0 v2 v4 v6
      (coe du_f'91'argmin'93''60'v'8314'_170 v0 v1 (coe v2 v4) v3 v5 v7)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
         (coe
            (\ v9 ->
               coe du_f'91'argmin'93''60'v'8314'_170 v0 v1 (coe v2 v9) v3 v5))
         (coe v6) (coe v8))
-- Data.List.Extrema.argmin-sel
d_argmin'45'sel_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_argmin'45'sel_292 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_argmin'45'sel_292 v3 v6
du_argmin'45'sel_292 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_argmin'45'sel_292 v0 v1
  = coe
      MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_foldr'45'selective_682
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480'_344 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480''45'sel_350
         (coe v0) (coe v1))
-- Data.List.Extrema.argmin-all
d_argmin'45'all_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_argmin'45'all_304 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 ~v10 v11
                    v12
  = du_argmin'45'all_304 v3 v7 v8 v9 v11 v12
du_argmin'45'all_304 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_argmin'45'all_304 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Data.List.Membership.Setoid.Properties.du_foldr'45'selective_1712
              (coe
                 MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
              (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480'_344 v0 v1)
              (coe
                 MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480''45'sel_350
                 (coe v0) (coe v1))
              (coe v2) (coe v3) in
    coe
      (case coe v6 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> coe v4
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
           -> coe
                MAlonzo.Code.Data.List.Relation.Unary.All.du_lookup_434 v3 v5 v7
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.List.Extrema._.v≤f[argmax]⁺
d_v'8804'f'91'argmax'93''8314'_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_v'8804'f'91'argmax'93''8314'_366 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_v'8804'f'91'argmax'93''8314'_366 v3 v6 v7
du_v'8804'f'91'argmax'93''8314'_366 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_v'8804'f'91'argmax'93''8314'_366 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'preserves'7506'_4252
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_346 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480''45'pres'7506''45'v'8804'_446
         (coe v0) (coe v1) (coe v2))
-- Data.List.Extrema._.v<f[argmax]⁺
d_v'60'f'91'argmax'93''8314'_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_v'60'f'91'argmax'93''8314'_376 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_v'60'f'91'argmax'93''8314'_376 v3 v6 v7
du_v'60'f'91'argmax'93''8314'_376 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_v'60'f'91'argmax'93''8314'_376 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'preserves'7506'_4252
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_346 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480''45'pres'7506''45'v'60'_468
         (coe v0) (coe v1) (coe v2))
-- Data.List.Extrema._.f[argmax]≤v⁺
d_f'91'argmax'93''8804'v'8314'_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_f'91'argmax'93''8804'v'8314'_386 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 ~v7 v8
                                   v9
  = du_f'91'argmax'93''8804'v'8314'_386 v3 v6 v8 v9
du_f'91'argmax'93''8804'v'8314'_386 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_f'91'argmax'93''8804'v'8314'_386 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'preserves'7495'_4212
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_346 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480''45'pres'7495''45''8804'v_490
         (coe v0) (coe v1))
      (coe v2) (coe v3)
-- Data.List.Extrema._.f[argmax]<v⁺
d_f'91'argmax'93''60'v'8314'_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_f'91'argmax'93''60'v'8314'_396 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 ~v7 v8
                                 v9
  = du_f'91'argmax'93''60'v'8314'_396 v3 v6 v8 v9
du_f'91'argmax'93''60'v'8314'_396 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_f'91'argmax'93''60'v'8314'_396 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'preserves'7495'_4212
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_346 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480''45'pres'7495''45''60'v_506
         (coe v0) (coe v1))
      (coe v2) (coe v3)
-- Data.List.Extrema._.f[⊥]≤f[argmax]
d_f'91''8869''93''8804'f'91'argmax'93'_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
d_f'91''8869''93''8804'f'91'argmax'93'_402 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                           v6 v7 v8
  = du_f'91''8869''93''8804'f'91'argmax'93'_402 v3 v6 v7 v8
du_f'91''8869''93''8804'f'91'argmax'93'_402 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
du_f'91''8869''93''8804'f'91'argmax'93'_402 v0 v1 v2 v3
  = coe
      du_v'8804'f'91'argmax'93''8314'_366 v0 v1 (coe v1 v2) v2 v3
      (coe
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
         (let v4
                = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
          coe
            (let v5
                   = coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v4) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_refl_98
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v5))
                  (coe v1 v2)))))
-- Data.List.Extrema._.f[xs]≤f[argmax]
d_f'91'xs'93''8804'f'91'argmax'93'_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_f'91'xs'93''8804'f'91'argmax'93'_414 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
                                       v8
  = du_f'91'xs'93''8804'f'91'argmax'93'_414 v3 v6 v7 v8
du_f'91'xs'93''8804'f'91'argmax'93'_414 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_f'91'xs'93''8804'f'91'argmax'93'_414 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'forces'7495'_4190
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_346 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480''45'forces'7495''45''8804'v_522
         (coe v0) (coe v1) (coe v1 (coe du_argmax_136 v0 v1 v2 v3)))
      (coe v2) (coe v3)
      (let v4
             = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
       coe
         (let v5
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v4) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_98
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v5))
               (coe
                  v1
                  (coe
                     MAlonzo.Code.Data.List.Base.du_foldr_216
                     (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_346 v0 v1)
                     (coe v2) (coe v3))))))
-- Data.List.Extrema._.f[argmax]≈f[v]⁺
d_f'91'argmax'93''8776'f'91'v'93''8314'_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
d_f'91'argmax'93''8776'f'91'v'93''8314'_428 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                            v6 v7 v8 v9 v10 v11 v12
  = du_f'91'argmax'93''8776'f'91'v'93''8314'_428
      v3 v6 v7 v8 v9 v10 v11 v12
du_f'91'argmax'93''8776'f'91'v'93''8314'_428 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
du_f'91'argmax'93''8776'f'91'v'93''8314'_428 v0 v1 v2 v3 v4 v5 v6
                                             v7
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_412
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_786 (coe v0)))
      (coe v1 (coe du_argmax_136 v0 v1 v3 v4)) (coe v1 v2)
      (coe du_f'91'argmax'93''8804'v'8314'_386 v0 v1 v3 v4 v7 v6)
      (coe
         du_v'8804'f'91'argmax'93''8314'_366 v0 v1 (coe v1 v2) v3 v4
         (coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            (coe
               MAlonzo.Code.Data.List.Membership.Propositional.du_lose_50 v2 v4 v5
               (let v8
                      = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
                coe
                  (let v9
                         = coe
                             MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v8) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_refl_98
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v9))
                        (coe v1 v2)))))))
-- Data.List.Extrema.argmax[xs]≤argmax[ys]⁺
d_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_454 ~v0 ~v1 ~v2 v3
                                                   ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_454
      v3 v6 v7 v8 v9 v10 v11 v12 v13
du_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_454 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_454 v0 v1 v2 v3 v4
                                                    v5 v6 v7 v8
  = coe
      du_f'91'argmax'93''8804'v'8314'_386 v0 v1 v3 v5
      (coe
         du_v'8804'f'91'argmax'93''8314'_366 v0 v2 (coe v1 v3) v4 v6 v7)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
         (coe
            (\ v9 ->
               coe du_v'8804'f'91'argmax'93''8314'_366 v0 v2 (coe v1 v9) v4 v6))
         (coe v5) (coe v8))
-- Data.List.Extrema.argmax[xs]<argmax[ys]⁺
d_argmax'91'xs'93''60'argmax'91'ys'93''8314'_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_argmax'91'xs'93''60'argmax'91'ys'93''8314'_482 ~v0 ~v1 ~v2 v3 ~v4
                                                 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du_argmax'91'xs'93''60'argmax'91'ys'93''8314'_482
      v3 v6 v7 v8 v9 v10 v11 v12 v13
du_argmax'91'xs'93''60'argmax'91'ys'93''8314'_482 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_argmax'91'xs'93''60'argmax'91'ys'93''8314'_482 v0 v1 v2 v3 v4 v5
                                                  v6 v7 v8
  = coe
      du_f'91'argmax'93''60'v'8314'_396 v0 v1 v3 v5
      (coe du_v'60'f'91'argmax'93''8314'_376 v0 v2 (coe v1 v3) v4 v6 v7)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
         (coe
            (\ v9 ->
               coe du_v'60'f'91'argmax'93''8314'_376 v0 v2 (coe v1 v9) v4 v6))
         (coe v5) (coe v8))
-- Data.List.Extrema.argmax-sel
d_argmax'45'sel_498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_argmax'45'sel_498 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_argmax'45'sel_498 v3 v6
du_argmax'45'sel_498 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_argmax'45'sel_498 v0 v1
  = coe
      MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_foldr'45'selective_682
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_346 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480''45'sel_434
         (coe v0) (coe v1))
-- Data.List.Extrema.argmax-all
d_argmax'45'all_510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_argmax'45'all_510 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 ~v8 v9 v10 v11
                    v12
  = du_argmax'45'all_510 v3 v7 v9 v10 v11 v12
du_argmax'45'all_510 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_argmax'45'all_510 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Data.List.Membership.Setoid.Properties.du_foldr'45'selective_1712
              (coe
                 MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
              (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_346 v0 v1)
              (coe
                 MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480''45'sel_434
                 (coe v0) (coe v1))
              (coe v2) (coe v3) in
    coe
      (case coe v6 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> coe v4
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
           -> coe
                MAlonzo.Code.Data.List.Relation.Unary.All.du_lookup_434 v3 v5 v7
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.List.Extrema.min≤v⁺
d_min'8804'v'8314'_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_min'8804'v'8314'_564 ~v0 ~v1 ~v2 v3 v4
  = du_min'8804'v'8314'_564 v3 v4
du_min'8804'v'8314'_564 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_min'8804'v'8314'_564 v0 v1
  = coe
      du_f'91'argmin'93''8804'v'8314'_160 (coe v0) (coe (\ v2 -> v2))
      (coe v1)
-- Data.List.Extrema.min<v⁺
d_min'60'v'8314'_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_min'60'v'8314'_574 ~v0 ~v1 ~v2 v3 v4
  = du_min'60'v'8314'_574 v3 v4
du_min'60'v'8314'_574 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_min'60'v'8314'_574 v0 v1
  = coe
      du_f'91'argmin'93''60'v'8314'_170 (coe v0) (coe (\ v2 -> v2))
      (coe v1)
-- Data.List.Extrema.v≤min⁺
d_v'8804'min'8314'_584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_v'8804'min'8314'_584 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_v'8804'min'8314'_584 v3 v5 v6
du_v'8804'min'8314'_584 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_v'8804'min'8314'_584 v0 v1 v2
  = coe
      du_v'8804'f'91'argmin'93''8314'_180 (coe v0) (coe (\ v3 -> v3))
      (coe v1) (coe v2)
-- Data.List.Extrema.v<min⁺
d_v'60'min'8314'_594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_v'60'min'8314'_594 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_v'60'min'8314'_594 v3 v5 v6
du_v'60'min'8314'_594 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_v'60'min'8314'_594 v0 v1 v2
  = coe
      du_v'60'f'91'argmin'93''8314'_190 (coe v0) (coe (\ v3 -> v3))
      (coe v1) (coe v2)
-- Data.List.Extrema.min≤⊤
d_min'8804''8868'_600 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> [AgdaAny] -> AgdaAny
d_min'8804''8868'_600 ~v0 ~v1 ~v2 v3 = du_min'8804''8868'_600 v3
du_min'8804''8868'_600 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> [AgdaAny] -> AgdaAny
du_min'8804''8868'_600 v0
  = coe
      du_f'91'argmin'93''8804'f'91''8868''93'_196 (coe v0)
      (coe (\ v1 -> v1))
-- Data.List.Extrema.min≤xs
d_min'8804'xs_608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_min'8804'xs_608 ~v0 ~v1 ~v2 v3 = du_min'8804'xs_608 v3
du_min'8804'xs_608 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_min'8804'xs_608 v0
  = coe
      du_f'91'argmin'93''8804'f'91'xs'93'_208 (coe v0) (coe (\ v1 -> v1))
-- Data.List.Extrema.min≈v⁺
d_min'8776'v'8314'_618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
d_min'8776'v'8314'_618 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_min'8776'v'8314'_618 v3 v4 v5 v6
du_min'8776'v'8314'_618 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
du_min'8776'v'8314'_618 v0 v1 v2 v3
  = coe
      du_f'91'argmin'93''8776'f'91'v'93''8314'_222 (coe v0)
      (coe (\ v4 -> v4)) (coe v1) (coe v2) (coe v3)
-- Data.List.Extrema.min[xs]≤min[ys]⁺
d_min'91'xs'93''8804'min'91'ys'93''8314'_634 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_min'91'xs'93''8804'min'91'ys'93''8314'_634 ~v0 ~v1 ~v2 v3
  = du_min'91'xs'93''8804'min'91'ys'93''8314'_634 v3
du_min'91'xs'93''8804'min'91'ys'93''8314'_634 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_min'91'xs'93''8804'min'91'ys'93''8314'_634 v0
  = coe
      du_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_248 (coe v0)
      (coe (\ v1 -> v1)) (coe (\ v1 -> v1))
-- Data.List.Extrema.min[xs]<min[ys]⁺
d_min'91'xs'93''60'min'91'ys'93''8314'_650 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_min'91'xs'93''60'min'91'ys'93''8314'_650 ~v0 ~v1 ~v2 v3
  = du_min'91'xs'93''60'min'91'ys'93''8314'_650 v3
du_min'91'xs'93''60'min'91'ys'93''8314'_650 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_min'91'xs'93''60'min'91'ys'93''8314'_650 v0
  = coe
      du_argmin'91'xs'93''60'argmin'91'ys'93''8314'_276 (coe v0)
      (coe (\ v1 -> v1)) (coe (\ v1 -> v1))
-- Data.List.Extrema.min-mono-⊆
d_min'45'mono'45''8838'_660 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny
d_min'45'mono'45''8838'_660 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9
  = du_min'45'mono'45''8838'_660 v3 v4 v5 v6 v7 v8 v9
du_min'45'mono'45''8838'_660 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny
du_min'45'mono'45''8838'_660 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_min'91'xs'93''8804'min'91'ys'93''8314'_634 v0 v1 v2 v3 v4
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v5))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_tabulate_264 v4
         (\ v7 v8 ->
            coe
              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
              (coe
                 MAlonzo.Code.Data.List.Relation.Unary.Any.du_map_76
                 (\ v9 v10 -> coe du_'46'extendedlambda0_666 (coe v0) (coe v7))
                 (coe v3) (coe v6 v7 v8))))
-- Data.List.Extrema..extendedlambda0
d_'46'extendedlambda0_666 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'46'extendedlambda0_666 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          v10 ~v11 ~v12 ~v13
  = du_'46'extendedlambda0_666 v3 v10
du_'46'extendedlambda0_666 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny
du_'46'extendedlambda0_666 v0 v1
  = let v2
          = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
    coe
      (let v3
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v2) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_98
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v3))
            (coe v1)))
-- Data.List.Extrema.max≤v⁺
d_max'8804'v'8314'_676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_max'8804'v'8314'_676 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_max'8804'v'8314'_676 v3 v5 v6
du_max'8804'v'8314'_676 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_max'8804'v'8314'_676 v0 v1 v2
  = coe
      du_f'91'argmax'93''8804'v'8314'_386 (coe v0) (coe (\ v3 -> v3))
      (coe v1) (coe v2)
-- Data.List.Extrema.max<v⁺
d_max'60'v'8314'_686 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_max'60'v'8314'_686 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_max'60'v'8314'_686 v3 v5 v6
du_max'60'v'8314'_686 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_max'60'v'8314'_686 v0 v1 v2
  = coe
      du_f'91'argmax'93''60'v'8314'_396 (coe v0) (coe (\ v3 -> v3))
      (coe v1) (coe v2)
-- Data.List.Extrema.v≤max⁺
d_v'8804'max'8314'_696 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_v'8804'max'8314'_696 ~v0 ~v1 ~v2 v3 v4
  = du_v'8804'max'8314'_696 v3 v4
du_v'8804'max'8314'_696 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_v'8804'max'8314'_696 v0 v1
  = coe
      du_v'8804'f'91'argmax'93''8314'_366 (coe v0) (coe (\ v2 -> v2))
      (coe v1)
-- Data.List.Extrema.v<max⁺
d_v'60'max'8314'_706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_v'60'max'8314'_706 ~v0 ~v1 ~v2 v3 v4
  = du_v'60'max'8314'_706 v3 v4
du_v'60'max'8314'_706 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_v'60'max'8314'_706 v0 v1
  = coe
      du_v'60'f'91'argmax'93''8314'_376 (coe v0) (coe (\ v2 -> v2))
      (coe v1)
-- Data.List.Extrema.⊥≤max
d_'8869''8804'max_712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> [AgdaAny] -> AgdaAny
d_'8869''8804'max_712 ~v0 ~v1 ~v2 v3 = du_'8869''8804'max_712 v3
du_'8869''8804'max_712 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> [AgdaAny] -> AgdaAny
du_'8869''8804'max_712 v0
  = coe
      du_f'91''8869''93''8804'f'91'argmax'93'_402 (coe v0)
      (coe (\ v1 -> v1))
-- Data.List.Extrema.xs≤max
d_xs'8804'max_720 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_xs'8804'max_720 ~v0 ~v1 ~v2 v3 = du_xs'8804'max_720 v3
du_xs'8804'max_720 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_xs'8804'max_720 v0
  = coe
      du_f'91'xs'93''8804'f'91'argmax'93'_414 (coe v0) (coe (\ v1 -> v1))
-- Data.List.Extrema.max≈v⁺
d_max'8776'v'8314'_730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
d_max'8776'v'8314'_730 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_max'8776'v'8314'_730 v3 v4 v5 v6
du_max'8776'v'8314'_730 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
du_max'8776'v'8314'_730 v0 v1 v2 v3
  = coe
      du_f'91'argmax'93''8776'f'91'v'93''8314'_428 (coe v0)
      (coe (\ v4 -> v4)) (coe v1) (coe v2) (coe v3)
-- Data.List.Extrema.max[xs]≤max[ys]⁺
d_max'91'xs'93''8804'max'91'ys'93''8314'_746 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_max'91'xs'93''8804'max'91'ys'93''8314'_746 ~v0 ~v1 ~v2 v3 v4
  = du_max'91'xs'93''8804'max'91'ys'93''8314'_746 v3 v4
du_max'91'xs'93''8804'max'91'ys'93''8314'_746 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_max'91'xs'93''8804'max'91'ys'93''8314'_746 v0 v1
  = coe
      du_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_454 (coe v0)
      (coe (\ v2 -> v2)) (coe (\ v2 -> v2)) (coe v1)
-- Data.List.Extrema.max[xs]<max[ys]⁺
d_max'91'xs'93''60'max'91'ys'93''8314'_762 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_max'91'xs'93''60'max'91'ys'93''8314'_762 ~v0 ~v1 ~v2 v3 v4
  = du_max'91'xs'93''60'max'91'ys'93''8314'_762 v3 v4
du_max'91'xs'93''60'max'91'ys'93''8314'_762 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_max'91'xs'93''60'max'91'ys'93''8314'_762 v0 v1
  = coe
      du_argmax'91'xs'93''60'argmax'91'ys'93''8314'_482 (coe v0)
      (coe (\ v2 -> v2)) (coe (\ v2 -> v2)) (coe v1)
-- Data.List.Extrema.max-mono-⊆
d_max'45'mono'45''8838'_772 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny
d_max'45'mono'45''8838'_772 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9
  = du_max'45'mono'45''8838'_772 v3 v4 v5 v6 v7 v8 v9
du_max'45'mono'45''8838'_772 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny
du_max'45'mono'45''8838'_772 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_max'91'xs'93''8804'max'91'ys'93''8314'_746 v0 v1 v2 v3 v4
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v5))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_tabulate_264 v3
         (\ v7 v8 ->
            coe
              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
              (coe
                 MAlonzo.Code.Data.List.Relation.Unary.Any.du_map_76
                 (\ v9 v10 -> coe du_'46'extendedlambda1_778 (coe v0) (coe v7))
                 (coe v4) (coe v6 v7 v8))))
-- Data.List.Extrema..extendedlambda1
d_'46'extendedlambda1_778 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'46'extendedlambda1_778 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          v10 ~v11 ~v12 ~v13
  = du_'46'extendedlambda1_778 v3 v10
du_'46'extendedlambda1_778 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  AgdaAny -> AgdaAny
du_'46'extendedlambda1_778 v0 v1
  = let v2
          = coe MAlonzo.Code.Relation.Binary.Bundles.du_poset_796 (coe v0) in
    coe
      (let v3
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344 (coe v2) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_98
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v3))
            (coe v1)))
