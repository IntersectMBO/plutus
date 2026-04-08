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

module MAlonzo.Code.Data.List.Extrema where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Extrema.Core
import qualified MAlonzo.Code.Data.List.Membership.Propositional
import qualified MAlonzo.Code.Data.List.Membership.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Membership.Setoid.Properties
import qualified MAlonzo.Code.Data.List.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Data.List.Extrema._._<_
d__'60'__102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny -> ()
d__'60'__102 = erased
-- Data.List.Extrema.argmin
d_argmin_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
d_argmin_140 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 = du_argmin_140 v3 v6
du_argmin_140 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
du_argmin_140 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480'_198 v0 v1)
-- Data.List.Extrema.argmax
d_argmax_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
d_argmax_144 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 = du_argmax_144 v3 v6
du_argmax_144 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
du_argmax_144 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_200 v0 v1)
-- Data.List.Extrema.min
d_min_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> [AgdaAny] -> AgdaAny
d_min_148 ~v0 ~v1 ~v2 v3 = du_min_148 v3
du_min_148 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> [AgdaAny] -> AgdaAny
du_min_148 v0 = coe du_argmin_140 (coe v0) (coe (\ v1 -> v1))
-- Data.List.Extrema.max
d_max_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> [AgdaAny] -> AgdaAny
d_max_150 ~v0 ~v1 ~v2 v3 = du_max_150 v3
du_max_150 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> [AgdaAny] -> AgdaAny
du_max_150 v0 = coe du_argmax_144 (coe v0) (coe (\ v1 -> v1))
-- Data.List.Extrema._.f[argmin]≤v⁺
d_f'91'argmin'93''8804'v'8314'_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_f'91'argmin'93''8804'v'8314'_168 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_f'91'argmin'93''8804'v'8314'_168 v3 v6 v7
du_f'91'argmin'93''8804'v'8314'_168 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_f'91'argmin'93''8804'v'8314'_168 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'preserves'7506'_4432
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480'_198 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480''45'pres'7506''45''8804'v_216
         (coe v0) (coe v1) (coe v2))
-- Data.List.Extrema._.f[argmin]<v⁺
d_f'91'argmin'93''60'v'8314'_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_f'91'argmin'93''60'v'8314'_178 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_f'91'argmin'93''60'v'8314'_178 v3 v6 v7
du_f'91'argmin'93''60'v'8314'_178 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_f'91'argmin'93''60'v'8314'_178 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'preserves'7506'_4432
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480'_198 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480''45'pres'7506''45''60'v_228
         (coe v0) (coe v1) (coe v2))
-- Data.List.Extrema._.v≤f[argmin]⁺
d_v'8804'f'91'argmin'93''8314'_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_v'8804'f'91'argmin'93''8314'_188 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 ~v7 v8
                                   v9
  = du_v'8804'f'91'argmin'93''8314'_188 v3 v6 v8 v9
du_v'8804'f'91'argmin'93''8314'_188 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_v'8804'f'91'argmin'93''8314'_188 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'preserves'7495'_4392
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480'_198 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480''45'pres'7495''45'v'8804'_240
         (coe v0) (coe v1))
      (coe v2) (coe v3)
-- Data.List.Extrema._.v<f[argmin]⁺
d_v'60'f'91'argmin'93''8314'_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_v'60'f'91'argmin'93''8314'_198 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 ~v7 v8
                                 v9
  = du_v'60'f'91'argmin'93''8314'_198 v3 v6 v8 v9
du_v'60'f'91'argmin'93''8314'_198 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_v'60'f'91'argmin'93''8314'_198 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'preserves'7495'_4392
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480'_198 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480''45'pres'7495''45'v'60'_256
         (coe v0) (coe v1))
      (coe v2) (coe v3)
-- Data.List.Extrema._.f[argmin]≤f[⊤]
d_f'91'argmin'93''8804'f'91''8868''93'_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
d_f'91'argmin'93''8804'f'91''8868''93'_204 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                           v6 v7 v8
  = du_f'91'argmin'93''8804'f'91''8868''93'_204 v3 v6 v7 v8
du_f'91'argmin'93''8804'f'91''8868''93'_204 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
du_f'91'argmin'93''8804'f'91''8868''93'_204 v0 v1 v2 v3
  = coe
      du_f'91'argmin'93''8804'v'8314'_168 v0 v1 (coe v1 v2) v2 v3
      (coe
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_104
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                     (coe v0))))
            (coe v1 v2)))
-- Data.List.Extrema._.f[argmin]≤f[xs]
d_f'91'argmin'93''8804'f'91'xs'93'_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_f'91'argmin'93''8804'f'91'xs'93'_216 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
                                       v8
  = du_f'91'argmin'93''8804'f'91'xs'93'_216 v3 v6 v7 v8
du_f'91'argmin'93''8804'f'91'xs'93'_216 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_f'91'argmin'93''8804'f'91'xs'93'_216 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'forces'7495'_4370
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480'_198 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480''45'forces'7495''45'v'8804'_272
         (coe v0) (coe v1) (coe v1 (coe du_argmin_140 v0 v1 v2 v3)))
      (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_refl_104
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                  (coe v0))))
         (coe v1 (coe du_argmin_140 v0 v1 v2 v3)))
-- Data.List.Extrema._.f[argmin]≈f[v]⁺
d_f'91'argmin'93''8776'f'91'v'93''8314'_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
d_f'91'argmin'93''8776'f'91'v'93''8314'_230 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                            v6 v7 v8 v9 v10 v11 v12
  = du_f'91'argmin'93''8776'f'91'v'93''8314'_230
      v3 v6 v7 v8 v9 v10 v11 v12
du_f'91'argmin'93''8776'f'91'v'93''8314'_230 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
du_f'91'argmin'93''8776'f'91'v'93''8314'_230 v0 v1 v2 v3 v4 v5 v6
                                             v7
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008 (coe v0)))
      (coe v1 (coe du_argmin_140 v0 v1 v3 v4)) (coe v1 v2)
      (coe
         du_f'91'argmin'93''8804'v'8314'_168 v0 v1 (coe v1 v2) v3 v4
         (coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            (coe
               MAlonzo.Code.Data.List.Membership.Propositional.du_lose_50 v2 v4 v5
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_refl_104
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                           (coe v0))))
                  (coe v1 v2)))))
      (coe du_v'8804'f'91'argmin'93''8314'_188 v0 v1 v3 v4 v7 v6)
-- Data.List.Extrema.argmin[xs]≤argmin[ys]⁺
d_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
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
d_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_256 ~v0 ~v1 ~v2 v3
                                                   ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_256
      v3 v6 v7 v8 v9 v10 v11 v12 v13
du_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_256 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_256 v0 v1 v2 v3 v4
                                                    v5 v6 v7 v8
  = coe
      du_v'8804'f'91'argmin'93''8314'_188 v0 v2 v4 v6
      (coe
         du_f'91'argmin'93''8804'v'8314'_168 v0 v1 (coe v2 v4) v3 v5 v7)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
         (coe
            (\ v9 ->
               coe du_f'91'argmin'93''8804'v'8314'_168 v0 v1 (coe v2 v9) v3 v5))
         (coe v6) (coe v8))
-- Data.List.Extrema.argmin[xs]<argmin[ys]⁺
d_argmin'91'xs'93''60'argmin'91'ys'93''8314'_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
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
d_argmin'91'xs'93''60'argmin'91'ys'93''8314'_284 ~v0 ~v1 ~v2 v3 ~v4
                                                 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du_argmin'91'xs'93''60'argmin'91'ys'93''8314'_284
      v3 v6 v7 v8 v9 v10 v11 v12 v13
du_argmin'91'xs'93''60'argmin'91'ys'93''8314'_284 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_argmin'91'xs'93''60'argmin'91'ys'93''8314'_284 v0 v1 v2 v3 v4 v5
                                                  v6 v7 v8
  = coe
      du_v'60'f'91'argmin'93''8314'_198 v0 v2 v4 v6
      (coe du_f'91'argmin'93''60'v'8314'_178 v0 v1 (coe v2 v4) v3 v5 v7)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
         (coe
            (\ v9 ->
               coe du_f'91'argmin'93''60'v'8314'_178 v0 v1 (coe v2 v9) v3 v5))
         (coe v6) (coe v8))
-- Data.List.Extrema.argmin-sel
d_argmin'45'sel_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_argmin'45'sel_300 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_argmin'45'sel_300 v3 v6
du_argmin'45'sel_300 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_argmin'45'sel_300 v0 v1
  = coe
      MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_foldr'45'selective_732
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480'_198 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480''45'sel_204
         (coe v0) (coe v1))
-- Data.List.Extrema.argmin-all
d_argmin'45'all_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_argmin'45'all_312 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 ~v10 v11
                    v12
  = du_argmin'45'all_312 v3 v7 v8 v9 v11 v12
du_argmin'45'all_312 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_argmin'45'all_312 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Data.List.Membership.Setoid.Properties.du_foldr'45'selective_1970
              (coe
                 MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
              (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480'_198 v0 v1)
              (coe
                 MAlonzo.Code.Data.List.Extrema.Core.du_'8851''7480''45'sel_204
                 (coe v0) (coe v1))
              (coe v2) (coe v3) in
    coe
      (case coe v6 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> coe v4
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
           -> coe
                MAlonzo.Code.Data.List.Relation.Unary.All.du_lookup_436 v3 v5 v7
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.List.Extrema._.v≤f[argmax]⁺
d_v'8804'f'91'argmax'93''8314'_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_v'8804'f'91'argmax'93''8314'_374 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_v'8804'f'91'argmax'93''8314'_374 v3 v6 v7
du_v'8804'f'91'argmax'93''8314'_374 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_v'8804'f'91'argmax'93''8314'_374 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'preserves'7506'_4432
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_200 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480''45'pres'7506''45'v'8804'_300
         (coe v0) (coe v1) (coe v2))
-- Data.List.Extrema._.v<f[argmax]⁺
d_v'60'f'91'argmax'93''8314'_384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_v'60'f'91'argmax'93''8314'_384 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du_v'60'f'91'argmax'93''8314'_384 v3 v6 v7
du_v'60'f'91'argmax'93''8314'_384 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_v'60'f'91'argmax'93''8314'_384 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'preserves'7506'_4432
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_200 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480''45'pres'7506''45'v'60'_322
         (coe v0) (coe v1) (coe v2))
-- Data.List.Extrema._.f[argmax]≤v⁺
d_f'91'argmax'93''8804'v'8314'_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_f'91'argmax'93''8804'v'8314'_394 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 ~v7 v8
                                   v9
  = du_f'91'argmax'93''8804'v'8314'_394 v3 v6 v8 v9
du_f'91'argmax'93''8804'v'8314'_394 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_f'91'argmax'93''8804'v'8314'_394 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'preserves'7495'_4392
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_200 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480''45'pres'7495''45''8804'v_344
         (coe v0) (coe v1))
      (coe v2) (coe v3)
-- Data.List.Extrema._.f[argmax]<v⁺
d_f'91'argmax'93''60'v'8314'_404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_f'91'argmax'93''60'v'8314'_404 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 ~v7 v8
                                 v9
  = du_f'91'argmax'93''60'v'8314'_404 v3 v6 v8 v9
du_f'91'argmax'93''60'v'8314'_404 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_f'91'argmax'93''60'v'8314'_404 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'preserves'7495'_4392
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_200 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480''45'pres'7495''45''60'v_360
         (coe v0) (coe v1))
      (coe v2) (coe v3)
-- Data.List.Extrema._.f[⊥]≤f[argmax]
d_f'91''8869''93''8804'f'91'argmax'93'_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
d_f'91''8869''93''8804'f'91'argmax'93'_410 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                           v6 v7 v8
  = du_f'91''8869''93''8804'f'91'argmax'93'_410 v3 v6 v7 v8
du_f'91''8869''93''8804'f'91'argmax'93'_410 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
du_f'91''8869''93''8804'f'91'argmax'93'_410 v0 v1 v2 v3
  = coe
      du_v'8804'f'91'argmax'93''8314'_374 v0 v1 (coe v1 v2) v2 v3
      (coe
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_104
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                     (coe v0))))
            (coe v1 v2)))
-- Data.List.Extrema._.f[xs]≤f[argmax]
d_f'91'xs'93''8804'f'91'argmax'93'_422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_f'91'xs'93''8804'f'91'argmax'93'_422 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
                                       v8
  = du_f'91'xs'93''8804'f'91'argmax'93'_422 v3 v6 v7 v8
du_f'91'xs'93''8804'f'91'argmax'93'_422 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_f'91'xs'93''8804'f'91'argmax'93'_422 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Properties.du_foldr'45'forces'7495'_4370
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_200 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480''45'forces'7495''45''8804'v_376
         (coe v0) (coe v1) (coe v1 (coe du_argmax_144 v0 v1 v2 v3)))
      (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_refl_104
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                  (coe v0))))
         (coe
            v1
            (coe
               MAlonzo.Code.Data.List.Base.du_foldr_216
               (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_200 v0 v1)
               (coe v2) (coe v3))))
-- Data.List.Extrema._.f[argmax]≈f[v]⁺
d_f'91'argmax'93''8776'f'91'v'93''8314'_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
d_f'91'argmax'93''8776'f'91'v'93''8314'_436 ~v0 ~v1 ~v2 v3 ~v4 ~v5
                                            v6 v7 v8 v9 v10 v11 v12
  = du_f'91'argmax'93''8776'f'91'v'93''8314'_436
      v3 v6 v7 v8 v9 v10 v11 v12
du_f'91'argmax'93''8776'f'91'v'93''8314'_436 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
du_f'91'argmax'93''8776'f'91'v'93''8314'_436 v0 v1 v2 v3 v4 v5 v6
                                             v7
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008 (coe v0)))
      (coe v1 (coe du_argmax_144 v0 v1 v3 v4)) (coe v1 v2)
      (coe du_f'91'argmax'93''8804'v'8314'_394 v0 v1 v3 v4 v7 v6)
      (coe
         du_v'8804'f'91'argmax'93''8314'_374 v0 v1 (coe v1 v2) v3 v4
         (coe
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
            (coe
               MAlonzo.Code.Data.List.Membership.Propositional.du_lose_50 v2 v4 v5
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_refl_104
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
                           (coe v0))))
                  (coe v1 v2)))))
-- Data.List.Extrema.argmax[xs]≤argmax[ys]⁺
d_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
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
d_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_462 ~v0 ~v1 ~v2 v3
                                                   ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_462
      v3 v6 v7 v8 v9 v10 v11 v12 v13
du_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_462 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_462 v0 v1 v2 v3 v4
                                                    v5 v6 v7 v8
  = coe
      du_f'91'argmax'93''8804'v'8314'_394 v0 v1 v3 v5
      (coe
         du_v'8804'f'91'argmax'93''8314'_374 v0 v2 (coe v1 v3) v4 v6 v7)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
         (coe
            (\ v9 ->
               coe du_v'8804'f'91'argmax'93''8314'_374 v0 v2 (coe v1 v9) v4 v6))
         (coe v5) (coe v8))
-- Data.List.Extrema.argmax[xs]<argmax[ys]⁺
d_argmax'91'xs'93''60'argmax'91'ys'93''8314'_490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
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
d_argmax'91'xs'93''60'argmax'91'ys'93''8314'_490 ~v0 ~v1 ~v2 v3 ~v4
                                                 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du_argmax'91'xs'93''60'argmax'91'ys'93''8314'_490
      v3 v6 v7 v8 v9 v10 v11 v12 v13
du_argmax'91'xs'93''60'argmax'91'ys'93''8314'_490 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_argmax'91'xs'93''60'argmax'91'ys'93''8314'_490 v0 v1 v2 v3 v4 v5
                                                  v6 v7 v8
  = coe
      du_f'91'argmax'93''60'v'8314'_404 v0 v1 v3 v5
      (coe du_v'60'f'91'argmax'93''8314'_384 v0 v2 (coe v1 v3) v4 v6 v7)
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
         (coe
            (\ v9 ->
               coe du_v'60'f'91'argmax'93''8314'_384 v0 v2 (coe v1 v9) v4 v6))
         (coe v5) (coe v8))
-- Data.List.Extrema.argmax-sel
d_argmax'45'sel_506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_argmax'45'sel_506 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_argmax'45'sel_506 v3 v6
du_argmax'45'sel_506 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_argmax'45'sel_506 v0 v1
  = coe
      MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_foldr'45'selective_732
      (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_200 v0 v1)
      (coe
         MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480''45'sel_288
         (coe v0) (coe v1))
-- Data.List.Extrema.argmax-all
d_argmax'45'all_518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_argmax'45'all_518 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 ~v8 v9 v10 v11
                    v12
  = du_argmax'45'all_518 v3 v7 v9 v10 v11 v12
du_argmax'45'all_518 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_argmax'45'all_518 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Data.List.Membership.Setoid.Properties.du_foldr'45'selective_1970
              (coe
                 MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
              (coe MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480'_200 v0 v1)
              (coe
                 MAlonzo.Code.Data.List.Extrema.Core.du_'8852''7480''45'sel_288
                 (coe v0) (coe v1))
              (coe v2) (coe v3) in
    coe
      (case coe v6 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> coe v4
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
           -> coe
                MAlonzo.Code.Data.List.Relation.Unary.All.du_lookup_436 v3 v5 v7
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.List.Extrema.min≤v⁺
d_min'8804'v'8314'_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_min'8804'v'8314'_572 ~v0 ~v1 ~v2 v3 v4
  = du_min'8804'v'8314'_572 v3 v4
du_min'8804'v'8314'_572 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_min'8804'v'8314'_572 v0 v1
  = coe
      du_f'91'argmin'93''8804'v'8314'_168 (coe v0) (coe (\ v2 -> v2))
      (coe v1)
-- Data.List.Extrema.min<v⁺
d_min'60'v'8314'_582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_min'60'v'8314'_582 ~v0 ~v1 ~v2 v3 v4
  = du_min'60'v'8314'_582 v3 v4
du_min'60'v'8314'_582 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_min'60'v'8314'_582 v0 v1
  = coe
      du_f'91'argmin'93''60'v'8314'_178 (coe v0) (coe (\ v2 -> v2))
      (coe v1)
-- Data.List.Extrema.v≤min⁺
d_v'8804'min'8314'_592 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_v'8804'min'8314'_592 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_v'8804'min'8314'_592 v3 v5 v6
du_v'8804'min'8314'_592 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_v'8804'min'8314'_592 v0 v1 v2
  = coe
      du_v'8804'f'91'argmin'93''8314'_188 (coe v0) (coe (\ v3 -> v3))
      (coe v1) (coe v2)
-- Data.List.Extrema.v<min⁺
d_v'60'min'8314'_602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_v'60'min'8314'_602 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_v'60'min'8314'_602 v3 v5 v6
du_v'60'min'8314'_602 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_v'60'min'8314'_602 v0 v1 v2
  = coe
      du_v'60'f'91'argmin'93''8314'_198 (coe v0) (coe (\ v3 -> v3))
      (coe v1) (coe v2)
-- Data.List.Extrema.min≤⊤
d_min'8804''8868'_608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> [AgdaAny] -> AgdaAny
d_min'8804''8868'_608 ~v0 ~v1 ~v2 v3 = du_min'8804''8868'_608 v3
du_min'8804''8868'_608 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> [AgdaAny] -> AgdaAny
du_min'8804''8868'_608 v0
  = coe
      du_f'91'argmin'93''8804'f'91''8868''93'_204 (coe v0)
      (coe (\ v1 -> v1))
-- Data.List.Extrema.min≤xs
d_min'8804'xs_616 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_min'8804'xs_616 ~v0 ~v1 ~v2 v3 = du_min'8804'xs_616 v3
du_min'8804'xs_616 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_min'8804'xs_616 v0
  = coe
      du_f'91'argmin'93''8804'f'91'xs'93'_216 (coe v0) (coe (\ v1 -> v1))
-- Data.List.Extrema.min≈v⁺
d_min'8776'v'8314'_626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
d_min'8776'v'8314'_626 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_min'8776'v'8314'_626 v3 v4 v5 v6
du_min'8776'v'8314'_626 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
du_min'8776'v'8314'_626 v0 v1 v2 v3
  = coe
      du_f'91'argmin'93''8776'f'91'v'93''8314'_230 (coe v0)
      (coe (\ v4 -> v4)) (coe v1) (coe v2) (coe v3)
-- Data.List.Extrema.min[xs]≤min[ys]⁺
d_min'91'xs'93''8804'min'91'ys'93''8314'_642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_min'91'xs'93''8804'min'91'ys'93''8314'_642 ~v0 ~v1 ~v2 v3
  = du_min'91'xs'93''8804'min'91'ys'93''8314'_642 v3
du_min'91'xs'93''8804'min'91'ys'93''8314'_642 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_min'91'xs'93''8804'min'91'ys'93''8314'_642 v0
  = coe
      du_argmin'91'xs'93''8804'argmin'91'ys'93''8314'_256 (coe v0)
      (coe (\ v1 -> v1)) (coe (\ v1 -> v1))
-- Data.List.Extrema.min[xs]<min[ys]⁺
d_min'91'xs'93''60'min'91'ys'93''8314'_658 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_min'91'xs'93''60'min'91'ys'93''8314'_658 ~v0 ~v1 ~v2 v3
  = du_min'91'xs'93''60'min'91'ys'93''8314'_658 v3
du_min'91'xs'93''60'min'91'ys'93''8314'_658 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_min'91'xs'93''60'min'91'ys'93''8314'_658 v0
  = coe
      du_argmin'91'xs'93''60'argmin'91'ys'93''8314'_284 (coe v0)
      (coe (\ v1 -> v1)) (coe (\ v1 -> v1))
-- Data.List.Extrema.min-mono-⊆
d_min'45'mono'45''8838'_668 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny
d_min'45'mono'45''8838'_668 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9
  = du_min'45'mono'45''8838'_668 v3 v4 v5 v6 v7 v8 v9
du_min'45'mono'45''8838'_668 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny
du_min'45'mono'45''8838'_668 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_min'91'xs'93''8804'min'91'ys'93''8314'_642 v0 v1 v2 v3 v4
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v5))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_tabulate_266 v4
         (\ v7 v8 ->
            coe
              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
              (coe
                 MAlonzo.Code.Data.List.Relation.Unary.Any.du_map_76
                 (\ v9 v10 -> coe du_'46'extendedlambda0_674 (coe v0) (coe v7))
                 (coe v3) (coe v6 v7 v8))))
-- Data.List.Extrema..extendedlambda0
d_'46'extendedlambda0_674 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
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
d_'46'extendedlambda0_674 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          v10 ~v11 ~v12 ~v13
  = du_'46'extendedlambda0_674 v3 v10
du_'46'extendedlambda0_674 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny
du_'46'extendedlambda0_674 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_refl_104
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
               (coe v0))))
      (coe v1)
-- Data.List.Extrema.max≤v⁺
d_max'8804'v'8314'_684 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_max'8804'v'8314'_684 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_max'8804'v'8314'_684 v3 v5 v6
du_max'8804'v'8314'_684 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_max'8804'v'8314'_684 v0 v1 v2
  = coe
      du_f'91'argmax'93''8804'v'8314'_394 (coe v0) (coe (\ v3 -> v3))
      (coe v1) (coe v2)
-- Data.List.Extrema.max<v⁺
d_max'60'v'8314'_694 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_max'60'v'8314'_694 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_max'60'v'8314'_694 v3 v5 v6
du_max'60'v'8314'_694 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_max'60'v'8314'_694 v0 v1 v2
  = coe
      du_f'91'argmax'93''60'v'8314'_404 (coe v0) (coe (\ v3 -> v3))
      (coe v1) (coe v2)
-- Data.List.Extrema.v≤max⁺
d_v'8804'max'8314'_704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_v'8804'max'8314'_704 ~v0 ~v1 ~v2 v3 v4
  = du_v'8804'max'8314'_704 v3 v4
du_v'8804'max'8314'_704 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_v'8804'max'8314'_704 v0 v1
  = coe
      du_v'8804'f'91'argmax'93''8314'_374 (coe v0) (coe (\ v2 -> v2))
      (coe v1)
-- Data.List.Extrema.v<max⁺
d_v'60'max'8314'_714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_v'60'max'8314'_714 ~v0 ~v1 ~v2 v3 v4
  = du_v'60'max'8314'_714 v3 v4
du_v'60'max'8314'_714 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_v'60'max'8314'_714 v0 v1
  = coe
      du_v'60'f'91'argmax'93''8314'_384 (coe v0) (coe (\ v2 -> v2))
      (coe v1)
-- Data.List.Extrema.⊥≤max
d_'8869''8804'max_720 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> [AgdaAny] -> AgdaAny
d_'8869''8804'max_720 ~v0 ~v1 ~v2 v3 = du_'8869''8804'max_720 v3
du_'8869''8804'max_720 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> [AgdaAny] -> AgdaAny
du_'8869''8804'max_720 v0
  = coe
      du_f'91''8869''93''8804'f'91'argmax'93'_410 (coe v0)
      (coe (\ v1 -> v1))
-- Data.List.Extrema.xs≤max
d_xs'8804'max_728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_xs'8804'max_728 ~v0 ~v1 ~v2 v3 = du_xs'8804'max_728 v3
du_xs'8804'max_728 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_xs'8804'max_728 v0
  = coe
      du_f'91'xs'93''8804'f'91'argmax'93'_422 (coe v0) (coe (\ v1 -> v1))
-- Data.List.Extrema.max≈v⁺
d_max'8776'v'8314'_738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
d_max'8776'v'8314'_738 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_max'8776'v'8314'_738 v3 v4 v5 v6
du_max'8776'v'8314'_738 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny -> AgdaAny
du_max'8776'v'8314'_738 v0 v1 v2 v3
  = coe
      du_f'91'argmax'93''8776'f'91'v'93''8314'_436 (coe v0)
      (coe (\ v4 -> v4)) (coe v1) (coe v2) (coe v3)
-- Data.List.Extrema.max[xs]≤max[ys]⁺
d_max'91'xs'93''8804'max'91'ys'93''8314'_754 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_max'91'xs'93''8804'max'91'ys'93''8314'_754 ~v0 ~v1 ~v2 v3 v4
  = du_max'91'xs'93''8804'max'91'ys'93''8314'_754 v3 v4
du_max'91'xs'93''8804'max'91'ys'93''8314'_754 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_max'91'xs'93''8804'max'91'ys'93''8314'_754 v0 v1
  = coe
      du_argmax'91'xs'93''8804'argmax'91'ys'93''8314'_462 (coe v0)
      (coe (\ v2 -> v2)) (coe (\ v2 -> v2)) (coe v1)
-- Data.List.Extrema.max[xs]<max[ys]⁺
d_max'91'xs'93''60'max'91'ys'93''8314'_770 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_max'91'xs'93''60'max'91'ys'93''8314'_770 ~v0 ~v1 ~v2 v3 v4
  = du_max'91'xs'93''60'max'91'ys'93''8314'_770 v3 v4
du_max'91'xs'93''60'max'91'ys'93''8314'_770 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_max'91'xs'93''60'max'91'ys'93''8314'_770 v0 v1
  = coe
      du_argmax'91'xs'93''60'argmax'91'ys'93''8314'_490 (coe v0)
      (coe (\ v2 -> v2)) (coe (\ v2 -> v2)) (coe v1)
-- Data.List.Extrema.max-mono-⊆
d_max'45'mono'45''8838'_780 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny
d_max'45'mono'45''8838'_780 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9
  = du_max'45'mono'45''8838'_780 v3 v4 v5 v6 v7 v8 v9
du_max'45'mono'45''8838'_780 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  AgdaAny
du_max'45'mono'45''8838'_780 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_max'91'xs'93''8804'max'91'ys'93''8314'_754 v0 v1 v2 v3 v4
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v5))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.du_tabulate_266 v3
         (\ v7 v8 ->
            coe
              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
              (coe
                 MAlonzo.Code.Data.List.Relation.Unary.Any.du_map_76
                 (\ v9 v10 -> coe du_'46'extendedlambda1_786 (coe v0) (coe v7))
                 (coe v4) (coe v6 v7 v8))))
-- Data.List.Extrema..extendedlambda1
d_'46'extendedlambda1_786 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
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
d_'46'extendedlambda1_786 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          v10 ~v11 ~v12 ~v13
  = du_'46'extendedlambda1_786 v3 v10
du_'46'extendedlambda1_786 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  AgdaAny -> AgdaAny
du_'46'extendedlambda1_786 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_refl_104
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008
               (coe v0))))
      (coe v1)
