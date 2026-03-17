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

module MAlonzo.Code.Class.Bifunctor where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base

-- Class.Bifunctor.BifunctorI
d_BifunctorI_30 a0 a1 a2 = ()
newtype T_BifunctorI_30
  = C_BifunctorI'46'constructor_583 (() ->
                                     () ->
                                     (AgdaAny -> ()) ->
                                     (AgdaAny -> ()) ->
                                     (AgdaAny -> AgdaAny) ->
                                     (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny)
-- Class.Bifunctor.BifunctorI.bimap′
d_bimap'8242'_44 ::
  T_BifunctorI_30 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_bimap'8242'_44 v0
  = case coe v0 of
      C_BifunctorI'46'constructor_583 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Bifunctor.BifunctorI.map₁′
d_map'8321''8242'_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> (AgdaAny -> ()) -> ()) ->
  T_BifunctorI_30 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'8321''8242'_46 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7
  = du_map'8321''8242'_46 v3 v7
du_map'8321''8242'_46 ::
  T_BifunctorI_30 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'8321''8242'_46 v0 v1
  = coe
      d_bimap'8242'_44 v0 erased erased erased erased v1 (\ v2 v3 -> v3)
-- Class.Bifunctor.BifunctorI._<$>₁′_
d__'60''36''62''8321''8242'__50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> (AgdaAny -> ()) -> ()) ->
  T_BifunctorI_30 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62''8321''8242'__50 ~v0 ~v1 ~v2 v3
  = du__'60''36''62''8321''8242'__50 v3
du__'60''36''62''8321''8242'__50 ::
  T_BifunctorI_30 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62''8321''8242'__50 v0 v1 v2 v3 v4
  = coe du_map'8321''8242'_46 (coe v0) v4
-- Class.Bifunctor.BifunctorI.map₂′
d_map'8322''8242'_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> (AgdaAny -> ()) -> ()) ->
  T_BifunctorI_30 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'8322''8242'_54 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7
  = du_map'8322''8242'_54 v3 v7
du_map'8322''8242'_54 ::
  T_BifunctorI_30 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'8322''8242'_54 v0 v1
  = coe
      d_bimap'8242'_44 v0 erased erased erased erased (\ v2 -> v2) v1
-- Class.Bifunctor.BifunctorI._<$>₂′_
d__'60''36''62''8322''8242'__58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> (AgdaAny -> ()) -> ()) ->
  T_BifunctorI_30 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62''8322''8242'__58 ~v0 ~v1 ~v2 v3
  = du__'60''36''62''8322''8242'__58 v3
du__'60''36''62''8322''8242'__58 ::
  T_BifunctorI_30 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62''8322''8242'__58 v0 v1 v2 v3 v4
  = coe du_map'8322''8242'_54 (coe v0) v4
-- Class.Bifunctor._._<$>₁′_
d__'60''36''62''8321''8242'__62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> (AgdaAny -> ()) -> ()) ->
  T_BifunctorI_30 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62''8321''8242'__62 ~v0 ~v1 ~v2 v3
  = du__'60''36''62''8321''8242'__62 v3
du__'60''36''62''8321''8242'__62 ::
  T_BifunctorI_30 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62''8321''8242'__62 v0
  = coe du__'60''36''62''8321''8242'__50 (coe v0)
-- Class.Bifunctor._._<$>₂′_
d__'60''36''62''8322''8242'__64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> (AgdaAny -> ()) -> ()) ->
  T_BifunctorI_30 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62''8322''8242'__64 ~v0 ~v1 ~v2 v3
  = du__'60''36''62''8322''8242'__64 v3
du__'60''36''62''8322''8242'__64 ::
  T_BifunctorI_30 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62''8322''8242'__64 v0
  = coe du__'60''36''62''8322''8242'__58 (coe v0)
-- Class.Bifunctor._.bimap′
d_bimap'8242'_66 ::
  T_BifunctorI_30 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_bimap'8242'_66 v0 = coe d_bimap'8242'_44 (coe v0)
-- Class.Bifunctor._.map₁′
d_map'8321''8242'_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> (AgdaAny -> ()) -> ()) ->
  T_BifunctorI_30 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'8321''8242'_68 ~v0 ~v1 ~v2 v3 = du_map'8321''8242'_68 v3
du_map'8321''8242'_68 ::
  T_BifunctorI_30 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'8321''8242'_68 v0 v1 v2 v3 v4
  = coe du_map'8321''8242'_46 (coe v0) v4
-- Class.Bifunctor._.map₂′
d_map'8322''8242'_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> (AgdaAny -> ()) -> ()) ->
  T_BifunctorI_30 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'8322''8242'_70 ~v0 ~v1 ~v2 v3 = du_map'8322''8242'_70 v3
du_map'8322''8242'_70 ::
  T_BifunctorI_30 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'8322''8242'_70 v0 v1 v2 v3 v4
  = coe du_map'8322''8242'_54 (coe v0) v4
-- Class.Bifunctor.Bifunctor-Σ
d_Bifunctor'45'Σ_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_BifunctorI_30
d_Bifunctor'45'Σ_72 ~v0 ~v1 = du_Bifunctor'45'Σ_72
du_Bifunctor'45'Σ_72 :: T_BifunctorI_30
du_Bifunctor'45'Σ_72
  = coe
      C_BifunctorI'46'constructor_583
      (coe
         (\ v0 v1 v2 v3 -> coe MAlonzo.Code.Data.Product.Base.du_map_128))
-- Class.Bifunctor.Bifunctor
d_Bifunctor_80 a0 a1 a2 = ()
newtype T_Bifunctor_80
  = C_Bifunctor'46'constructor_3949 (() ->
                                     () ->
                                     () ->
                                     () ->
                                     (AgdaAny -> AgdaAny) ->
                                     (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny)
-- Class.Bifunctor.Bifunctor.bimap
d_bimap_102 ::
  T_Bifunctor_80 ->
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_bimap_102 v0
  = case coe v0 of
      C_Bifunctor'46'constructor_3949 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Bifunctor.Bifunctor.map₁
d_map'8321'_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> () -> ()) ->
  T_Bifunctor_80 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'8321'_110 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7
  = du_map'8321'_110 v3 v7
du_map'8321'_110 ::
  T_Bifunctor_80 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'8321'_110 v0 v1
  = coe d_bimap_102 v0 erased erased erased erased v1 (\ v2 -> v2)
-- Class.Bifunctor.Bifunctor._<$>₁_
d__'60''36''62''8321'__114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> () -> ()) ->
  T_Bifunctor_80 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62''8321'__114 ~v0 ~v1 ~v2 v3
  = du__'60''36''62''8321'__114 v3
du__'60''36''62''8321'__114 ::
  T_Bifunctor_80 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62''8321'__114 v0 v1 v2 v3 v4
  = coe du_map'8321'_110 (coe v0) v4
-- Class.Bifunctor.Bifunctor.map₂
d_map'8322'_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> () -> ()) ->
  T_Bifunctor_80 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'8322'_122 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7
  = du_map'8322'_122 v3 v7
du_map'8322'_122 ::
  T_Bifunctor_80 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'8322'_122 v0 v1
  = coe d_bimap_102 v0 erased erased erased erased (\ v2 -> v2) v1
-- Class.Bifunctor.Bifunctor._<$>₂_
d__'60''36''62''8322'__126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> () -> ()) ->
  T_Bifunctor_80 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62''8322'__126 ~v0 ~v1 ~v2 v3
  = du__'60''36''62''8322'__126 v3
du__'60''36''62''8322'__126 ::
  T_Bifunctor_80 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62''8322'__126 v0 v1 v2 v3 v4
  = coe du_map'8322'_122 (coe v0) v4
-- Class.Bifunctor._._<$>₁_
d__'60''36''62''8321'__130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> () -> ()) ->
  T_Bifunctor_80 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62''8321'__130 ~v0 ~v1 ~v2 v3
  = du__'60''36''62''8321'__130 v3
du__'60''36''62''8321'__130 ::
  T_Bifunctor_80 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62''8321'__130 v0
  = coe du__'60''36''62''8321'__114 (coe v0)
-- Class.Bifunctor._._<$>₂_
d__'60''36''62''8322'__132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> () -> ()) ->
  T_Bifunctor_80 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62''8322'__132 ~v0 ~v1 ~v2 v3
  = du__'60''36''62''8322'__132 v3
du__'60''36''62''8322'__132 ::
  T_Bifunctor_80 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62''8322'__132 v0
  = coe du__'60''36''62''8322'__126 (coe v0)
-- Class.Bifunctor._.bimap
d_bimap_134 ::
  T_Bifunctor_80 ->
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_bimap_134 v0 = coe d_bimap_102 (coe v0)
-- Class.Bifunctor._.map₁
d_map'8321'_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> () -> ()) ->
  T_Bifunctor_80 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'8321'_136 ~v0 ~v1 ~v2 v3 = du_map'8321'_136 v3
du_map'8321'_136 ::
  T_Bifunctor_80 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'8321'_136 v0 v1 v2 v3 v4 = coe du_map'8321'_110 (coe v0) v4
-- Class.Bifunctor._.map₂
d_map'8322'_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> () -> ()) ->
  T_Bifunctor_80 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'8322'_138 ~v0 ~v1 ~v2 v3 = du_map'8322'_138 v3
du_map'8322'_138 ::
  T_Bifunctor_80 ->
  () -> () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'8322'_138 v0 v1 v2 v3 v4 = coe du_map'8322'_122 (coe v0) v4
-- Class.Bifunctor.map₁₂
d_map'8321''8322'_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> () -> ()) ->
  () ->
  () -> T_Bifunctor_80 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'8321''8322'_146 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_map'8321''8322'_146 v4 v5
du_map'8321''8322'_146 ::
  T_Bifunctor_80 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'8321''8322'_146 v0 v1
  = coe d_bimap_102 v0 erased erased erased erased v1 v1
-- Class.Bifunctor._<$>₁₂_
d__'60''36''62''8321''8322'__150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> () -> ()) ->
  () ->
  () -> T_Bifunctor_80 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62''8321''8322'__150 v0 v1 v2 v3 v4 v5
  = coe du_map'8321''8322'_146 v4 v5
-- Class.Bifunctor.Bifunctor-×
d_Bifunctor'45''215'_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_Bifunctor_80
d_Bifunctor'45''215'_152 ~v0 ~v1 = du_Bifunctor'45''215'_152
du_Bifunctor'45''215'_152 :: T_Bifunctor_80
du_Bifunctor'45''215'_152
  = coe
      C_Bifunctor'46'constructor_3949
      (coe
         (\ v0 v1 v2 v3 v4 v5 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128 (coe v4)
              (coe (\ v6 -> v5))))
-- Class.Bifunctor.Bifunctor-⊎
d_Bifunctor'45''8846'_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_Bifunctor_80
d_Bifunctor'45''8846'_158 ~v0 ~v1 = du_Bifunctor'45''8846'_158
du_Bifunctor'45''8846'_158 :: T_Bifunctor_80
du_Bifunctor'45''8846'_158
  = coe
      C_Bifunctor'46'constructor_3949
      (coe (\ v0 v1 v2 v3 -> coe MAlonzo.Code.Data.Sum.Base.du_map_84))
