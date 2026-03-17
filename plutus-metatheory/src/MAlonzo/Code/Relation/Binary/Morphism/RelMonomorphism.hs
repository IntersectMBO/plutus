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

module MAlonzo.Code.Relation.Binary.Morphism.RelMonomorphism where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Morphism.Structures
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Relation.Binary.Morphism.RelMonomorphism.refl
d_refl_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_refl_36 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11
  = du_refl_36 v8 v9 v10 v11
du_refl_36 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_refl_36 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_injective_78 v1
      v3 v3 (coe v2 (coe v0 v3))
-- Relation.Binary.Morphism.RelMonomorphism.sym
d_sym_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_40 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 v12 v13
  = du_sym_40 v8 v9 v10 v11 v12 v13
du_sym_40 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_40 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_injective_78 v1
      v4 v3
      (coe
         v2 (coe v0 v3) (coe v0 v4)
         (coe
            MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
            (MAlonzo.Code.Relation.Binary.Morphism.Structures.d_isHomomorphism_76
               (coe v1))
            v3 v4 v5))
-- Relation.Binary.Morphism.RelMonomorphism.trans
d_trans_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_46 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 v12 v13
           v14 v15
  = du_trans_46 v8 v9 v10 v11 v12 v13 v14 v15
du_trans_46 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_46 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Relation.Binary.Morphism.Structures.d_injective_78 v1
      v3 v5
      (coe
         v2 (coe v0 v3) (coe v0 v4) (coe v0 v5)
         (coe
            MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
            (MAlonzo.Code.Relation.Binary.Morphism.Structures.d_isHomomorphism_76
               (coe v1))
            v3 v4 v6)
         (coe
            MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
            (MAlonzo.Code.Relation.Binary.Morphism.Structures.d_isHomomorphism_76
               (coe v1))
            v4 v5 v7))
-- Relation.Binary.Morphism.RelMonomorphism.total
d_total_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_54 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 v12
  = du_total_54 v8 v9 v10 v11 v12
du_total_54 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_total_54 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Sum.Base.du_map_84
      (coe
         MAlonzo.Code.Relation.Binary.Morphism.Structures.d_injective_78 v1
         v3 v4)
      (coe
         MAlonzo.Code.Relation.Binary.Morphism.Structures.d_injective_78 v1
         v4 v3)
      (coe v2 (coe v0 v3) (coe v0 v4))
-- Relation.Binary.Morphism.RelMonomorphism.asym
d_asym_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_62 = erased
-- Relation.Binary.Morphism.RelMonomorphism.dec
d_dec_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_dec_70 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 v12
  = du_dec_70 v8 v9 v10 v11 v12
du_dec_70 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_dec_70 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      (coe
         MAlonzo.Code.Relation.Binary.Morphism.Structures.d_injective_78 v1
         v3 v4)
      (coe
         MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
         (MAlonzo.Code.Relation.Binary.Morphism.Structures.d_isHomomorphism_76
            (coe v1))
         v3 v4)
      (coe v2 (coe v0 v3) (coe v0 v4))
-- Relation.Binary.Morphism.RelMonomorphism.isEquivalence
d_isEquivalence_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_78 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_isEquivalence_78 v8 v9 v10
du_isEquivalence_78 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_78 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
      (coe
         du_refl_36 (coe v0) (coe v1)
         (coe MAlonzo.Code.Relation.Binary.Structures.d_refl_34 (coe v2)))
      (coe
         du_sym_40 (coe v0) (coe v1)
         (coe MAlonzo.Code.Relation.Binary.Structures.d_sym_36 (coe v2)))
      (coe
         du_trans_46 (coe v0) (coe v1)
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_38 (coe v2)))
-- Relation.Binary.Morphism.RelMonomorphism.isDecEquivalence
d_isDecEquivalence_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_isDecEquivalence_98 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_isDecEquivalence_98 v8 v9 v10
du_isDecEquivalence_98 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Morphism.Structures.T_IsRelMonomorphism_64 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
du_isDecEquivalence_98 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecEquivalence'46'constructor_3083
      (coe
         du_isEquivalence_78 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
            (coe v2)))
      (coe
         du_dec_70 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__52 (coe v2)))
