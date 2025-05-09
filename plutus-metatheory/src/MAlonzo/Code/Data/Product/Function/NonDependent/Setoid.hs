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

module MAlonzo.Code.Data.Product.Function.NonDependent.Setoid where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Product.Function.NonDependent.Setoid.proj₁ₛ
d_proj'8321''8347'_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d_proj'8321''8347'_38 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_proj'8321''8347'_38
du_proj'8321''8347'_38 :: MAlonzo.Code.Function.Bundles.T_Func_714
du_proj'8321''8347'_38
  = coe
      MAlonzo.Code.Function.Bundles.C_Func'46'constructor_6307
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
      (coe
         (\ v0 v1 v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
-- Data.Product.Function.NonDependent.Setoid.proj₂ₛ
d_proj'8322''8347'_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d_proj'8322''8347'_40 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_proj'8322''8347'_40
du_proj'8322''8347'_40 :: MAlonzo.Code.Function.Bundles.T_Func_714
du_proj'8322''8347'_40
  = coe
      MAlonzo.Code.Function.Bundles.C_Func'46'constructor_6307
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
      (coe
         (\ v0 v1 v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
-- Data.Product.Function.NonDependent.Setoid.<_,_>ₛ
d_'60'_'44'_'62''8347'_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d_'60'_'44'_'62''8347'_42 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
                          v10
  = du_'60'_'44'_'62''8347'_42 v9 v10
du_'60'_'44'_'62''8347'_42 ::
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
du_'60'_'44'_'62''8347'_42 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Func'46'constructor_6307
      (coe
         MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112
         (coe MAlonzo.Code.Function.Bundles.d_to_720 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to_720 (coe v1)))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112
              (coe MAlonzo.Code.Function.Bundles.d_cong_722 v0 v2 v3)
              (coe MAlonzo.Code.Function.Bundles.d_cong_722 v1 v2 v3)))
-- Data.Product.Function.NonDependent.Setoid.swapₛ
d_swap'8347'_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d_swap'8347'_52 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_swap'8347'_52
du_swap'8347'_52 :: MAlonzo.Code.Function.Bundles.T_Func_714
du_swap'8347'_52
  = coe
      du_'60'_'44'_'62''8347'_42 (coe du_proj'8322''8347'_40)
      (coe du_proj'8321''8347'_38)
-- Data.Product.Function.NonDependent.Setoid._×-function_
d__'215''45'function__54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d__'215''45'function__54 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 v12 v13
  = du__'215''45'function__54 v12 v13
du__'215''45'function__54 ::
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
du__'215''45'function__54 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Func'46'constructor_6307
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_720 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_720 (coe v1))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_cong_722 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_cong_722 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
-- Data.Product.Function.NonDependent.Setoid._×-equivalence_
d__'215''45'equivalence__64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d__'215''45'equivalence__64 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10 ~v11 v12 v13
  = du__'215''45'equivalence__64 v12 v13
du__'215''45'equivalence__64 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du__'215''45'equivalence__64 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Equivalence'46'constructor_25797
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_1724 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_1724 (coe v1))))
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_from_1726 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_from_1726 (coe v1))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_to'45'cong_1728 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_to'45'cong_1728 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_from'45'cong_1730 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_from'45'cong_1730 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
-- Data.Product.Function.NonDependent.Setoid._×-injection_
d__'215''45'injection__74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776
d__'215''45'injection__74 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 v12 v13
  = du__'215''45'injection__74 v12 v13
du__'215''45'injection__74 ::
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776
du__'215''45'injection__74 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Injection'46'constructor_8675
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_784 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_784 (coe v1))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_cong_786 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_cong_786 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_injective_788 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_injective_788 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
-- Data.Product.Function.NonDependent.Setoid._×-surjection_
d__'215''45'surjection__84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
d__'215''45'surjection__84 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12 v13
  = du__'215''45'surjection__84 v12 v13
du__'215''45'surjection__84 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
du__'215''45'surjection__84 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Surjection'46'constructor_11197
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_854 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_854 (coe v1))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_cong_856 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_cong_856 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_zip_198
              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32)
              (coe
                 (\ v3 v4 v5 v6 v7 v8 ->
                    coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe
                         v5 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v7))
                         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v8)))
                      (coe
                         v6 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v7))
                         (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v8)))))
              (coe
                 MAlonzo.Code.Function.Bundles.d_surjective_858 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
              (coe
                 MAlonzo.Code.Function.Bundles.d_surjective_858 v1
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))))
-- Data.Product.Function.NonDependent.Setoid._×-bijection_
d__'215''45'bijection__102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
d__'215''45'bijection__102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12 v13
  = du__'215''45'bijection__102 v12 v13
du__'215''45'bijection__102 ::
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
du__'215''45'bijection__102 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Bijection'46'constructor_15277
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_934 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_934 (coe v1))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_cong_936 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_cong_936 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            (\ v2 v3 ->
               coe
                 MAlonzo.Code.Data.Product.Base.du_map_128
                 (coe
                    MAlonzo.Code.Function.Bundles.du_injective_940 (coe v0)
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
                 (coe
                    (\ v4 ->
                       coe
                         MAlonzo.Code.Function.Bundles.du_injective_940 (coe v1)
                         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
         (coe
            (\ v2 ->
               case coe v2 of
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                   -> coe
                        MAlonzo.Code.Data.Product.Base.du_zip_198
                        (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32)
                        (coe
                           (\ v5 v6 v7 v8 v9 v10 ->
                              case coe v10 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                  -> coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe
                                          v7 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v9))
                                          v11)
                                       (coe
                                          v8 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v9))
                                          v12)
                                _ -> MAlonzo.RTE.mazUnreachableError))
                        (coe MAlonzo.Code.Function.Bundles.du_surjective_942 v0 v3)
                        (coe MAlonzo.Code.Function.Bundles.du_surjective_942 v1 v4)
                 _ -> MAlonzo.RTE.mazUnreachableError)))
-- Data.Product.Function.NonDependent.Setoid._×-leftInverse_
d__'215''45'leftInverse__128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
d__'215''45'leftInverse__128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 ~v10 ~v11 v12 v13
  = du__'215''45'leftInverse__128 v12 v13
du__'215''45'leftInverse__128 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
du__'215''45'leftInverse__128 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_LeftInverse'46'constructor_29775
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_1804 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_1804 (coe v1))))
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_from_1806 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_from_1806 (coe v1))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_to'45'cong_1808 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_to'45'cong_1808 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_from'45'cong_1810 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_from'45'cong_1810 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Function.Bundles.d_inverse'737'_1812 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
              (coe
                 MAlonzo.Code.Function.Bundles.d_inverse'737'_1812 v1
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))))
-- Data.Product.Function.NonDependent.Setoid._×-rightInverse_
d__'215''45'rightInverse__140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
d__'215''45'rightInverse__140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10 ~v11 v12 v13
  = du__'215''45'rightInverse__140 v12 v13
du__'215''45'rightInverse__140 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
du__'215''45'rightInverse__140 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_RightInverse'46'constructor_34573
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_1892 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_1892 (coe v1))))
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_from_1894 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_from_1894 (coe v1))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_to'45'cong_1896 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_to'45'cong_1896 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_from'45'cong_1898 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_from'45'cong_1898 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Function.Bundles.d_inverse'691'_1900 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
              (coe
                 MAlonzo.Code.Function.Bundles.d_inverse'691'_1900 v1
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))))
-- Data.Product.Function.NonDependent.Setoid._×-inverse_
d__'215''45'inverse__152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d__'215''45'inverse__152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 v12 v13
  = du__'215''45'inverse__152 v12 v13
du__'215''45'inverse__152 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du__'215''45'inverse__152 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Inverse'46'constructor_38621
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_1972 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_1972 (coe v1))))
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_from_1974 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_from_1974 (coe v1))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_to'45'cong_1976 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_to'45'cong_1976 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_from'45'cong_1978 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_from'45'cong_1978 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            (\ v2 v3 v4 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                 (coe
                    MAlonzo.Code.Function.Bundles.du_inverse'737'_1982 v0
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
                 (coe
                    MAlonzo.Code.Function.Bundles.du_inverse'737'_1982 v1
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))))
         (coe
            (\ v2 v3 v4 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                 (coe
                    MAlonzo.Code.Function.Bundles.du_inverse'691'_1984 v0
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
                 (coe
                    MAlonzo.Code.Function.Bundles.du_inverse'691'_1984 v1
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))))))
-- Data.Product.Function.NonDependent.Setoid._×-left-inverse_
d__'215''45'left'45'inverse__166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
d__'215''45'left'45'inverse__166 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 v11 v12 v13
  = coe du__'215''45'leftInverse__128 v12 v13
