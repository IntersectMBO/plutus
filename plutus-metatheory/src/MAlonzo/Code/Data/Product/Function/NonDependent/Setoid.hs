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

module MAlonzo.Code.Data.Product.Function.NonDependent.Setoid where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Binary.Bundles

-- Data.Product.Function.NonDependent.Setoid.proj₁ₛ
d_proj'8321''8347'_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
d_proj'8321''8347'_38 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_proj'8321''8347'_38
du_proj'8321''8347'_38 :: MAlonzo.Code.Function.Bundles.T_Func_774
du_proj'8321''8347'_38
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_840
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)))
      (coe
         (\ v0 v1 v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
-- Data.Product.Function.NonDependent.Setoid.proj₂ₛ
d_proj'8322''8347'_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
d_proj'8322''8347'_40 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_proj'8322''8347'_40
du_proj'8322''8347'_40 :: MAlonzo.Code.Function.Bundles.T_Func_774
du_proj'8322''8347'_40
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_840
      (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)))
      (coe
         (\ v0 v1 v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
-- Data.Product.Function.NonDependent.Setoid.<_,_>ₛ
d_'60'_'44'_'62''8347'_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
d_'60'_'44'_'62''8347'_42 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
                          v10
  = du_'60'_'44'_'62''8347'_42 v9 v10
du_'60'_'44'_'62''8347'_42 ::
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
du_'60'_'44'_'62''8347'_42 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_840
      (coe
         MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112
         (coe MAlonzo.Code.Function.Bundles.d_to_780 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to_780 (coe v1)))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112
              (coe MAlonzo.Code.Function.Bundles.d_cong_782 v0 v2 v3)
              (coe MAlonzo.Code.Function.Bundles.d_cong_782 v1 v2 v3)))
-- Data.Product.Function.NonDependent.Setoid.swapₛ
d_swap'8347'_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
d_swap'8347'_52 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_swap'8347'_52
du_swap'8347'_52 :: MAlonzo.Code.Function.Bundles.T_Func_774
du_swap'8347'_52
  = coe
      du_'60'_'44'_'62''8347'_42 (coe du_proj'8322''8347'_40)
      (coe du_proj'8321''8347'_38)
-- Data.Product.Function.NonDependent.Setoid._×-function_
d__'215''45'function__54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
d__'215''45'function__54 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 v12 v13
  = du__'215''45'function__54 v12 v13
du__'215''45'function__54 ::
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
du__'215''45'function__54 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_840
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_780 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_780 (coe v1))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_cong_782 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_cong_782 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
-- Data.Product.Function.NonDependent.Setoid._×-equivalence_
d__'215''45'equivalence__64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d__'215''45'equivalence__64 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10 ~v11 v12 v13
  = du__'215''45'equivalence__64 v12 v13
du__'215''45'equivalence__64 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
du__'215''45'equivalence__64 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_1940
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_1868 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_1868 (coe v1))))
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_from_1870 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_from_1870 (coe v1))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_to'45'cong_1872 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_to'45'cong_1872 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_from'45'cong_1874 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_from'45'cong_1874 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
-- Data.Product.Function.NonDependent.Setoid._×-injection_
d__'215''45'injection__74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842
d__'215''45'injection__74 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 v12 v13
  = du__'215''45'injection__74 v12 v13
du__'215''45'injection__74 ::
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842
du__'215''45'injection__74 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_916
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_850 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_850 (coe v1))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_cong_852 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_cong_852 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_injective_854 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_injective_854 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
-- Data.Product.Function.NonDependent.Setoid._×-surjection_
d__'215''45'surjection__84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
d__'215''45'surjection__84 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12 v13
  = du__'215''45'surjection__84 v12 v13
du__'215''45'surjection__84 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
du__'215''45'surjection__84 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_1002
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_926 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_926 (coe v1))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_cong_928 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_cong_928 v1
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
                 MAlonzo.Code.Function.Bundles.d_surjective_930 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
              (coe
                 MAlonzo.Code.Function.Bundles.d_surjective_930 v1
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))))
-- Data.Product.Function.NonDependent.Setoid._×-bijection_
d__'215''45'bijection__102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004
d__'215''45'bijection__102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12 v13
  = du__'215''45'bijection__102 v12 v13
du__'215''45'bijection__102 ::
  MAlonzo.Code.Function.Bundles.T_Bijection_1004 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004
du__'215''45'bijection__102 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_1094
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_1012 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_1012 (coe v1))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_cong_1014 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_cong_1014 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            (\ v2 v3 ->
               coe
                 MAlonzo.Code.Data.Product.Base.du_map_128
                 (coe
                    MAlonzo.Code.Function.Bundles.du_injective_1018 (coe v0)
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
                 (coe
                    (\ v4 ->
                       coe
                         MAlonzo.Code.Function.Bundles.du_injective_1018 (coe v1)
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
                        (coe MAlonzo.Code.Function.Bundles.du_surjective_1020 v0 v3)
                        (coe MAlonzo.Code.Function.Bundles.du_surjective_1020 v1 v4)
                 _ -> MAlonzo.RTE.mazUnreachableError)))
-- Data.Product.Function.NonDependent.Setoid._×-leftInverse_
d__'215''45'leftInverse__128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
d__'215''45'leftInverse__128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 ~v10 ~v11 v12 v13
  = du__'215''45'leftInverse__128 v12 v13
du__'215''45'leftInverse__128 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
du__'215''45'leftInverse__128 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_2034
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_1954 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_1954 (coe v1))))
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_from_1956 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_from_1956 (coe v1))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_to'45'cong_1958 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_to'45'cong_1958 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_from'45'cong_1960 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_from'45'cong_1960 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Function.Bundles.d_inverse'737'_1962 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
              (coe
                 MAlonzo.Code.Function.Bundles.d_inverse'737'_1962 v1
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))))
-- Data.Product.Function.NonDependent.Setoid._×-rightInverse_
d__'215''45'rightInverse__140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
d__'215''45'rightInverse__140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10 ~v11 v12 v13
  = du__'215''45'rightInverse__140 v12 v13
du__'215''45'rightInverse__140 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
du__'215''45'rightInverse__140 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_2120
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_2048 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_2048 (coe v1))))
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_from_2050 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_from_2050 (coe v1))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_to'45'cong_2052 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_to'45'cong_2052 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_from'45'cong_2054 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_from'45'cong_2054 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Function.Bundles.d_inverse'691'_2056 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
              (coe
                 MAlonzo.Code.Function.Bundles.d_inverse'691'_2056 v1
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))))
-- Data.Product.Function.NonDependent.Setoid._×-inverse_
d__'215''45'inverse__152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
d__'215''45'inverse__152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 v12 v13
  = du__'215''45'inverse__152 v12 v13
du__'215''45'inverse__152 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du__'215''45'inverse__152 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_2220
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_2134 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_2134 (coe v1))))
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_from_2136 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_from_2136 (coe v1))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_to'45'cong_2138 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_to'45'cong_2138 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe
                 MAlonzo.Code.Function.Bundles.d_from'45'cong_2140 v0
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              (coe
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Function.Bundles.d_from'45'cong_2140 v1
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            (\ v2 v3 v4 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                 (coe
                    MAlonzo.Code.Function.Bundles.du_inverse'737'_2144 v0
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
                 (coe
                    MAlonzo.Code.Function.Bundles.du_inverse'737'_2144 v1
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))))
         (coe
            (\ v2 v3 v4 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                 (coe
                    MAlonzo.Code.Function.Bundles.du_inverse'691'_2146 v0
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
                 (coe
                    MAlonzo.Code.Function.Bundles.du_inverse'691'_2146 v1
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))))))
-- Data.Product.Function.NonDependent.Setoid._×-left-inverse_
d__'215''45'left'45'inverse__166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
d__'215''45'left'45'inverse__166 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 v11 v12 v13
  = coe du__'215''45'leftInverse__128 v12 v13
