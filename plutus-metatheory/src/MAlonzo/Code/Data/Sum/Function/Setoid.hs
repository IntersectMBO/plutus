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

module MAlonzo.Code.Data.Sum.Function.Setoid where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Sum.Function.Setoid.inj₁ₛ
d_inj'8321''8347'_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d_inj'8321''8347'_52 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_inj'8321''8347'_52
du_inj'8321''8347'_52 :: MAlonzo.Code.Function.Bundles.T_Func_714
du_inj'8321''8347'_52
  = coe
      MAlonzo.Code.Function.Bundles.C_Func'46'constructor_6307
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
      (\ v0 v1 v2 ->
         coe
           MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8321'_88 v2)
-- Data.Sum.Function.Setoid.inj₂ₛ
d_inj'8322''8347'_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d_inj'8322''8347'_54 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_inj'8322''8347'_54
du_inj'8322''8347'_54 :: MAlonzo.Code.Function.Bundles.T_Func_714
du_inj'8322''8347'_54
  = coe
      MAlonzo.Code.Function.Bundles.C_Func'46'constructor_6307
      (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
      (\ v0 v1 v2 ->
         coe
           MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8322'_94 v2)
-- Data.Sum.Function.Setoid.[_,_]ₛ
d_'91'_'44'_'93''8347'_56 ::
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
d_'91'_'44'_'93''8347'_56 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
                          v10
  = du_'91'_'44'_'93''8347'_56 v9 v10
du_'91'_'44'_'93''8347'_56 ::
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
du_'91'_'44'_'93''8347'_56 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Func'46'constructor_6307
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
         (coe MAlonzo.Code.Function.Bundles.d_to_720 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to_720 (coe v1)))
      (coe du_'46'extendedlambda0_66 (coe v0) (coe v1))
-- Data.Sum.Function.Setoid._..extendedlambda0
d_'46'extendedlambda0_66 ::
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
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70 ->
  AgdaAny
d_'46'extendedlambda0_66 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
                         v11 v12 v13
  = du_'46'extendedlambda0_66 v9 v10 v11 v12 v13
du_'46'extendedlambda0_66 ::
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70 ->
  AgdaAny
du_'46'extendedlambda0_66 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8321'_88 v7
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe MAlonzo.Code.Function.Bundles.d_cong_722 v0 v8 v9 v7
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8322'_94 v7
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe MAlonzo.Code.Function.Bundles.d_cong_722 v1 v8 v9 v7
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Function.Setoid.swapₛ
d_swap'8347'_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d_swap'8347'_72 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_swap'8347'_72
du_swap'8347'_72 :: MAlonzo.Code.Function.Bundles.T_Func_714
du_swap'8347'_72
  = coe
      du_'91'_'44'_'93''8347'_56 (coe du_inj'8322''8347'_54)
      (coe du_inj'8321''8347'_52)
-- Data.Sum.Function.Setoid.⊎-injective
d_'8846''45'injective_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70
d_'8846''45'injective_78 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 v19 v20 v21 v22
  = du_'8846''45'injective_78 v18 v19 v20 v21 v22
du_'8846''45'injective_78 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70
du_'8846''45'injective_78 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8321'_88 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8321'_88
                           (coe v0 v5 v6 v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8322'_94 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8322'_94
                           (coe v1 v5 v6 v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Function.Setoid.⊎-strictlySurjective
d_'8846''45'strictlySurjective_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8846''45'strictlySurjective_104 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 v14 v15
  = du_'8846''45'strictlySurjective_104 v14 v15
du_'8846''45'strictlySurjective_104 ::
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8846''45'strictlySurjective_104 v0 v1
  = coe
      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8321'_88))
              (coe v0 v2)))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
              (coe
                 (\ v3 ->
                    coe
                      MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8322'_94))
              (coe v1 v2)))
-- Data.Sum.Function.Setoid.⊎-surjective
d_'8846''45'surjective_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8846''45'surjective_114 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18 v19
  = du_'8846''45'surjective_114 v18 v19
du_'8846''45'surjective_114 ::
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8846''45'surjective_114 v0 v1
  = coe
      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
              (\ v3 v4 v5 v6 -> coe du_'46'extendedlambda0_120 v4 v5 v6)
              (coe v0 v2)))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Data.Product.Base.du_map_128
              (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
              (\ v3 v4 v5 v6 -> coe du_'46'extendedlambda1_126 v4 v5 v6)
              (coe v1 v2)))
-- Data.Sum.Function.Setoid..extendedlambda0
d_'46'extendedlambda0_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70
d_'46'extendedlambda0_120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 v23
                          v24
  = du_'46'extendedlambda0_120 v22 v23 v24
du_'46'extendedlambda0_120 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70
du_'46'extendedlambda0_120 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8321'_88 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8321'_88
                    (coe v0 v6 v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Function.Setoid..extendedlambda1
d_'46'extendedlambda1_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70
d_'46'extendedlambda1_126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 v22 v23
                          v24
  = du_'46'extendedlambda1_126 v22 v23 v24
du_'46'extendedlambda1_126 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70
du_'46'extendedlambda1_126 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8322'_94 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8322'_94
                    (coe v0 v6 v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Function.Setoid._⊎-function_
d__'8846''45'function__132 ::
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
d__'8846''45'function__132 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12 v13
  = du__'8846''45'function__132 v12 v13
du__'8846''45'function__132 ::
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
du__'8846''45'function__132 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Func'46'constructor_6307
      (coe
         MAlonzo.Code.Data.Sum.Base.du_map_84
         (coe MAlonzo.Code.Function.Bundles.d_to_720 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to_720 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.du_map_100
         (coe MAlonzo.Code.Function.Bundles.d_cong_722 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_722 (coe v1)))
-- Data.Sum.Function.Setoid._⊎-equivalence_
d__'8846''45'equivalence__142 ::
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
d__'8846''45'equivalence__142 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10 ~v11 v12 v13
  = du__'8846''45'equivalence__142 v12 v13
du__'8846''45'equivalence__142 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du__'8846''45'equivalence__142 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Equivalence'46'constructor_25797
      (coe
         MAlonzo.Code.Data.Sum.Base.du_map_84
         (coe MAlonzo.Code.Function.Bundles.d_to_1724 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to_1724 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Base.du_map_84
         (coe MAlonzo.Code.Function.Bundles.d_from_1726 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_from_1726 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.du_map_100
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1728 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1728 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.du_map_100
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1730 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1730 (coe v1)))
-- Data.Sum.Function.Setoid._⊎-injection_
d__'8846''45'injection__152 ::
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
d__'8846''45'injection__152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10 ~v11 v12 v13
  = du__'8846''45'injection__152 v12 v13
du__'8846''45'injection__152 ::
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776
du__'8846''45'injection__152 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Injection'46'constructor_8675
      (coe
         MAlonzo.Code.Data.Sum.Base.du_map_84
         (coe MAlonzo.Code.Function.Bundles.d_to_784 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to_784 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.du_map_100
         (coe MAlonzo.Code.Function.Bundles.d_cong_786 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_786 (coe v1)))
      (coe
         du_'8846''45'injective_78
         (coe MAlonzo.Code.Function.Bundles.d_injective_788 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_injective_788 (coe v1)))
-- Data.Sum.Function.Setoid._⊎-surjection_
d__'8846''45'surjection__162 ::
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
d__'8846''45'surjection__162 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 ~v10 ~v11 v12 v13
  = du__'8846''45'surjection__162 v12 v13
du__'8846''45'surjection__162 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
du__'8846''45'surjection__162 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Surjection'46'constructor_11197
      (coe
         MAlonzo.Code.Data.Sum.Base.du_map_84
         (coe MAlonzo.Code.Function.Bundles.d_to_854 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to_854 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.du_map_100
         (coe MAlonzo.Code.Function.Bundles.d_cong_856 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_856 (coe v1)))
      (coe
         du_'8846''45'surjective_114
         (coe MAlonzo.Code.Function.Bundles.d_surjective_858 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_surjective_858 (coe v1)))
-- Data.Sum.Function.Setoid._⊎-bijection_
d__'8846''45'bijection__172 ::
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
d__'8846''45'bijection__172 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10 ~v11 v12 v13
  = du__'8846''45'bijection__172 v12 v13
du__'8846''45'bijection__172 ::
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
du__'8846''45'bijection__172 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Bijection'46'constructor_15277
      (coe
         MAlonzo.Code.Data.Sum.Base.du_map_84
         (coe MAlonzo.Code.Function.Bundles.d_to_934 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to_934 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.du_map_100
         (coe MAlonzo.Code.Function.Bundles.d_cong_936 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_936 (coe v1)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            du_'8846''45'injective_78
            (coe MAlonzo.Code.Function.Bundles.du_injective_940 (coe v0))
            (coe MAlonzo.Code.Function.Bundles.du_injective_940 (coe v1)))
         (coe
            du_'8846''45'surjective_114
            (coe MAlonzo.Code.Function.Bundles.du_surjective_942 (coe v0))
            (coe MAlonzo.Code.Function.Bundles.du_surjective_942 (coe v1))))
-- Data.Sum.Function.Setoid._⊎-leftInverse_
d__'8846''45'leftInverse__182 ::
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
d__'8846''45'leftInverse__182 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10 ~v11 v12 v13
  = du__'8846''45'leftInverse__182 v12 v13
du__'8846''45'leftInverse__182 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
du__'8846''45'leftInverse__182 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_LeftInverse'46'constructor_29775
      (coe
         MAlonzo.Code.Data.Sum.Base.du_map_84
         (coe MAlonzo.Code.Function.Bundles.d_to_1804 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to_1804 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Base.du_map_84
         (coe MAlonzo.Code.Function.Bundles.d_from_1806 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_from_1806 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.du_map_100
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1808 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1808 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.du_map_100
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1810 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1810 (coe v1)))
      (coe du_'46'extendedlambda2_192 (coe v0) (coe v1))
-- Data.Sum.Function.Setoid._..extendedlambda2
d_'46'extendedlambda2_192 ::
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
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70
d_'46'extendedlambda2_192 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 v12 v13 v14 v15 v16
  = du_'46'extendedlambda2_192 v12 v13 v14 v15 v16
du_'46'extendedlambda2_192 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70
du_'46'extendedlambda2_192 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8321'_88 v8
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8321'_88
                           (coe MAlonzo.Code.Function.Bundles.d_inverse'737'_1812 v0 v5 v9 v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8322'_94 v8
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8322'_94
                           (coe MAlonzo.Code.Function.Bundles.d_inverse'737'_1812 v1 v5 v9 v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Function.Setoid._⊎-rightInverse_
d__'8846''45'rightInverse__198 ::
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
d__'8846''45'rightInverse__198 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 v12 v13
  = du__'8846''45'rightInverse__198 v12 v13
du__'8846''45'rightInverse__198 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
du__'8846''45'rightInverse__198 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_RightInverse'46'constructor_34573
      (coe
         MAlonzo.Code.Data.Sum.Base.du_map_84
         (coe MAlonzo.Code.Function.Bundles.d_to_1892 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to_1892 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Base.du_map_84
         (coe MAlonzo.Code.Function.Bundles.d_from_1894 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_from_1894 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.du_map_100
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1896 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1896 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.du_map_100
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1898 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1898 (coe v1)))
      (coe du_'46'extendedlambda2_208 (coe v0) (coe v1))
-- Data.Sum.Function.Setoid._..extendedlambda2
d_'46'extendedlambda2_208 ::
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
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70
d_'46'extendedlambda2_208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 v12 v13 v14 v15 v16
  = du_'46'extendedlambda2_208 v12 v13 v14 v15 v16
du_'46'extendedlambda2_208 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70
du_'46'extendedlambda2_208 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8321'_88 v8
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8321'_88
                           (coe MAlonzo.Code.Function.Bundles.d_inverse'691'_1900 v0 v5 v9 v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8322'_94 v8
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8322'_94
                           (coe MAlonzo.Code.Function.Bundles.d_inverse'691'_1900 v1 v5 v9 v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Function.Setoid._⊎-inverse_
d__'8846''45'inverse__214 ::
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
d__'8846''45'inverse__214 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 v12 v13
  = du__'8846''45'inverse__214 v12 v13
du__'8846''45'inverse__214 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du__'8846''45'inverse__214 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Inverse'46'constructor_38621
      (coe
         MAlonzo.Code.Data.Sum.Base.du_map_84
         (coe MAlonzo.Code.Function.Bundles.d_to_1972 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to_1972 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Base.du_map_84
         (coe MAlonzo.Code.Function.Bundles.d_from_1974 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_from_1974 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.du_map_100
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1976 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1976 (coe v1)))
      (coe
         MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.du_map_100
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1978 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1978 (coe v1)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe du_'46'extendedlambda2_224 (coe v0) (coe v1))
         (coe du_'46'extendedlambda3_230 (coe v0) (coe v1)))
-- Data.Sum.Function.Setoid._..extendedlambda2
d_'46'extendedlambda2_224 ::
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
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70
d_'46'extendedlambda2_224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 v12 v13 v14 v15 v16
  = du_'46'extendedlambda2_224 v12 v13 v14 v15 v16
du_'46'extendedlambda2_224 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70
du_'46'extendedlambda2_224 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8321'_88 v8
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8321'_88
                           (coe
                              MAlonzo.Code.Function.Bundles.du_inverse'737'_1982 v0 v5 v9 v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8322'_94 v8
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8322'_94
                           (coe
                              MAlonzo.Code.Function.Bundles.du_inverse'737'_1982 v1 v5 v9 v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Function.Setoid._..extendedlambda3
d_'46'extendedlambda3_230 ::
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
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70
d_'46'extendedlambda3_230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 v12 v13 v14 v15 v16
  = du_'46'extendedlambda3_230 v12 v13 v14 v15 v16
du_'46'extendedlambda3_230 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70 ->
  MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.T_Pointwise_70
du_'46'extendedlambda3_230 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8321'_88 v8
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8321'_88
                           (coe
                              MAlonzo.Code.Function.Bundles.du_inverse'691'_1984 v0 v5 v9 v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8322'_94 v8
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.C_inj'8322'_94
                           (coe
                              MAlonzo.Code.Function.Bundles.du_inverse'691'_1984 v1 v5 v9 v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Function.Setoid._⊎-left-inverse_
d__'8846''45'left'45'inverse__236 ::
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
d__'8846''45'left'45'inverse__236 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                  v11 v12 v13
  = coe du__'8846''45'leftInverse__182 v12 v13
