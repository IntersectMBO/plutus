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

module MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Bool qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Relation.Nullary.Reflects qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Sum.Relation.Binary.Pointwise.Pointwise
d_Pointwise_70 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
data T_Pointwise_70
  = C_inj'8321'_88 AgdaAny | C_inj'8322'_94 AgdaAny
-- Data.Sum.Relation.Binary.Pointwise.map
d_map_100 ::
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
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 -> T_Pointwise_70
d_map_100 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 v18 v19 v20 v21 v22
  = du_map_100 v18 v19 v20 v21 v22
du_map_100 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 -> T_Pointwise_70
du_map_100 v0 v1 v2 v3 v4
  = case coe v4 of
      C_inj'8321'_88 v7
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe C_inj'8321'_88 (coe v0 v8 v9 v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_inj'8322'_94 v7
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe C_inj'8322'_94 (coe v1 v8 v9 v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Relation.Binary.Pointwise.drop-inj₁
d_drop'45'inj'8321'_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> T_Pointwise_70 -> AgdaAny
d_drop'45'inj'8321'_114 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 ~v13 v14
  = du_drop'45'inj'8321'_114 v14
du_drop'45'inj'8321'_114 :: T_Pointwise_70 -> AgdaAny
du_drop'45'inj'8321'_114 v0
  = case coe v0 of
      C_inj'8321'_88 v3 -> coe v3
      _                 -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Relation.Binary.Pointwise.drop-inj₂
d_drop'45'inj'8322'_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> T_Pointwise_70 -> AgdaAny
d_drop'45'inj'8322'_122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 ~v13 v14
  = du_drop'45'inj'8322'_122 v14
du_drop'45'inj'8322'_122 :: T_Pointwise_70 -> AgdaAny
du_drop'45'inj'8322'_122 v0
  = case coe v0 of
      C_inj'8322'_94 v3 -> coe v3
      _                 -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Relation.Binary.Pointwise.⊎-refl
d_'8846''45'refl_126 ::
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
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_Pointwise_70
d_'8846''45'refl_126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_'8846''45'refl_126 v8 v9 v10
du_'8846''45'refl_126 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_Pointwise_70
du_'8846''45'refl_126 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
        -> coe C_inj'8321'_88 (coe v0 v3)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe C_inj'8322'_94 (coe v1 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Relation.Binary.Pointwise.⊎-symmetric
d_'8846''45'symmetric_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 -> T_Pointwise_70
d_'8846''45'symmetric_140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
                          v11 v12
  = du_'8846''45'symmetric_140 v8 v9 v10 v11 v12
du_'8846''45'symmetric_140 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 -> T_Pointwise_70
du_'8846''45'symmetric_140 v0 v1 v2 v3 v4
  = case coe v4 of
      C_inj'8321'_88 v7
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe C_inj'8321'_88 (coe v0 v8 v9 v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_inj'8322'_94 v7
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe C_inj'8322'_94 (coe v1 v8 v9 v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Relation.Binary.Pointwise.⊎-transitive
d_'8846''45'transitive_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 -> T_Pointwise_70 -> T_Pointwise_70
d_'8846''45'transitive_154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
                           v10 v11 v12 v13 v14
  = du_'8846''45'transitive_154 v8 v9 v10 v11 v12 v13 v14
du_'8846''45'transitive_154 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 -> T_Pointwise_70 -> T_Pointwise_70
du_'8846''45'transitive_154 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      C_inj'8321'_88 v9
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v6 of
                           C_inj'8321'_88 v14
                             -> case coe v4 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v15
                                    -> coe C_inj'8321'_88 (coe v0 v10 v11 v15 v9 v14)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_inj'8322'_94 v9
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v6 of
                           C_inj'8322'_94 v14
                             -> case coe v4 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v15
                                    -> coe C_inj'8322'_94 (coe v1 v10 v11 v15 v9 v14)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Relation.Binary.Pointwise.⊎-asymmetric
d_'8846''45'asymmetric_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 ->
  T_Pointwise_70 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8846''45'asymmetric_172 = erased
-- Data.Sum.Relation.Binary.Pointwise..extendedlambda0
d_'46'extendedlambda0_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T_Pointwise_70 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda0_180 = erased
-- Data.Sum.Relation.Binary.Pointwise..extendedlambda1
d_'46'extendedlambda1_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T_Pointwise_70 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda1_190 = erased
-- Data.Sum.Relation.Binary.Pointwise.⊎-substitutive
d_'8846''45'substitutive_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 -> AgdaAny -> AgdaAny
d_'8846''45'substitutive_194 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
                             v10 v11 v12 v13 v14
  = du_'8846''45'substitutive_194 v9 v10 v11 v12 v13 v14
du_'8846''45'substitutive_194 ::
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 -> AgdaAny -> AgdaAny
du_'8846''45'substitutive_194 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_inj'8321'_88 v8
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                      -> coe
                           v0
                           (\ v11 ->
                              coe v2 (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v11)))
                           v9 v10 v8
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_inj'8322'_94 v8
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                      -> coe
                           v1
                           (\ v11 ->
                              coe v2 (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v11)))
                           v9 v10 v8
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Relation.Binary.Pointwise.⊎-decidable
d_'8846''45'decidable_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8846''45'decidable_212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 v12 v13 v14 v15
  = du_'8846''45'decidable_212 v12 v13 v14 v15
du_'8846''45'decidable_212 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8846''45'decidable_212 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                    (coe C_inj'8321'_88) (coe du_drop'45'inj'8321'_114) (coe v0 v4 v5)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                    (coe C_inj'8322'_94) (coe du_drop'45'inj'8322'_122) (coe v1 v4 v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Relation.Binary.Pointwise.⊎-reflexive
d_'8846''45'reflexive_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 -> T_Pointwise_70
d_'8846''45'reflexive_246 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 v12 v13 v14 v15 v16
  = du_'8846''45'reflexive_246 v12 v13 v14 v15 v16
du_'8846''45'reflexive_246 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 -> T_Pointwise_70
du_'8846''45'reflexive_246 v0 v1 v2 v3 v4
  = case coe v4 of
      C_inj'8321'_88 v7
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe C_inj'8321'_88 (coe v0 v8 v9 v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_inj'8322'_94 v7
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe C_inj'8322'_94 (coe v1 v8 v9 v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Relation.Binary.Pointwise.⊎-irreflexive
d_'8846''45'irreflexive_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 ->
  T_Pointwise_70 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8846''45'irreflexive_260 = erased
-- Data.Sum.Relation.Binary.Pointwise.⊎-antisymmetric
d_'8846''45'antisymmetric_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 -> T_Pointwise_70 -> T_Pointwise_70
d_'8846''45'antisymmetric_278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10 ~v11 v12 v13 v14 v15 v16 v17
  = du_'8846''45'antisymmetric_278 v12 v13 v14 v15 v16 v17
du_'8846''45'antisymmetric_278 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 -> T_Pointwise_70 -> T_Pointwise_70
du_'8846''45'antisymmetric_278 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C_inj'8321'_88 v8
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                      -> case coe v5 of
                           C_inj'8321'_88 v13 -> coe C_inj'8321'_88 (coe v0 v9 v10 v8 v13)
                           _                  -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_inj'8322'_94 v8
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                      -> case coe v5 of
                           C_inj'8322'_94 v13 -> coe C_inj'8322'_94 (coe v1 v9 v10 v8 v13)
                           _                  -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Relation.Binary.Pointwise.⊎-respectsˡ
d_'8846''45'respects'737'_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 -> T_Pointwise_70 -> T_Pointwise_70
d_'8846''45'respects'737'_296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 v21 v22
  = du_'8846''45'respects'737'_296 v16 v17 v18 v19 v20 v21 v22
du_'8846''45'respects'737'_296 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 -> T_Pointwise_70 -> T_Pointwise_70
du_'8846''45'respects'737'_296 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      C_inj'8321'_88 v9
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v6 of
                           C_inj'8321'_88 v14
                             -> case coe v2 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v15
                                    -> coe C_inj'8321'_88 (coe v0 v15 v10 v11 v9 v14)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_inj'8322'_94 v9
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v6 of
                           C_inj'8322'_94 v14
                             -> case coe v2 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v15
                                    -> coe C_inj'8322'_94 (coe v1 v15 v10 v11 v9 v14)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Relation.Binary.Pointwise.⊎-respectsʳ
d_'8846''45'respects'691'_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 -> T_Pointwise_70 -> T_Pointwise_70
d_'8846''45'respects'691'_314 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16 v17 v18 v19 v20 v21 v22
  = du_'8846''45'respects'691'_314 v16 v17 v18 v19 v20 v21 v22
du_'8846''45'respects'691'_314 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 -> T_Pointwise_70 -> T_Pointwise_70
du_'8846''45'respects'691'_314 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      C_inj'8321'_88 v9
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v6 of
                           C_inj'8321'_88 v14
                             -> case coe v2 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v15
                                    -> coe C_inj'8321'_88 (coe v0 v15 v10 v11 v9 v14)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_inj'8322'_94 v9
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v6 of
                           C_inj'8322'_94 v14
                             -> case coe v2 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v15
                                    -> coe C_inj'8322'_94 (coe v1 v15 v10 v11 v9 v14)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Relation.Binary.Pointwise.⊎-respects₂
d_'8846''45'respects'8322'_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8846''45'respects'8322'_332 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 v12 v13
  = du_'8846''45'respects'8322'_332 v12 v13
du_'8846''45'respects'8322'_332 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8846''45'respects'8322'_332 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_'8846''45'respects'691'_314 (coe v2) (coe v4))
                    (coe du_'8846''45'respects'737'_296 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Relation.Binary.Pointwise.⊎-isEquivalence
d_'8846''45'isEquivalence_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8846''45'isEquivalence_342 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_'8846''45'isEquivalence_342 v8 v9
du_'8846''45'isEquivalence_342 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_'8846''45'isEquivalence_342 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
      (coe
         du_'8846''45'refl_126
         (coe MAlonzo.Code.Relation.Binary.Structures.d_refl_34 (coe v0))
         (coe MAlonzo.Code.Relation.Binary.Structures.d_refl_34 (coe v1)))
      (coe
         du_'8846''45'symmetric_140
         (coe MAlonzo.Code.Relation.Binary.Structures.d_sym_36 (coe v0))
         (coe MAlonzo.Code.Relation.Binary.Structures.d_sym_36 (coe v1)))
      (coe
         du_'8846''45'transitive_154
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_38 (coe v0))
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_38 (coe v1)))
-- Data.Sum.Relation.Binary.Pointwise.⊎-isDecEquivalence
d_'8846''45'isDecEquivalence_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_'8846''45'isDecEquivalence_352 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
                                 v9
  = du_'8846''45'isDecEquivalence_352 v8 v9
du_'8846''45'isDecEquivalence_352 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
du_'8846''45'isDecEquivalence_352 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecEquivalence'46'constructor_3083
      (coe
         du_'8846''45'isEquivalence_342
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
            (coe v1)))
      (coe
         du_'8846''45'decidable_212
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__52 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__52 (coe v1)))
-- Data.Sum.Relation.Binary.Pointwise.⊎-isPreorder
d_'8846''45'isPreorder_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_'8846''45'isPreorder_362 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 v12 v13
  = du_'8846''45'isPreorder_362 v12 v13
du_'8846''45'isPreorder_362 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_'8846''45'isPreorder_362 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe
         du_'8846''45'isEquivalence_342
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
            (coe v1)))
      (coe
         du_'8846''45'reflexive_246
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82 (coe v1)))
      (coe
         du_'8846''45'transitive_154
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_84 (coe v0))
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_84 (coe v1)))
-- Data.Sum.Relation.Binary.Pointwise.⊎-isPartialOrder
d_'8846''45'isPartialOrder_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_'8846''45'isPartialOrder_372 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 ~v11 v12 v13
  = du_'8846''45'isPartialOrder_372 v12 v13
du_'8846''45'isPartialOrder_372 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
du_'8846''45'isPartialOrder_372 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPartialOrder'46'constructor_9853
      (coe
         du_'8846''45'isPreorder_362
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
      (coe
         du_'8846''45'antisymmetric_278
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_antisym_184 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_antisym_184 (coe v1)))
-- Data.Sum.Relation.Binary.Pointwise.⊎-isStrictPartialOrder
d_'8846''45'isStrictPartialOrder_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'8846''45'isStrictPartialOrder_382 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                     ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
  = du_'8846''45'isStrictPartialOrder_382 v12 v13
du_'8846''45'isStrictPartialOrder_382 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
du_'8846''45'isStrictPartialOrder_382 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_14045
      (coe
         du_'8846''45'isEquivalence_342
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
            (coe v1)))
      (coe
         du_'8846''45'transitive_154
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_306 (coe v0))
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_306 (coe v1)))
      (coe
         du_'8846''45'respects'8322'_332
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
            (coe v1)))
-- Data.Sum.Relation.Binary.Pointwise.⊎-setoid
d_'8846''45'setoid_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'8846''45'setoid_392 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8846''45'setoid_392 v4 v5
du_'8846''45'setoid_392 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_'8846''45'setoid_392 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_733
      (coe
         du_'8846''45'isEquivalence_342
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Data.Sum.Relation.Binary.Pointwise.⊎-decSetoid
d_'8846''45'decSetoid_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
d_'8846''45'decSetoid_402 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8846''45'decSetoid_402 v4 v5
du_'8846''45'decSetoid_402 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
du_'8846''45'decSetoid_402 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecSetoid'46'constructor_1389
      (coe
         du_'8846''45'isDecEquivalence_352
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_100
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_100
            (coe v1)))
-- Data.Sum.Relation.Binary.Pointwise.⊎-preorder
d_'8846''45'preorder_412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_'8846''45'preorder_412 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_'8846''45'preorder_412 v6 v7
du_'8846''45'preorder_412 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_'8846''45'preorder_412 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Preorder'46'constructor_2267
      (coe
         du_'8846''45'isPreorder_362
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v1)))
-- Data.Sum.Relation.Binary.Pointwise.⊎-poset
d_'8846''45'poset_422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_'8846''45'poset_422 ~v0 ~v1 ~v2 v3 v4
  = du_'8846''45'poset_422 v3 v4
du_'8846''45'poset_422 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_'8846''45'poset_422 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Poset'46'constructor_6389
      (coe
         du_'8846''45'isPartialOrder_372
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
            (coe v1)))
-- Data.Sum.Relation.Binary.Pointwise._⊎ₛ_
d__'8846''8347'__432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d__'8846''8347'__432 ~v0 ~v1 ~v2 ~v3 = du__'8846''8347'__432
du__'8846''8347'__432 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du__'8846''8347'__432 = coe du_'8846''45'setoid_392
-- Data.Sum.Relation.Binary.Pointwise.Pointwise-≡⇒≡
d_Pointwise'45''8801''8658''8801'_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  T_Pointwise_70 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Pointwise'45''8801''8658''8801'_434 = erased
-- Data.Sum.Relation.Binary.Pointwise.≡⇒Pointwise-≡
d_'8801''8658'Pointwise'45''8801'_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Pointwise_70
d_'8801''8658'Pointwise'45''8801'_440 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du_'8801''8658'Pointwise'45''8801'_440 v4
du_'8801''8658'Pointwise'45''8801'_440 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_Pointwise_70
du_'8801''8658'Pointwise'45''8801'_440 v0
  = coe du_'8846''45'refl_126 erased erased (coe v0)
-- Data.Sum.Relation.Binary.Pointwise.Pointwise-≡↔≡
d_Pointwise'45''8801''8596''8801'_446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_Pointwise'45''8801''8596''8801'_446 ~v0 ~v1 ~v2 ~v3
  = du_Pointwise'45''8801''8596''8801'_446
du_Pointwise'45''8801''8596''8801'_446 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_Pointwise'45''8801''8596''8801'_446
  = coe
      MAlonzo.Code.Function.Bundles.C_Inverse'46'constructor_38621
      (coe (\ v0 -> v0)) (coe (\ v0 -> v0)) erased
      (\ v0 v1 v2 -> coe du_'8801''8658'Pointwise'45''8801'_440 v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            (\ v0 v1 v2 ->
               coe du_'8801''8658'Pointwise'45''8801'_440 (coe v1))))
