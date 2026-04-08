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

module MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.List.Relation.Binary.Pointwise.Properties.reflexive
d_reflexive_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_reflexive_28 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_reflexive_28
du_reflexive_28 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_reflexive_28
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.du_map_120
-- Data.List.Relation.Binary.Pointwise.Properties.refl
d_refl_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_refl_30 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_refl_30 v4 v5
du_refl_30 ::
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_refl_30 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
             (coe v0 v2) (coe du_refl_30 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.Properties.symmetric
d_symmetric_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_symmetric_40 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11
  = du_symmetric_40 v8 v9 v10 v11
du_symmetric_40 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_symmetric_40 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe v3
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v8 v9
        -> case coe v1 of
             (:) v10 v11
               -> case coe v2 of
                    (:) v12 v13
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                           (coe v0 v10 v12 v8)
                           (coe du_symmetric_40 (coe v0) (coe v11) (coe v13) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.Properties.transitive
d_transitive_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_transitive_50 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12 v13 v14 v15 v16 v17
  = du_transitive_50 v12 v13 v14 v15 v16 v17
du_transitive_50 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_transitive_50 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe seq (coe v5) (coe v4)
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v10 v11
        -> case coe v1 of
             (:) v12 v13
               -> case coe v2 of
                    (:) v14 v15
                      -> case coe v5 of
                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v20 v21
                             -> case coe v3 of
                                  (:) v22 v23
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                         (coe v0 v12 v14 v22 v10 v20)
                                         (coe
                                            du_transitive_50 (coe v0) (coe v13) (coe v15) (coe v23)
                                            (coe v11) (coe v21))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.Properties.antisymmetric
d_antisymmetric_64 ::
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
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_antisymmetric_64 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
                   v12 v13 v14
  = du_antisymmetric_64 v10 v11 v12 v13 v14
du_antisymmetric_64 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_antisymmetric_64 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe seq (coe v4) (coe v3)
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v9 v10
        -> case coe v1 of
             (:) v11 v12
               -> case coe v2 of
                    (:) v13 v14
                      -> case coe v4 of
                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v19 v20
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                  (coe v0 v11 v13 v9 v19)
                                  (coe
                                     du_antisymmetric_64 (coe v0) (coe v12) (coe v14) (coe v10)
                                     (coe v20))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.Properties.respʳ
d_resp'691'_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_resp'691'_78 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 v12
               v13
  = du_resp'691'_78 v8 v9 v10 v11 v12 v13
du_resp'691'_78 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_resp'691'_78 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe seq (coe v5) (coe v4)
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v10 v11
        -> case coe v2 of
             (:) v12 v13
               -> case coe v3 of
                    (:) v14 v15
                      -> case coe v5 of
                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v20 v21
                             -> case coe v1 of
                                  (:) v22 v23
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                         (coe v0 v22 v12 v14 v10 v20)
                                         (coe
                                            du_resp'691'_78 (coe v0) (coe v23) (coe v13) (coe v15)
                                            (coe v11) (coe v21))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.Properties.respˡ
d_resp'737'_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_resp'737'_92 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 v12
               v13
  = du_resp'737'_92 v8 v9 v10 v11 v12 v13
du_resp'737'_92 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_resp'737'_92 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe seq (coe v5) (coe v4)
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v10 v11
        -> case coe v2 of
             (:) v12 v13
               -> case coe v3 of
                    (:) v14 v15
                      -> case coe v5 of
                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v20 v21
                             -> case coe v1 of
                                  (:) v22 v23
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                         (coe v0 v22 v12 v14 v10 v20)
                                         (coe
                                            du_resp'737'_92 (coe v0) (coe v23) (coe v13) (coe v15)
                                            (coe v11) (coe v21))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.Properties.respects₂
d_respects'8322'_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_respects'8322'_106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_respects'8322'_106 v6
du_respects'8322'_106 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_respects'8322'_106 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_resp'691'_78 (coe v1)) (coe du_resp'737'_92 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.Properties.decidable
d_decidable_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decidable_112 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_decidable_112 v6 v7 v8
du_decidable_112 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_decidable_112 v0 v1 v2
  = case coe v1 of
      []
        -> case coe v2 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe
                          MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56))
             (:) v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v3 v4
        -> case coe v2 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             (:) v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    (coe
                       MAlonzo.Code.Data.Product.Base.du_uncurry_244
                       (coe
                          MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.du_uncons_76)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                       (coe v0 v3 v5) (coe du_decidable_112 (coe v0) (coe v4) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.Properties.irrelevant
d_irrelevant_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irrelevant_132 = erased
-- Data.List.Relation.Binary.Pointwise.Properties.Pointwise-length
d_Pointwise'45'length_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Pointwise'45'length_150 = erased
-- Data.List.Relation.Binary.Pointwise.Properties.lookup-cast
d_lookup'45'cast_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_lookup'45'cast_164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9 v10
  = du_lookup'45'cast_164 v6 v7 v8 v10
du_lookup'45'cast_164 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_lookup'45'cast_164 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v1 of
                    (:) v12 v13
                      -> case coe v3 of
                           MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v8
                           MAlonzo.Code.Data.Fin.Base.C_suc_16 v15
                             -> coe du_lookup'45'cast_164 (coe v11) (coe v13) (coe v9) (coe v15)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
