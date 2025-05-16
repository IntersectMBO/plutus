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

module MAlonzo.Code.Data.List.Relation.Unary.All where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Bool qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.List qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.List.Relation.Unary.Any qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Effect.Applicative qualified
import MAlonzo.Code.Effect.Functor qualified
import MAlonzo.Code.Effect.Monad qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Relation.Nullary.Reflects qualified
import MAlonzo.Code.Relation.Unary.Properties qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.List.Relation.Unary.All.All
d_All_44 a0 a1 a2 a3 a4 = ()
data T_All_44 = C_'91''93'_50 | C__'8759'__60 AgdaAny T_All_44
-- Data.List.Relation.Unary.All._[_]=_
d__'91'_'93''61'__74 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T__'91'_'93''61'__74
  = C_here_88 | C_there_104 T__'91'_'93''61'__74
-- Data.List.Relation.Unary.All.Null
d_Null_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> [AgdaAny] -> ()
d_Null_106 = erased
-- Data.List.Relation.Unary.All.uncons
d_uncons_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] -> T_All_44 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_uncons_108 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_uncons_108 v6
du_uncons_108 :: T_All_44 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_uncons_108 v0
  = case coe v0 of
      C__'8759'__60 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All.head
d_head_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) -> AgdaAny -> [AgdaAny] -> T_All_44 -> AgdaAny
d_head_114 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_head_114 v6
du_head_114 :: T_All_44 -> AgdaAny
du_head_114 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_uncons_108 (coe v0))
-- Data.List.Relation.Unary.All.tail
d_tail_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) -> AgdaAny -> [AgdaAny] -> T_All_44 -> T_All_44
d_tail_116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_tail_116 v6
du_tail_116 :: T_All_44 -> T_All_44
du_tail_116 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe du_uncons_108 (coe v0))
-- Data.List.Relation.Unary.All.reduce
d_reduce_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_All_44 -> [AgdaAny]
d_reduce_122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_reduce_122 v6 v7 v8
du_reduce_122 ::
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_All_44 -> [AgdaAny]
du_reduce_122 v0 v1 v2
  = case coe v2 of
      C_'91''93'_50 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C__'8759'__60 v5 v6
        -> case coe v0 of
             (:) v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1 v7 v5)
                    (coe du_reduce_122 (coe v8) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All.construct
d_construct_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_construct_136 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_construct_136 v6 v7
du_construct_136 ::
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_construct_136 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe C_'91''93'_50)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Product.Base.du_zip_198
             (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22)
             (\ v4 v5 v6 v7 -> coe C__'8759'__60 v6 v7) (coe v0 v2)
             (coe du_construct_136 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All.fromList
d_fromList_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_All_44
d_fromList_148 ~v0 ~v1 ~v2 ~v3 v4 = du_fromList_148 v4
du_fromList_148 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_All_44
du_fromList_148 v0
  = case coe v0 of
      [] -> coe C_'91''93'_50
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe C__'8759'__60 v4 (coe du_fromList_148 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All.toList
d_toList_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] -> T_All_44 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_toList_156 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_toList_156 v4 v5
du_toList_156 ::
  [AgdaAny] -> T_All_44 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_toList_156 v0 v1
  = coe
      du_reduce_122 (coe v0)
      (coe
         (\ v2 v3 ->
            coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)))
      (coe v1)
-- Data.List.Relation.Unary.All.map
d_map_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> T_All_44 -> T_All_44
d_map_164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 = du_map_164 v6 v7 v8
du_map_164 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> T_All_44 -> T_All_44
du_map_164 v0 v1 v2
  = case coe v2 of
      C_'91''93'_50 -> coe v2
      C__'8759'__60 v5 v6
        -> case coe v1 of
             (:) v7 v8
               -> coe
                    C__'8759'__60 (coe v0 v7 v5)
                    (coe du_map_164 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All.zipWith
d_zipWith_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_All_44
d_zipWith_174 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_zipWith_174 v8 v9 v10
du_zipWith_174 ::
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_All_44
du_zipWith_174 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_'91''93'_50 -> coe seq (coe v4) (coe v3)
             C__'8759'__60 v7 v8
               -> case coe v1 of
                    (:) v9 v10
                      -> case coe v4 of
                           C__'8759'__60 v13 v14
                             -> coe
                                  C__'8759'__60
                                  (coe
                                     v0 v9
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                        (coe v13)))
                                  (coe
                                     du_zipWith_174 (coe v0) (coe v10)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                        (coe v14)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All.unzipWith
d_unzipWith_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [AgdaAny] -> T_All_44 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unzipWith_188 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_unzipWith_188 v8 v9 v10
du_unzipWith_188 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [AgdaAny] -> T_All_44 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unzipWith_188 v0 v1 v2
  = case coe v2 of
      C_'91''93'_50
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v2)
      C__'8759'__60 v5 v6
        -> case coe v1 of
             (:) v7 v8
               -> coe
                    MAlonzo.Code.Data.Product.Base.du_zip_198 (coe C__'8759'__60)
                    (coe (\ v9 v10 -> coe C__'8759'__60)) (coe v0 v7 v5)
                    (coe du_unzipWith_188 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All.zip
d_zip_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_All_44
d_zip_198 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_zip_198 v6
du_zip_198 ::
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_All_44
du_zip_198 v0 = coe du_zipWith_174 (coe (\ v1 v2 -> v2)) (coe v0)
-- Data.List.Relation.Unary.All.unzip
d_unzip_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] -> T_All_44 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unzip_200 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_unzip_200 v6
du_unzip_200 ::
  [AgdaAny] -> T_All_44 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unzip_200 v0
  = coe du_unzipWith_188 (coe (\ v1 v2 -> v2)) (coe v0)
-- Data.List.Relation.Unary.All._._._∈_
d__'8712'__240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> ()) -> AgdaAny -> [AgdaAny] -> ()
d__'8712'__240 = erased
-- Data.List.Relation.Unary.All._.tabulateₛ
d_tabulate'8347'_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny) ->
  T_All_44
d_tabulate'8347'_256 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_tabulate'8347'_256 v3 v5 v6
du_tabulate'8347'_256 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny) ->
  T_All_44
du_tabulate'8347'_256 v0 v1 v2
  = case coe v1 of
      [] -> coe C_'91''93'_50
      (:) v3 v4
        -> coe
             C__'8759'__60
             (coe
                v2 v3
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                   (coe
                      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                      (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
                      v3)))
             (coe
                du_tabulate'8347'_256 (coe v0) (coe v4)
                (coe
                   (\ v5 v6 ->
                      coe
                        v2 v5
                        (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v6))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All.tabulate
d_tabulate_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny) ->
  T_All_44
d_tabulate_264 ~v0 ~v1 v2 ~v3 ~v4 = du_tabulate_264 v2
du_tabulate_264 ::
  [AgdaAny] ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny) ->
  T_All_44
du_tabulate_264 v0
  = coe
      du_tabulate'8347'_256
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      (coe v0)
-- Data.List.Relation.Unary.All.self
d_self_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> T_All_44
d_self_268 ~v0 ~v1 v2 = du_self_268 v2
du_self_268 :: [AgdaAny] -> T_All_44
du_self_268 v0 = coe du_tabulate_264 v0 (\ v1 v2 -> v1)
-- Data.List.Relation.Unary.All.updateAt
d_updateAt_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  (AgdaAny -> AgdaAny) -> T_All_44 -> T_All_44
d_updateAt_274 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8
  = du_updateAt_274 v3 v6 v7 v8
du_updateAt_274 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  (AgdaAny -> AgdaAny) -> T_All_44 -> T_All_44
du_updateAt_274 v0 v1 v2 v3
  = case coe v3 of
      C__'8759'__60 v6 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v12
                      -> coe C__'8759'__60 (coe v2 v6) v7
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v12
                      -> coe
                           C__'8759'__60 v6
                           (coe du_updateAt_274 (coe v9) (coe v12) (coe v2) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All._[_]%=_
d__'91'_'93''37''61'__292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  AgdaAny ->
  T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  (AgdaAny -> AgdaAny) -> T_All_44
d__'91'_'93''37''61'__292 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8
  = du__'91'_'93''37''61'__292 v4 v6 v7 v8
du__'91'_'93''37''61'__292 ::
  [AgdaAny] ->
  T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  (AgdaAny -> AgdaAny) -> T_All_44
du__'91'_'93''37''61'__292 v0 v1 v2 v3
  = coe du_updateAt_274 (coe v0) (coe v2) (coe v3) (coe v1)
-- Data.List.Relation.Unary.All._[_]≔_
d__'91'_'93''8788'__300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  AgdaAny ->
  T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> T_All_44
d__'91'_'93''8788'__300 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8
  = du__'91'_'93''8788'__300 v4 v6 v7 v8
du__'91'_'93''8788'__300 ::
  [AgdaAny] ->
  T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> T_All_44
du__'91'_'93''8788'__300 v0 v1 v2 v3
  = coe
      du__'91'_'93''37''61'__292 (coe v0) (coe v1) (coe v2)
      (coe (\ v4 -> v3))
-- Data.List.Relation.Unary.All._.sequenceA
d_sequenceA_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  [AgdaAny] -> T_All_44 -> AgdaAny
d_sequenceA_358 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_sequenceA_358 v5 v6 v7
du_sequenceA_358 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  [AgdaAny] -> T_All_44 -> AgdaAny
du_sequenceA_358 v0 v1 v2
  = case coe v2 of
      C_'91''93'_50
        -> coe MAlonzo.Code.Effect.Applicative.d_pure_32 v0 erased v2
      C__'8759'__60 v5 v6
        -> case coe v1 of
             (:) v7 v8
               -> coe
                    MAlonzo.Code.Effect.Applicative.d__'60''42''62'__34 v0 erased
                    erased
                    (coe
                       MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
                       (MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v0)) erased
                       erased (coe C__'8759'__60) v5)
                    (coe du_sequenceA_358 (coe v0) (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All._.mapA
d_mapA_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> [AgdaAny] -> T_All_44 -> AgdaAny
d_mapA_366 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 v9
  = du_mapA_366 v5 v8 v9
du_mapA_366 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> [AgdaAny] -> T_All_44 -> AgdaAny
du_mapA_366 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe du_sequenceA_358 (coe v0) (coe v2))
      (coe du_map_164 (coe v1) (coe v2))
-- Data.List.Relation.Unary.All._.forA
d_forA_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [AgdaAny] ->
  (AgdaAny -> ()) ->
  T_All_44 -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
d_forA_372 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 v9 v10
  = du_forA_372 v5 v7 v9 v10
du_forA_372 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  [AgdaAny] -> T_All_44 -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
du_forA_372 v0 v1 v2 v3 = coe du_mapA_366 v0 v3 v1 v2
-- Data.List.Relation.Unary.All._.App
d_App_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
d_App_394 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_App_394 v5
du_App_394 ::
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
du_App_394 v0
  = coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0)
-- Data.List.Relation.Unary.All._.sequenceM
d_sequenceM_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  [AgdaAny] -> T_All_44 -> AgdaAny
d_sequenceM_396 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_sequenceM_396 v5 v6
du_sequenceM_396 ::
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  [AgdaAny] -> T_All_44 -> AgdaAny
du_sequenceM_396 v0 v1
  = coe du_sequenceA_358 (coe du_App_394 (coe v0)) (coe v1)
-- Data.List.Relation.Unary.All._.mapM
d_mapM_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> [AgdaAny] -> T_All_44 -> AgdaAny
d_mapM_400 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du_mapM_400 v5
du_mapM_400 ::
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> [AgdaAny] -> T_All_44 -> AgdaAny
du_mapM_400 v0 = coe du_mapA_366 (coe du_App_394 (coe v0))
-- Data.List.Relation.Unary.All._.forM
d_forM_404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [AgdaAny] ->
  (AgdaAny -> ()) ->
  T_All_44 -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
d_forM_404 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 = du_forM_404 v5 v7
du_forM_404 ::
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  [AgdaAny] -> T_All_44 -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
du_forM_404 v0 v1
  = coe du_forA_372 (coe du_App_394 (coe v0)) (coe v1)
-- Data.List.Relation.Unary.All.lookupAny
d_lookupAny_408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupAny_408 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
  = du_lookupAny_408 v4 v7 v8
du_lookupAny_408 ::
  [AgdaAny] ->
  T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lookupAny_408 v0 v1 v2
  = case coe v1 of
      C__'8759'__60 v5 v6
        -> case coe v0 of
             (:) v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v11)
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v11
                      -> coe du_lookupAny_408 (coe v8) (coe v6) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All.lookupWith
d_lookupWith_424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny
d_lookupWith_424 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11
  = du_lookupWith_424 v8 v9 v10 v11
du_lookupWith_424 ::
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny
du_lookupWith_424 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Product.Base.du_uncurry_244
      (coe
         v1
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.Any.du_lookup_94 (coe v0)
            (coe v3)))
      (coe du_lookupAny_408 (coe v0) (coe v2) (coe v3))
-- Data.List.Relation.Unary.All.lookup
d_lookup_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  T_All_44 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny
d_lookup_434 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 = du_lookup_434 v4 v5
du_lookup_434 ::
  [AgdaAny] ->
  T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny
du_lookup_434 v0 v1
  = coe du_lookupWith_424 (coe v0) (coe (\ v2 v3 v4 -> v3)) (coe v1)
-- Data.List.Relation.Unary.All..extendedlambda0
d_'46'extendedlambda0_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  T_All_44 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'46'extendedlambda0_438 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_'46'extendedlambda0_438 v8
du_'46'extendedlambda0_438 :: AgdaAny -> AgdaAny
du_'46'extendedlambda0_438 v0 = coe v0
-- Data.List.Relation.Unary.All._._._≈_
d__'8776'__458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d__'8776'__458 = erased
-- Data.List.Relation.Unary.All._._._∈_
d__'8712'__480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> ()) -> AgdaAny -> [AgdaAny] -> ()
d__'8712'__480 = erased
-- Data.List.Relation.Unary.All._.lookupₛ
d_lookup'8347'_496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  T_All_44 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny
d_lookup'8347'_496 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8
  = du_lookup'8347'_496 v3 v5 v6 v7 v8
du_lookup'8347'_496 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  T_All_44 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny
du_lookup'8347'_496 v0 v1 v2 v3 v4
  = coe
      du_lookupWith_424 (coe v1)
      (coe
         (\ v5 v6 v7 ->
            coe
              v2 v5 v4
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                 (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
                 v4 v5 v7)
              v6))
      (coe v3)
-- Data.List.Relation.Unary.All.all?
d_all'63'_506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_all'63'_506 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_all'63'_506 v4 v5
du_all'63'_506 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_all'63'_506 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe C_'91''93'_50))
      (:) v2 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
             (coe
                MAlonzo.Code.Data.Product.Base.du_uncurry_244 (coe C__'8759'__60))
             (coe du_uncons_108)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__76
                (coe v0 v2) (coe du_all'63'_506 (coe v0) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All.universal
d_universal_516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> T_All_44
d_universal_516 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_universal_516 v4 v5
du_universal_516 :: (AgdaAny -> AgdaAny) -> [AgdaAny] -> T_All_44
du_universal_516 v0 v1
  = case coe v1 of
      [] -> coe C_'91''93'_50
      (:) v2 v3
        -> coe
             C__'8759'__60 (coe v0 v2) (coe du_universal_516 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All.universal-U
d_universal'45'U_526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> T_All_44
d_universal'45'U_526 ~v0 ~v1 = du_universal'45'U_526
du_universal'45'U_526 :: [AgdaAny] -> T_All_44
du_universal'45'U_526
  = coe
      du_universal_516
      (\ v0 ->
         coe MAlonzo.Code.Relation.Unary.Properties.du_U'45'Universal_36)
-- Data.List.Relation.Unary.All.irrelevant
d_irrelevant_528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  T_All_44 ->
  T_All_44 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irrelevant_528 = erased
-- Data.List.Relation.Unary.All.satisfiable
d_satisfiable_542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_satisfiable_542 ~v0 ~v1 ~v2 ~v3 = du_satisfiable_542
du_satisfiable_542 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_satisfiable_542
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe C_'91''93'_50)
-- Data.List.Relation.Unary.All.decide
d_decide_544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_decide_544 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 = du_decide_544 v6 v7
du_decide_544 ::
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_decide_544 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe C_'91''93'_50)
      (:) v2 v3
        -> let v4 = coe v0 v2 in
           coe
             (case coe v4 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.du_map_84 (coe C__'8759'__60 v5)
                       (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54)
                       (coe du_decide_544 (coe v0) (coe v3))
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All.all
d_all_576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_all_576 v0 v1 v2 v3 v4 v5 = coe du_all'63'_506 v4 v5
