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

module MAlonzo.Code.Data.List.Relation.Unary.Any where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.List.Relation.Unary.Any.Any
d_Any_34 a0 a1 a2 a3 a4 = ()
data T_Any_34 = C_here_46 AgdaAny | C_there_54 T_Any_34
-- Data.List.Relation.Unary.Any.head
d_head_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  AgdaAny ->
  (T_Any_34 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Any_34 -> AgdaAny
d_head_56 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_head_56 v7
du_head_56 :: T_Any_34 -> AgdaAny
du_head_56 v0
  = case coe v0 of
      C_here_46 v3 -> coe v3
      C_there_54 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Any.tail
d_tail_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Any_34 -> T_Any_34
d_tail_66 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_tail_66 v7
du_tail_66 :: T_Any_34 -> T_Any_34
du_tail_66 v0
  = case coe v0 of
      C_here_46 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      C_there_54 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Any.map
d_map_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> T_Any_34 -> T_Any_34
d_map_76 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 = du_map_76 v6 v7 v8
du_map_76 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> T_Any_34 -> T_Any_34
du_map_76 v0 v1 v2
  = case coe v2 of
      C_here_46 v5
        -> case coe v1 of
             (:) v6 v7 -> coe C_here_46 (coe v0 v6 v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_there_54 v5
        -> case coe v1 of
             (:) v6 v7
               -> coe C_there_54 (coe du_map_76 (coe v0) (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Any.index
d_index_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] -> T_Any_34 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_index_86 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_index_86 v4 v5
du_index_86 ::
  [AgdaAny] -> T_Any_34 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_index_86 v0 v1
  = case coe v1 of
      C_here_46 v4 -> coe MAlonzo.Code.Data.Fin.Base.C_zero_12
      C_there_54 v4
        -> case coe v0 of
             (:) v5 v6
               -> coe
                    MAlonzo.Code.Data.Fin.Base.C_suc_16
                    (coe du_index_86 (coe v6) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Any.lookup
d_lookup_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [AgdaAny] -> (AgdaAny -> ()) -> T_Any_34 -> AgdaAny
d_lookup_94 ~v0 ~v1 ~v2 v3 ~v4 v5 = du_lookup_94 v3 v5
du_lookup_94 :: [AgdaAny] -> T_Any_34 -> AgdaAny
du_lookup_94 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_lookup_390 (coe v0)
      (coe du_index_86 (coe v0) (coe v1))
-- Data.List.Relation.Unary.Any._∷=_
d__'8759''61'__102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [AgdaAny] -> (AgdaAny -> ()) -> T_Any_34 -> AgdaAny -> [AgdaAny]
d__'8759''61'__102 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du__'8759''61'__102 v3 v5 v6
du__'8759''61'__102 ::
  [AgdaAny] -> T_Any_34 -> AgdaAny -> [AgdaAny]
du__'8759''61'__102 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Base.du__'91'_'93''8759''61'__970 (coe v0)
      (coe du_index_86 (coe v0) (coe v1)) (coe v2)
-- Data.List.Relation.Unary.Any._─_
d__'9472'__114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) -> [AgdaAny] -> T_Any_34 -> [AgdaAny]
d__'9472'__114 ~v0 ~v1 ~v2 ~v3 v4 v5 = du__'9472'__114 v4 v5
du__'9472'__114 :: [AgdaAny] -> T_Any_34 -> [AgdaAny]
du__'9472'__114 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_removeAt_570 (coe v0)
      (coe du_index_86 (coe v0) (coe v1))
-- Data.List.Relation.Unary.Any.satisfied
d_satisfied_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] -> T_Any_34 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_satisfied_120 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_satisfied_120 v4 v5
du_satisfied_120 ::
  [AgdaAny] -> T_Any_34 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_satisfied_120 v0 v1
  = case coe v1 of
      C_here_46 v4
        -> case coe v0 of
             (:) v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_there_54 v4
        -> case coe v0 of
             (:) v5 v6 -> coe du_satisfied_120 (coe v6) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Any.toSum
d_toSum_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] -> T_Any_34 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_toSum_126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_toSum_126 v6
du_toSum_126 ::
  T_Any_34 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_toSum_126 v0
  = case coe v0 of
      C_here_46 v3
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v3)
      C_there_54 v3
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Any.fromSum
d_fromSum_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_Any_34
d_fromSum_132 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_fromSum_132 v6
du_fromSum_132 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_Any_34
du_fromSum_132 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> coe C_here_46 v1
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1 -> coe C_there_54 v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Any.any?
d_any'63'_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_any'63'_138 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_any'63'_138 v4 v5
du_any'63'_138 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_any'63'_138 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
             (coe du_fromSum_132) (coe du_toSum_126)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
                (coe v0 v2) (coe du_any'63'_138 (coe v0) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Any.satisfiable
d_satisfiable_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_satisfiable_148 ~v0 ~v1 ~v2 ~v3 v4 = du_satisfiable_148 v4
du_satisfiable_148 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_satisfiable_148 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
             (coe C_here_46 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Any.any
d_any_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_any_154 v0 v1 v2 v3 v4 v5 = coe du_any'63'_138 v4 v5
