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

module MAlonzo.Code.Data.List.Relation.Unary.All.Properties.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.List.Relation.Unary.All.Properties.Core.¬Any⇒All¬
d_'172'Any'8658'All'172'_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_'172'Any'8658'All'172'_38 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'172'Any'8658'All'172'_38 v4 v5
du_'172'Any'8658'All'172'_38 ::
  [AgdaAny] ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_'172'Any'8658'All'172'_38 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (\ v4 ->
                coe
                  v1 (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v4))
             (coe du_'172'Any'8658'All'172'_38 (coe v3) erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All.Properties.Core.All¬⇒¬Any
d_All'172''8658''172'Any_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_All'172''8658''172'Any_50 = erased
-- Data.List.Relation.Unary.All.Properties.Core.¬All⇒Any¬
d_'172'All'8658'Any'172'_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  (MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'172'All'8658'Any'172'_62 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6
  = du_'172'All'8658'Any'172'_62 v4 v5
du_'172'All'8658'Any'172'_62 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'172'All'8658'Any'172'_62 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      (:) v2 v3
        -> let v4 = coe v0 v2 in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe
                              MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                              (coe du_'172'All'8658'Any'172'_62 (coe v0) (coe v3))
                       else coe
                              MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                              (coe MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38 (coe v6))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All.Properties.Core.Any¬⇒¬All
d_Any'172''8658''172'All_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_Any'172''8658''172'All_102 = erased
-- Data.List.Relation.Unary.All.Properties.Core.¬Any↠All¬
d_'172'Any'8608'All'172'_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] -> MAlonzo.Code.Function.Bundles.T_Surjection_918
d_'172'Any'8608'All'172'_110 ~v0 ~v1 ~v2 ~v3 v4
  = du_'172'Any'8608'All'172'_110 v4
du_'172'Any'8608'All'172'_110 ::
  [AgdaAny] -> MAlonzo.Code.Function.Bundles.T_Surjection_918
du_'172'Any'8608'All'172'_110 v0
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8608''8347'_2536
      (coe du_'172'Any'8658'All'172'_38 (coe v0))
      (coe
         (\ v1 ->
            coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Data.List.Relation.Unary.All.Properties.Core._.to∘from
d_to'8728'from_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_to'8728'from_120 = erased
-- Data.List.Relation.Unary.All.Properties.Core.Any¬⇔¬All
d_Any'172''8660''172'All_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_Any'172''8660''172'All_156 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_Any'172''8660''172'All_156 v4 v5
du_Any'172''8660''172'All_156 ::
  [AgdaAny] ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
du_Any'172''8660''172'All_156 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2474 erased
      (\ v2 -> coe du_'172'All'8658'Any'172'_62 (coe v1) (coe v0))
-- Data.List.Relation.Unary.All.Properties.Core._.All-swap
d_All'45'swap_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_All'45'swap_198 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_All'45'swap_198 v6 v7 v8
du_All'45'swap_198 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_All'45'swap_198 v0 v1 v2
  = case coe v1 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.du_universal_520
                    (coe (\ v5 -> v2)) (coe v1)
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> case coe v0 of
                    (:) v9 v10
                      -> case coe v7 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v13 v14
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v13
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
                                        (coe
                                           (\ v15 ->
                                              coe
                                                MAlonzo.Code.Data.List.Relation.Unary.All.du_head_114))
                                        (coe v10) (coe v8)))
                                  (coe
                                     du_All'45'swap_198 (coe v0) (coe v4)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v14
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
                                           (coe
                                              (\ v15 ->
                                                 coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.All.du_tail_116))
                                           (coe v10) (coe v8))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All.Properties.Core._..generalizedField-P.a
d_'46'generalizedField'45'P'46'a_28211 ::
  T_GeneralizeTel_28219 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'P'46'a_28211 v0
  = case coe v0 of
      C_mkGeneralizeTel_28221 v1 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All.Properties.Core._..generalizedField-P.A
d_'46'generalizedField'45'P'46'A_28213 ::
  T_GeneralizeTel_28219 -> ()
d_'46'generalizedField'45'P'46'A_28213 = erased
-- Data.List.Relation.Unary.All.Properties.Core._..generalizedField-P.p
d_'46'generalizedField'45'P'46'p_28215 ::
  T_GeneralizeTel_28219 -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'46'generalizedField'45'P'46'p_28215 v0
  = case coe v0 of
      C_mkGeneralizeTel_28221 v1 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.All.Properties.Core._..generalizedField-P
d_'46'generalizedField'45'P_28217 ::
  T_GeneralizeTel_28219 -> AgdaAny -> ()
d_'46'generalizedField'45'P_28217 = erased
-- Data.List.Relation.Unary.All.Properties.Core._.GeneralizeTel
d_GeneralizeTel_28219 a0 a1 a2 a3 a4 = ()
data T_GeneralizeTel_28219
  = C_mkGeneralizeTel_28221 MAlonzo.Code.Agda.Primitive.T_Level_18
                            MAlonzo.Code.Agda.Primitive.T_Level_18
