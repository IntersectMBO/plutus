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

module MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Relation.Binary.Construct.NonStrictToStrict._≉_
d__'8777'__20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d__'8777'__20 = erased
-- Relation.Binary.Construct.NonStrictToStrict._<_
d__'60'__26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d__'60'__26 = erased
-- Relation.Binary.Construct.NonStrictToStrict.<⇒≤
d_'60''8658''8804'_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_'60''8658''8804'_32 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'60''8658''8804'_32 v8
du_'60''8658''8804'_32 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_'60''8658''8804'_32 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Relation.Binary.Construct.NonStrictToStrict.<⇒≉
d_'60''8658''8777'_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8777'_38 = erased
-- Relation.Binary.Construct.NonStrictToStrict.≤∧≉⇒<
d_'8804''8743''8777''8658''60'_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8804''8743''8777''8658''60'_44 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_'8804''8743''8777''8658''60'_44
du_'8804''8743''8777''8658''60'_44 ::
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8804''8743''8777''8658''60'_44
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
-- Relation.Binary.Construct.NonStrictToStrict.<⇒≱
d_'60''8658''8817'_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8817'_50 = erased
-- Relation.Binary.Construct.NonStrictToStrict.≤⇒≯
d_'8804''8658''8815'_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8804''8658''8815'_64 = erased
-- Relation.Binary.Construct.NonStrictToStrict.≰⇒>
d_'8816''8658''62'_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8816''8658''62'_76 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_'8816''8658''62'_76 v6 v7 v8 v9 v10 v11
du_'8816''8658''62'_76 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8816''8658''62'_76 v0 v1 v2 v3 v4 v5
  = let v6 = coe v2 v3 v4 in
    coe
      (case coe v6 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
           -> coe
                MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                erased
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                (coe (\ v8 -> coe v5 (coe v1 v3 v4 (coe v0 v4 v3 v8))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Relation.Binary.Construct.NonStrictToStrict.≮⇒≥
d_'8814''8658''8805'_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_'8814''8658''8805'_126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10
                         v11 ~v12
  = du_'8814''8658''8805'_126 v6 v7 v8 v9 v10 v11
du_'8814''8658''8805'_126 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8814''8658''8805'_126 v0 v1 v2 v3 v4 v5
  = let v6 = coe v1 v4 v5 in
    coe
      (let v7 = coe v3 v5 v4 in
       coe
         (case coe v6 of
            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
              -> let v10
                       = case coe v7 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10 -> coe v10
                           _ -> MAlonzo.RTE.mazUnreachableError in
                 coe
                   (if coe v8
                      then let v11
                                 = case coe v7 of
                                     MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11 -> coe v11
                                     _ -> MAlonzo.RTE.mazUnreachableError in
                           coe
                             (case coe v9 of
                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                  -> coe v2 v5 v4 (coe v0 v4 v5 v12)
                                _ -> coe v11)
                      else (case coe v7 of
                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11 -> coe v11
                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                -> case coe v9 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                       -> coe
                                            MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                            erased
                                     _ -> coe v10
                              _ -> MAlonzo.RTE.mazUnreachableError))
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Relation.Binary.Construct.NonStrictToStrict.<-irrefl
d_'60''45'irrefl_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irrefl_196 = erased
-- Relation.Binary.Construct.NonStrictToStrict.<-trans
d_'60''45'trans_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'trans_202 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_'60''45'trans_202 v6 v7 v8 v9 v10 v11
du_'60''45'trans_202 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'trans_202 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.d_trans_90
                       (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v0))
                       v1 v2 v3 v6 v8)
                    (coe
                       (\ v10 ->
                          coe
                            v7
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_antisym_258 v0 v1 v2 v6
                               (coe
                                  MAlonzo.Code.Relation.Binary.Structures.d_trans_90
                                  (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                                     (coe v0))
                                  v2 v3 v1 v8
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
                                     (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                                        (coe v0))
                                     v3 v1
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                                        (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                                           (coe
                                              MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                                              (coe v0)))
                                        v1 v3 v10))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.NonStrictToStrict.<-≤-trans
d_'60''45''8804''45'trans_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45''8804''45'trans_256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
                              v10 v11 v12 v13 v14
  = du_'60''45''8804''45'trans_256 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_'60''45''8804''45'trans_256 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45''8804''45'trans_256 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1 v4 v5 v6 v9 v8)
             (coe
                (\ v11 ->
                   coe v10 (coe v2 v4 v5 v9 (coe v3 v5 v6 v4 (coe v0 v4 v6 v11) v8))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.NonStrictToStrict.≤-<-trans
d_'8804''45''60''45'trans_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8804''45''60''45'trans_274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
                              v10 v11 v12 v13
  = du_'8804''45''60''45'trans_274 v6 v7 v8 v9 v10 v11 v12 v13
du_'8804''45''60''45'trans_274 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8804''45''60''45'trans_274 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 v3 v4 v5 v6 v8)
             (coe (\ v10 -> coe v9 (coe v1 v4 v5 v8 (coe v2 v4 v3 v5 v10 v6))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.NonStrictToStrict.<-asym
d_'60''45'asym_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'asym_290 = erased
-- Relation.Binary.Construct.NonStrictToStrict.<-respˡ-≈
d_'60''45'resp'737''45''8776'_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'737''45''8776'_300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
                                  v9 v10 v11 v12
  = du_'60''45'resp'737''45''8776'_300 v6 v7 v8 v9 v10 v11 v12
du_'60''45'resp'737''45''8776'_300 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'737''45''8776'_300 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1 v2 v3 v4 v5 v7)
             (coe (\ v9 -> coe v8 (coe v0 v3 v4 v2 v5 v9)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.NonStrictToStrict.<-respʳ-≈
d_'60''45'resp'691''45''8776'_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'691''45''8776'_312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
                                  v9 v10 v11 v12 v13
  = du_'60''45'resp'691''45''8776'_312 v6 v7 v8 v9 v10 v11 v12 v13
du_'60''45'resp'691''45''8776'_312 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'691''45''8776'_312 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2 v3 v4 v5 v6 v8)
             (coe (\ v10 -> coe v9 (coe v1 v3 v5 v4 v10 (coe v0 v4 v5 v6))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.NonStrictToStrict.<-resp-≈
d_'60''45'resp'45''8776'_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8776'_328 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_'60''45'resp'45''8776'_328 v6 v7
du_'60''45'resp'45''8776'_328 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'resp'45''8776'_328 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_'60''45'resp'691''45''8776'_312
                (coe MAlonzo.Code.Relation.Binary.Structures.d_sym_38 (coe v0))
                (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_40 (coe v0))
                (coe v2))
             (coe
                du_'60''45'resp'737''45''8776'_300
                (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_40 (coe v0))
                (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.NonStrictToStrict.<-trichotomous
d_'60''45'trichotomous_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''45'trichotomous_352 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 v9
                           v10 v11
  = du_'60''45'trichotomous_352 v7 v9 v10 v11
du_'60''45'trichotomous_352 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_'60''45'trichotomous_352 v0 v1 v2 v3
  = let v4 = coe v0 v2 v3 in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                         -> coe MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v7
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v6)
                       (let v7 = coe v1 v2 v3 in
                        coe
                          (case coe v7 of
                             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                               -> coe
                                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) erased)
                             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                               -> coe
                                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) erased)
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Relation.Binary.Construct.NonStrictToStrict.<-decidable
d_'60''45'decidable_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'60''45'decidable_434 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_'60''45'decidable_434 v6 v7 v8 v9
du_'60''45'decidable_434 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'60''45'decidable_434 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
      (coe v1 v2 v3)
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_76
         (coe v0 v2 v3))
-- Relation.Binary.Construct.NonStrictToStrict.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_'60''45'isStrictPartialOrder_444 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'isStrictPartialOrder_444 v6
du_'60''45'isStrictPartialOrder_444 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
du_'60''45'isStrictPartialOrder_444 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_412
      (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v0)))
      (coe du_'60''45'trans_202 (coe v0))
      (coe
         du_'60''45'resp'45''8776'_328
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v0)))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v0))))
-- Relation.Binary.Construct.NonStrictToStrict.<-isDecStrictPartialOrder
d_'60''45'isDecStrictPartialOrder_490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418
d_'60''45'isDecStrictPartialOrder_490 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'isDecStrictPartialOrder_490 v6
du_'60''45'isDecStrictPartialOrder_490 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418
du_'60''45'isDecStrictPartialOrder_490 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_482
      (coe
         du_'60''45'isStrictPartialOrder_444
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_310
            (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d__'8799'__312 (coe v0))
      (coe
         du_'60''45'decidable_434
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__312 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__314
            (coe v0)))
-- Relation.Binary.Construct.NonStrictToStrict.<-isStrictTotalOrder₁
d_'60''45'isStrictTotalOrder'8321'_550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
d_'60''45'isStrictTotalOrder'8321'_550 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
                                       v7
  = du_'60''45'isStrictTotalOrder'8321'_550 v6 v7
du_'60''45'isStrictTotalOrder'8321'_550 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
du_'60''45'isStrictTotalOrder'8321'_550 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_680
      (coe
         du_'60''45'isStrictPartialOrder_444
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
            (coe v1)))
      (coe
         du_'60''45'trichotomous_352 (coe v0)
         (coe MAlonzo.Code.Relation.Binary.Structures.d_total_498 (coe v1)))
-- Relation.Binary.Construct.NonStrictToStrict.<-isStrictTotalOrder₂
d_'60''45'isStrictTotalOrder'8322'_604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
d_'60''45'isStrictTotalOrder'8322'_604 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'isStrictTotalOrder'8322'_604 v6
du_'60''45'isStrictTotalOrder'8322'_604 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
du_'60''45'isStrictTotalOrder'8322'_604 v0
  = coe
      du_'60''45'isStrictTotalOrder'8321'_550
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d__'8799'__558 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_556
         (coe v0))
