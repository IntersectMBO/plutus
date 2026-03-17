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

module MAlonzo.Code.Relation.Binary.Construct.StrictToNonStrict where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Relation.Binary.Construct.StrictToNonStrict._≤_
d__'8804'__20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d__'8804'__20 = erased
-- Relation.Binary.Construct.StrictToNonStrict.<⇒≤
d_'60''8658''8804'_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'60''8658''8804'_26 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_'60''8658''8804'_26
du_'60''8658''8804'_26 ::
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'60''8658''8804'_26
  = coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
-- Relation.Binary.Construct.StrictToNonStrict.reflexive
d_reflexive_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_reflexive_28 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_reflexive_28
du_reflexive_28 ::
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_reflexive_28 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
-- Relation.Binary.Construct.StrictToNonStrict.antisym
d_antisym_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_antisym_30 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 v10
  = du_antisym_30 v6 v9 v10
du_antisym_30 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_antisym_30 v0 v1 v2 = coe du_as_54 (coe v0) (coe v1) (coe v2)
-- Relation.Binary.Construct.StrictToNonStrict._.as
d_as_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_as_54 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 v11 v12 v13 v14
  = du_as_54 v6 v11 v12 v13 v14
du_as_54 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_as_54 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                    erased
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe MAlonzo.Code.Relation.Binary.Structures.d_sym_36 v0 v2 v1 v6
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.StrictToNonStrict.trans
d_trans_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_trans_64 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_trans_64 v6 v7 v8 v9 v10 v11
du_trans_64 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_trans_64 v0 v1 v2 v3 v4 v5
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> coe
             du_tr_90 (coe v0) (coe v6) (coe v7) (coe v2) (coe v3) (coe v4)
             (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.StrictToNonStrict._.tr
d_tr_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_tr_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 ~v11 ~v12 v13 v14
        v15 v16 v17
  = du_tr_90 v6 v7 v8 v9 v13 v14 v15 v16 v17
du_tr_90 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_tr_90 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
        -> case coe v8 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v3 v4 v5 v6 v9 v10)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v1 v4 v5 v6 v10 v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
        -> case coe v8 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe
                       v2 v6 v5 v4
                       (coe MAlonzo.Code.Relation.Binary.Structures.d_sym_36 v0 v4 v5 v9)
                       v10)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.d_trans_38 v0 v4 v5 v6 v9
                       v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.StrictToNonStrict.<-≤-trans
d_'60''45''8804''45'trans_108 ::
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
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_'60''45''8804''45'trans_108 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
                              v10 v11 v12
  = du_'60''45''8804''45'trans_108 v6 v7 v8 v9 v10 v11 v12
du_'60''45''8804''45'trans_108 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_'60''45''8804''45'trans_108 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
        -> coe v0 v2 v3 v4 v5 v7
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe v1 v2 v3 v4 v7 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.StrictToNonStrict.≤-<-trans
d_'8804''45''60''45'trans_126 ::
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
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> AgdaAny
d_'8804''45''60''45'trans_126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
                              v10 v11 v12 v13
  = du_'8804''45''60''45'trans_126 v6 v7 v8 v9 v10 v11 v12 v13
du_'8804''45''60''45'trans_126 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> AgdaAny
du_'8804''45''60''45'trans_126 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
        -> coe v1 v3 v4 v5 v8 v7
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> coe v2 v5 v4 v3 (coe v0 v3 v4 v8) v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.StrictToNonStrict.≤-respʳ-≈
d_'8804''45'resp'691''45''8776'_148 ::
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
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45'resp'691''45''8776'_148 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
                                    v8 v9 v10 v11 v12
  = du_'8804''45'resp'691''45''8776'_148 v6 v7 v8 v9 v10 v11 v12
du_'8804''45'resp'691''45''8776'_148 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8804''45'resp'691''45''8776'_148 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v1 v2 v3 v4 v5 v7)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v0 v2 v3 v4 v7 v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.StrictToNonStrict.≤-respˡ-≈
d_'8804''45'resp'737''45''8776'_166 ::
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
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45'resp'737''45''8776'_166 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
                                    v8 v9 v10 v11 v12 v13
  = du_'8804''45'resp'737''45''8776'_166 v6 v7 v8 v9 v10 v11 v12 v13
du_'8804''45'resp'737''45''8776'_166 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8804''45'resp'737''45''8776'_166 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v2 v3 v4 v5 v6 v8)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe v1 v5 v4 v3 (coe v0 v4 v5 v6) v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.StrictToNonStrict.≤-resp-≈
d_'8804''45'resp'45''8776'_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8804''45'resp'45''8776'_188 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_'8804''45'resp'45''8776'_188 v6 v7
du_'8804''45'resp'45''8776'_188 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8804''45'resp'45''8776'_188 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_'8804''45'resp'691''45''8776'_148
                (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_38 (coe v0))
                (coe v2))
             (coe
                du_'8804''45'resp'737''45''8776'_166
                (coe MAlonzo.Code.Relation.Binary.Structures.d_sym_36 (coe v0))
                (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_38 (coe v0))
                (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.StrictToNonStrict.total
d_total_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_total_212 v6 v7 v8
du_total_212 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_total_212 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v4
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v4))
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v5
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v5))
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v6
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v6))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Relation.Binary.Construct.StrictToNonStrict.decidable
d_decidable_260 ::
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
d_decidable_260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_decidable_260 v6 v7 v8 v9
du_decidable_260 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_decidable_260 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
      (coe v1 v2 v3) (coe v0 v2 v3)
-- Relation.Binary.Construct.StrictToNonStrict.decidable′
d_decidable'8242'_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decidable'8242'_270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_decidable'8242'_270 v6 v7 v8
du_decidable'8242'_270 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_decidable'8242'_270 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v4
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe
                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                   (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v4)))
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v5
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe
                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                   (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v5)))
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v6
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Relation.Binary.Construct.StrictToNonStrict.isPreorder₁
d_isPreorder'8321'_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder'8321'_308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPreorder'8321'_308 v6
du_isPreorder'8321'_308 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_isPreorder'8321'_308 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe v0))
      (\ v1 v2 -> coe du_reflexive_28)
      (coe
         du_trans_64
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
            (coe v0))
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_84 (coe v0)))
-- Relation.Binary.Construct.StrictToNonStrict.isPreorder₂
d_isPreorder'8322'_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_354 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder'8322'_350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPreorder'8322'_350 v6
du_isPreorder'8322'_350 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_354 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_isPreorder'8322'_350 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_366
         (coe v0))
      (\ v1 v2 -> coe du_reflexive_28)
      (coe
         du_trans_64
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_366
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_372
            (coe v0))
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_370 (coe v0)))
-- Relation.Binary.Construct.StrictToNonStrict.isPartialOrder
d_isPartialOrder_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_354 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_236
d_isPartialOrder_386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialOrder_386 v6
du_isPartialOrder_386 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_354 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_236
du_isPartialOrder_386 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPartialOrder'46'constructor_11935
      (coe du_isPreorder'8322'_350 (coe v0))
      (coe
         du_antisym_30
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_366
            (coe v0)))
-- Relation.Binary.Construct.StrictToNonStrict.isTotalOrder
d_isTotalOrder_422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_600 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_468
d_isTotalOrder_422 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isTotalOrder_422 v6
du_isTotalOrder_422 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_600 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_468
du_isTotalOrder_422 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalOrder'46'constructor_22821
      (coe
         du_isPartialOrder_386
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_608
            (coe v0)))
      (coe
         du_total_212
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_compare_610 (coe v0)))
-- Relation.Binary.Construct.StrictToNonStrict.isDecTotalOrder
d_isDecTotalOrder_476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_600 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_524
d_isDecTotalOrder_476 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecTotalOrder_476 v6
du_isDecTotalOrder_476 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_600 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_524
du_isDecTotalOrder_476 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecTotalOrder'46'constructor_24961
      (coe du_isTotalOrder_422 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du__'8799'__628 (coe v0))
      (coe
         du_decidable'8242'_270
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_compare_610 (coe v0)))
-- Relation.Binary.Construct.StrictToNonStrict.decidable'
d_decidable''_530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decidable''_530 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_decidable''_530
du_decidable''_530 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_decidable''_530 = coe du_decidable'8242'_270
