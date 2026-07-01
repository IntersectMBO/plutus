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

module MAlonzo.Code.Data.List.Relation.Binary.Lex where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Binary.Lex.Core
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.List.Relation.Binary.Lex._._≋_
d__'8779'__28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> [AgdaAny] -> [AgdaAny] -> ()
d__'8779'__28 = erased
-- Data.List.Relation.Binary.Lex._._<_
d__'60'__30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> [AgdaAny] -> [AgdaAny] -> ()
d__'60'__30 = erased
-- Data.List.Relation.Binary.Lex._.¬≤-this
d_'172''8804''45'this_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172''8804''45'this_40 = erased
-- Data.List.Relation.Binary.Lex._.¬≤-next
d_'172''8804''45'next_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172''8804''45'next_64 = erased
-- Data.List.Relation.Binary.Lex._.antisymmetric
d_antisymmetric_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_antisymmetric_78 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
  = du_antisymmetric_78 v10 v11
du_antisymmetric_78 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_antisymmetric_78 v0 v1 = coe du_as_90 (coe v0) (coe v1)
-- Data.List.Relation.Binary.Lex._._.as
d_as_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_as_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12 v13
        v14 v15
  = du_as_90 v12 v13 v14 v15
du_as_90 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_as_90 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_base_42 v4
        -> coe
             seq (coe v3)
             (coe
                MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56)
      MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60 v8
        -> coe
             seq (coe v3)
             (coe
                MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                erased)
      MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_next_74 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v1 of
                    (:) v12 v13
                      -> case coe v3 of
                           MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60 v18
                             -> coe
                                  MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                  erased
                           MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_next_74 v18 v19
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                  v8 (coe du_as_90 (coe v11) (coe v13) (coe v9) (coe v19))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Lex._.toSum
d_toSum_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_toSum_124 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_toSum_124 v11
du_toSum_124 ::
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_toSum_124 v0
  = case coe v0 of
      MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60 v5
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v5)
      MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_next_74 v5 v6
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Lex._.transitive
d_transitive_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32
d_transitive_132 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 v11 v12
  = du_transitive_132 v7 v8 v9 v10 v11 v12
du_transitive_132 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32
du_transitive_132 v0 v1 v2 v3 v4 v5
  = coe
      du_trans_144 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Data.List.Relation.Binary.Lex._._.trans
d_trans_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32
d_trans_144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 ~v10 ~v11 ~v12 v13
            v14 v15 v16 v17
  = du_trans_144 v7 v8 v9 v13 v14 v15 v16 v17
du_trans_144 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32
du_trans_144 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_base_42 v8
        -> case coe v7 of
             MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_base_42 v9
               -> coe v6
             MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_halt_48
               -> coe MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_halt_48
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_halt_48
        -> coe
             seq (coe v7)
             (coe MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_halt_48)
      MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60 v12
        -> case coe v3 of
             (:) v13 v14
               -> case coe v4 of
                    (:) v15 v16
                      -> case coe v7 of
                           MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60 v21
                             -> case coe v5 of
                                  (:) v22 v23
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60
                                         (coe v2 v13 v15 v22 v12 v21)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_next_74 v21 v22
                             -> case coe v5 of
                                  (:) v23 v24
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v1 v13 v15 v23
                                            v21 v12)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_next_74 v12 v13
        -> case coe v3 of
             (:) v14 v15
               -> case coe v4 of
                    (:) v16 v17
                      -> case coe v7 of
                           MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60 v22
                             -> case coe v5 of
                                  (:) v23 v24
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 v1 v23 v16 v14
                                            (coe
                                               MAlonzo.Code.Relation.Binary.Structures.d_sym_38 v0
                                               v14 v16 v12)
                                            v22)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_next_74 v22 v23
                             -> case coe v5 of
                                  (:) v24 v25
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_next_74
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Structures.d_trans_40 v0
                                            v14 v16 v24 v12 v22)
                                         (coe
                                            du_trans_144 (coe v0) (coe v1) (coe v2) (coe v15)
                                            (coe v17) (coe v25) (coe v13) (coe v23))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Lex._.respects₂
d_respects'8322'_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_respects'8322'_180 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_respects'8322'_180 v7 v8
du_respects'8322'_180 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_respects'8322'_180 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_resp'185'_200 (coe v0) (coe v2))
             (coe du_resp'178'_218 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Lex._._.resp¹
d_resp'185'_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32
d_resp'185'_200 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 ~v9 v10 v11 v12
                v13 v14
  = du_resp'185'_200 v7 v8 v10 v11 v12 v13 v14
du_resp'185'_200 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32
du_resp'185'_200 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe v6
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v11 v12
        -> case coe v3 of
             (:) v13 v14
               -> case coe v4 of
                    (:) v15 v16
                      -> case coe v6 of
                           MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_halt_48
                             -> coe MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_halt_48
                           MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60 v21
                             -> case coe v2 of
                                  (:) v22 v23
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60
                                         (coe v1 v22 v13 v15 v11 v21)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_next_74 v21 v22
                             -> case coe v2 of
                                  (:) v23 v24
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_next_74
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Structures.d_trans_40 v0
                                            v23 v13 v15 v21 v11)
                                         (coe
                                            du_resp'185'_200 (coe v0) (coe v1) (coe v24) (coe v14)
                                            (coe v16) (coe v12) (coe v22))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Lex._._.resp²
d_resp'178'_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32
d_resp'178'_218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 v9 v10 v11 v12
                v13 v14
  = du_resp'178'_218 v7 v9 v10 v11 v12 v13 v14
du_resp'178'_218 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32
du_resp'178'_218 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe v6
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v11 v12
        -> case coe v3 of
             (:) v13 v14
               -> case coe v4 of
                    (:) v15 v16
                      -> case coe v6 of
                           MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60 v21
                             -> case coe v2 of
                                  (:) v22 v23
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60
                                         (coe v1 v22 v13 v15 v11 v21)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_next_74 v21 v22
                             -> case coe v2 of
                                  (:) v23 v24
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_next_74
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Structures.d_trans_40 v0
                                            v15 v13 v23
                                            (coe
                                               MAlonzo.Code.Relation.Binary.Structures.d_sym_38 v0
                                               v13 v15 v11)
                                            v21)
                                         (coe
                                            du_resp'178'_218 (coe v0) (coe v1) (coe v24) (coe v14)
                                            (coe v16) (coe v12) (coe v22))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Lex._.[]<[]-⇔
d_'91''93''60''91''93''45''8660'_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_'91''93''60''91''93''45''8660'_234 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'91''93''60''91''93''45''8660'_234
du_'91''93''60''91''93''45''8660'_234 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
du_'91''93''60''91''93''45''8660'_234
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2474
      (coe MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_base_42)
      (coe du_'46'extendedlambda0_236)
-- Data.List.Relation.Binary.Lex._..extendedlambda0
d_'46'extendedlambda0_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 -> AgdaAny
d_'46'extendedlambda0_236 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'46'extendedlambda0_236 v7
du_'46'extendedlambda0_236 ::
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 -> AgdaAny
du_'46'extendedlambda0_236 v0
  = case coe v0 of
      MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_base_42 v1
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Lex._.∷<∷-⇔
d_'8759''60''8759''45''8660'_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_'8759''60''8759''45''8660'_248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10
  = du_'8759''60''8759''45''8660'_248
du_'8759''60''8759''45''8660'_248 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
du_'8759''60''8759''45''8660'_248
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2474
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
         (coe MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60)
         (coe
            MAlonzo.Code.Data.Product.Base.du_uncurry_244
            (coe MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_next_74)))
      (coe du_toSum_124)
-- Data.List.Relation.Binary.Lex._._.decidable
d_decidable_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decidable_260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 v11
  = du_decidable_260 v7 v8 v9 v10 v11
du_decidable_260 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_decidable_260 v0 v1 v2 v3 v4
  = case coe v3 of
      []
        -> case coe v4 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.du_map_18
                    (coe du_'91''93''60''91''93''45''8660'_234) v0
             (:) v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_halt_48))
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v5 v6
        -> case coe v4 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             (:) v7 v8
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.du_map_18
                    (coe du_'8759''60''8759''45''8660'_248)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
                       (coe v2 v5 v7)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                          (coe v1 v5 v7)
                          (coe
                             du_decidable_260 (coe v0) (coe v1) (coe v2) (coe v6) (coe v8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
