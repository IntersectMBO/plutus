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

module MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Relation.Binary.Construct.Closure.Reflexive.Properties._.=[]⇒
d_'61''91''93''8658'_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30
d_'61''91''93''8658'_44 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
                        v11 v12
  = du_'61''91''93''8658'_44 v9 v10 v11 v12
du_'61''91''93''8658'_44 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30
du_'61''91''93''8658'_44 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_refl_36
        -> coe
             MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_refl_36
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44 v6
        -> coe
             MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44
             (coe v0 v1 v2 v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Closure.Reflexive.Properties._._~ᵒ_
d__'126''7506'__62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d__'126''7506'__62 = erased
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.fromSum
d_fromSum_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30
d_fromSum_68 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_fromSum_68 v6
du_fromSum_68 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30
du_fromSum_68 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe
             MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_refl_36
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe
             MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44
             v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.toSum
d_toSum_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_toSum_76 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_toSum_76 v6
du_toSum_76 ::
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_toSum_76 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_refl_36
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44 v3
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.⊎⇔Refl
d_'8846''8660'Refl_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_'8846''8660'Refl_84 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8846''8660'Refl_84
du_'8846''8660'Refl_84 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
du_'8846''8660'Refl_84
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2474 (coe du_fromSum_68)
      (coe du_toSum_76)
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.sym
d_sym_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30
d_sym_86 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_sym_86 v4 v5 v6 v7
du_sym_86 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30
du_sym_86 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_refl_36
        -> coe
             MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_refl_36
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44 v6
        -> coe
             MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44
             (coe v0 v1 v2 v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.trans
d_trans_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30
d_trans_94 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_trans_94 v4 v5 v6 v7 v8 v9
du_trans_94 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30
du_trans_94 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_refl_36
        -> case coe v5 of
             MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_refl_36
               -> coe
                    MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_refl_36
             MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44 v9
               -> coe
                    MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44
                    v9
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44 v8
        -> case coe v5 of
             MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_refl_36
               -> coe
                    MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44
                    v8
             MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44 v11
               -> coe
                    MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44
                    (coe v0 v1 v2 v3 v8 v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.antisym
d_antisym_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  AgdaAny
d_antisym_114 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 v10 v11
  = du_antisym_114 v6 v8 v10 v11
du_antisym_114 ::
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  AgdaAny
du_antisym_114 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_refl_36
        -> coe v0 v1
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44 v6
        -> case coe v3 of
             MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_refl_36
               -> coe v0 v1
             MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44 v9
               -> coe
                    MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.total
d_total_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_140 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_total_140 v4 v5 v6
du_total_140 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_total_140 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v4
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe
                   MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44
                   v4)
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v5
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe
                   MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_refl_36)
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v6
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe
                   MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44
                   v6)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.dec
d_dec_174 ::
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
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_dec_174 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_dec_174 v4 v5 v6 v7
du_dec_174 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_dec_174 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.du_map_18
      (coe du_'8846''8660'Refl_84)
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
         (coe v0 v2 v3) (coe v1 v2 v3))
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.decidable
d_decidable_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decidable_184 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_decidable_184 v4 v5 v6
du_decidable_184 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_decidable_184 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v4
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe
                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                   (coe
                      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44
                      v4))
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v5
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe
                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                   (coe
                      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_refl_36))
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v6
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Relation.Binary.Construct.Closure.Reflexive.Properties._..extendedlambda0
d_'46'extendedlambda0_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'46'extendedlambda0_220 = erased
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.respˡ
d_resp'737'_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  AgdaAny -> AgdaAny
d_resp'737'_226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 v12
  = du_resp'737'_226 v8 v9 v10 v11 v12
du_resp'737'_226 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  AgdaAny -> AgdaAny
du_resp'737'_226 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_refl_36
        -> coe (\ v6 -> v6)
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44 v7
        -> coe v0 v1 v2 v3 v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.respʳ
d_resp'691'_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  AgdaAny -> AgdaAny
d_resp'691'_234 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_resp'691'_234
du_resp'691'_234 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  AgdaAny -> AgdaAny
du_resp'691'_234 = coe du_resp'737'_226
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.resp
d_resp_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  AgdaAny -> AgdaAny
d_resp_250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_resp_250 v6 v7 v8 v9
du_resp_250 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  AgdaAny -> AgdaAny
du_resp_250 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_refl_36
        -> coe (\ v5 -> v5)
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_'91'_'93'_44 v6
        -> coe v0 v1 v2 v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.resp₂
d_resp'8322'_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_resp'8322'_270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_resp'8322'_270
du_resp'8322'_270 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_resp'8322'_270
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128 (coe du_resp'737'_226)
      (coe (\ v0 -> coe du_resp'691'_234))
-- Relation.Binary.Construct.Closure.Reflexive.Properties._._~ᵒ_
d__'126''7506'__282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d__'126''7506'__282 = erased
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.isPreorder
d_isPreorder_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_284 ~v0 ~v1 ~v2 ~v3 v4 = du_isPreorder_284 v4
du_isPreorder_284 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_isPreorder_284 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v1 v2 v3 -> coe du_'46'extendedlambda0_288)
      (coe du_trans_94 (coe v0))
-- Relation.Binary.Construct.Closure.Reflexive.Properties._..extendedlambda0
d_'46'extendedlambda0_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30
d_'46'extendedlambda0_288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_'46'extendedlambda0_288
du_'46'extendedlambda0_288 ::
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30
du_'46'extendedlambda0_288
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.C_refl_36
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.isPartialOrder
d_isPartialOrder_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_290 ~v0 ~v1 ~v2 ~v3 v4 = du_isPartialOrder_290 v4
du_isPartialOrder_290 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_isPartialOrder_290 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe
         du_isPreorder_284
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_386 (coe v0)))
      (\ v1 v2 v3 v4 -> coe du_antisym_114 erased v1 v3 v4)
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.isDecPartialOrder
d_isDecPartialOrder_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300
d_isDecPartialOrder_326 ~v0 ~v1 ~v2 ~v3 v4
  = du_isDecPartialOrder_326 v4
du_isDecPartialOrder_326 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300
du_isDecPartialOrder_326 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_364
      (coe
         du_isPartialOrder_290
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_428
            (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d__'8799'__430 (coe v0))
      (coe
         du_dec_174
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__430 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'60''63'__432 (coe v0)))
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.isTotalOrder
d_isTotalOrder_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
d_isTotalOrder_374 ~v0 ~v1 ~v2 ~v3 v4 = du_isTotalOrder_374 v4
du_isTotalOrder_374 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
du_isTotalOrder_374 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_540
      (coe
         du_isPartialOrder_290
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
            (coe v0)))
      (coe
         du_total_140
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_compare_634 (coe v0)))
-- Relation.Binary.Construct.Closure.Reflexive.Properties._.isDecTotalOrder
d_isDecTotalOrder_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
d_isDecTotalOrder_428 ~v0 ~v1 ~v2 ~v3 v4
  = du_isDecTotalOrder_428 v4
du_isDecTotalOrder_428 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
du_isDecTotalOrder_428 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_618
      (coe du_isTotalOrder_374 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du__'8799'__652 (coe v0))
      (coe
         du_dec_174
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du__'8799'__652 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du__'60''63'__654
            (coe v0)))
