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

module MAlonzo.Code.Data.List.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Morphism.Structures
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Maybe.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Divisibility
import qualified MAlonzo.Code.Data.Nat.Divisibility.Core
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.These.Base
import qualified MAlonzo.Code.Relation.Binary.Morphism.Structures
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.List.Properties.∷-injective
d_'8759''45'injective_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8759''45'injective_48 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8759''45'injective_48
du_'8759''45'injective_48 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8759''45'injective_48
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.List.Properties.∷-injectiveˡ
d_'8759''45'injective'737'_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8759''45'injective'737'_50 = erased
-- Data.List.Properties.∷-injectiveʳ
d_'8759''45'injective'691'_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8759''45'injective'691'_52 = erased
-- Data.List.Properties.∷-dec
d_'8759''45'dec_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8759''45'dec_54 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_'8759''45'dec_54 v6 v7
du_'8759''45'dec_54 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8759''45'dec_54 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      (coe MAlonzo.Code.Data.Product.Base.du_uncurry_244 erased)
      (\ v2 -> coe du_'8759''45'injective_48)
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
         (coe v0) (coe v1))
-- Data.List.Properties.≡-dec
d_'8801''45'dec_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8801''45'dec_60 ~v0 ~v1 v2 v3 v4 = du_'8801''45'dec_60 v2 v3 v4
du_'8801''45'dec_60 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8801''45'dec_60 v0 v1 v2
  = case coe v1 of
      []
        -> case coe v2 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
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
                    du_'8759''45'dec_54 (coe v0 v3 v5)
                    (coe du_'8801''45'dec_60 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Properties.map-id
d_map'45'id_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'id_86 = erased
-- Data.List.Properties.map-id-local
d_map'45'id'45'local_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'id'45'local_100 = erased
-- Data.List.Properties.map-++
d_map'45''43''43'_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45''43''43'_112 = erased
-- Data.List.Properties.map-cong
d_map'45'cong_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'cong_132 = erased
-- Data.List.Properties.map-cong-local
d_map'45'cong'45'local_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'cong'45'local_150 = erased
-- Data.List.Properties.length-map
d_length'45'map_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'map_160 = erased
-- Data.List.Properties.map-∘
d_map'45''8728'_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45''8728'_174 = erased
-- Data.List.Properties.map-injective
d_map'45'injective_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'injective_184 = erased
-- Data.List.Properties.length-++
d_length'45''43''43'_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45''43''43'_210 = erased
-- Data.List.Properties._._.Associative
d_Associative_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> ([AgdaAny] -> [AgdaAny] -> [AgdaAny]) -> ()
d_Associative_248 = erased
-- Data.List.Properties._._.Cancellative
d_Cancellative_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> ([AgdaAny] -> [AgdaAny] -> [AgdaAny]) -> ()
d_Cancellative_250 = erased
-- Data.List.Properties._._.Conical
d_Conical_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> ([AgdaAny] -> [AgdaAny] -> [AgdaAny]) -> ()
d_Conical_258 = erased
-- Data.List.Properties._._.Identity
d_Identity_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> ([AgdaAny] -> [AgdaAny] -> [AgdaAny]) -> ()
d_Identity_268 = erased
-- Data.List.Properties._._.LeftCancellative
d_LeftCancellative_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> ([AgdaAny] -> [AgdaAny] -> [AgdaAny]) -> ()
d_LeftCancellative_282 = erased
-- Data.List.Properties._._.LeftIdentity
d_LeftIdentity_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> ([AgdaAny] -> [AgdaAny] -> [AgdaAny]) -> ()
d_LeftIdentity_294 = erased
-- Data.List.Properties._._.RightCancellative
d_RightCancellative_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> ([AgdaAny] -> [AgdaAny] -> [AgdaAny]) -> ()
d_RightCancellative_312 = erased
-- Data.List.Properties._._.RightIdentity
d_RightIdentity_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> ([AgdaAny] -> [AgdaAny] -> [AgdaAny]) -> ()
d_RightIdentity_324 = erased
-- Data.List.Properties._.++-assoc
d_'43''43''45'assoc_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'assoc_354 = erased
-- Data.List.Properties._.++-identityˡ
d_'43''43''45'identity'737'_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'identity'737'_370 = erased
-- Data.List.Properties._.++-identityʳ
d_'43''43''45'identity'691'_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'identity'691'_374 = erased
-- Data.List.Properties._.++-identity
d_'43''43''45'identity_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''43''45'identity_382 ~v0 ~v1 = du_'43''43''45'identity_382
du_'43''43''45'identity_382 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'43''43''45'identity_382
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.List.Properties._.++-identityʳ-unique
d_'43''43''45'identity'691''45'unique_388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'identity'691''45'unique_388 = erased
-- Data.List.Properties._.++-identityˡ-unique
d_'43''43''45'identity'737''45'unique_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'identity'737''45'unique_400 = erased
-- Data.List.Properties._.++-cancelˡ
d_'43''43''45'cancel'737'_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'cancel'737'_432 = erased
-- Data.List.Properties._.++-cancelʳ
d_'43''43''45'cancel'691'_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'cancel'691'_442 = erased
-- Data.List.Properties._.++-cancel
d_'43''43''45'cancel_470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''43''45'cancel_470 ~v0 ~v1 = du_'43''43''45'cancel_470
du_'43''43''45'cancel_470 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'43''43''45'cancel_470
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.List.Properties._.++-conicalˡ
d_'43''43''45'conical'737'_476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'conical'737'_476 = erased
-- Data.List.Properties._.++-conicalʳ
d_'43''43''45'conical'691'_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'conical'691'_482 = erased
-- Data.List.Properties._.++-conical
d_'43''43''45'conical_484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''43''45'conical_484 ~v0 ~v1 = du_'43''43''45'conical_484
du_'43''43''45'conical_484 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'43''43''45'conical_484
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.List.Properties.length-++-sucˡ
d_length'45''43''43''45'suc'737'_492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45''43''43''45'suc'737'_492 = erased
-- Data.List.Properties.length-++-sucʳ
d_length'45''43''43''45'suc'691'_500 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45''43''43''45'suc'691'_500 = erased
-- Data.List.Properties.length-++-comm
d_length'45''43''43''45'comm_512 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45''43''43''45'comm_512 = erased
-- Data.List.Properties.length-++-≤ˡ
d_length'45''43''43''45''8804''737'_532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] -> [AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_length'45''43''43''45''8804''737'_532 ~v0 ~v1 v2 ~v3
  = du_length'45''43''43''45''8804''737'_532 v2
du_length'45''43''43''45''8804''737'_532 ::
  [AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_length'45''43''43''45''8804''737'_532 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe du_length'45''43''43''45''8804''737'_532 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Properties.length-++-≤ʳ
d_length'45''43''43''45''8804''691'_542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] -> [AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_length'45''43''43''45''8804''691'_542 ~v0 ~v1 v2 v3
  = du_length'45''43''43''45''8804''691'_542 v2 v3
du_length'45''43''43''45''8804''691'_542 ::
  [AgdaAny] -> [AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_length'45''43''43''45''8804''691'_542 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
      (coe du_length'45''43''43''45''8804''737'_532 (coe v0))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
         (coe
            MAlonzo.Code.Data.List.Base.du_length_268
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v1))))
-- Data.List.Properties._._.IsMagma
d_IsMagma_646 a0 a1 a2 = ()
-- Data.List.Properties._._.IsMonoid
d_IsMonoid_658 a0 a1 a2 a3 = ()
-- Data.List.Properties._._.IsSemigroup
d_IsSemigroup_702 a0 a1 a2 = ()
-- Data.List.Properties._._.IsMagma.isEquivalence
d_isEquivalence_1998 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1998 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v0)
-- Data.List.Properties._._.IsMagma.∙-cong
d_'8729''45'cong_2012 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2012 = erased
-- Data.List.Properties._._.IsMonoid.identity
d_identity_2108 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2108 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_724 (coe v0)
-- Data.List.Properties._._.IsMonoid.isSemigroup
d_isSemigroup_2120 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_2120 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0)
-- Data.List.Properties._._.IsSemigroup.assoc
d_assoc_2854 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2854 = erased
-- Data.List.Properties._._.IsSemigroup.isMagma
d_isMagma_2858 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2858 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0)
-- Data.List.Properties._.++-isMagma
d_'43''43''45'isMagma_3178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'43''43''45'isMagma_3178 ~v0 ~v1 = du_'43''43''45'isMagma_3178
du_'43''43''45'isMagma_3178 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'43''43''45'isMagma_3178
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_210
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased
-- Data.List.Properties._.++-isSemigroup
d_'43''43''45'isSemigroup_3180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'43''43''45'isSemigroup_3180 ~v0 ~v1
  = du_'43''43''45'isSemigroup_3180
du_'43''43''45'isSemigroup_3180 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'43''43''45'isSemigroup_3180
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_522
      (coe du_'43''43''45'isMagma_3178) erased
-- Data.List.Properties._.++-isMonoid
d_'43''43''45'isMonoid_3182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'43''43''45'isMonoid_3182 ~v0 ~v1 = du_'43''43''45'isMonoid_3182
du_'43''43''45'isMonoid_3182 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'43''43''45'isMonoid_3182
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_758
      (coe du_'43''43''45'isSemigroup_3180)
      (coe du_'43''43''45'identity_382)
-- Data.List.Properties._.++-semigroup
d_'43''43''45'semigroup_3192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'43''43''45'semigroup_3192 ~v0 ~v1
  = du_'43''43''45'semigroup_3192
du_'43''43''45'semigroup_3192 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
du_'43''43''45'semigroup_3192
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_614
      (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
      (coe du_'43''43''45'isSemigroup_3180)
-- Data.List.Properties._.++-monoid
d_'43''43''45'monoid_3194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'43''43''45'monoid_3194 ~v0 ~v1 = du_'43''43''45'monoid_3194
du_'43''43''45'monoid_3194 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_914
du_'43''43''45'monoid_3194
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_990
      (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe du_'43''43''45'isMonoid_3182)
-- Data.List.Properties._.length-isMagmaHomomorphism
d_length'45'isMagmaHomomorphism_3204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaHomomorphism_194
d_length'45'isMagmaHomomorphism_3204 ~v0 ~v1
  = du_length'45'isMagmaHomomorphism_3204
du_length'45'isMagmaHomomorphism_3204 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaHomomorphism_194
du_length'45'isMagmaHomomorphism_3204
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_constructor_210
      (coe
         MAlonzo.Code.Relation.Binary.Morphism.Structures.C_constructor_54
         erased)
      erased
-- Data.List.Properties._.length-isMonoidHomomorphism
d_length'45'isMonoidHomomorphism_3210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidHomomorphism_380
d_length'45'isMonoidHomomorphism_3210 ~v0 ~v1
  = du_length'45'isMonoidHomomorphism_3210
du_length'45'isMonoidHomomorphism_3210 ::
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidHomomorphism_380
du_length'45'isMonoidHomomorphism_3210
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.C_constructor_400
      (coe du_length'45'isMagmaHomomorphism_3204) erased
-- Data.List.Properties._.prod
d_prod_3224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d_prod_3224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_prod_3224 v6
du_prod_3224 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du_prod_3224 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_cartesianProductWith_70 (coe v0)
-- Data.List.Properties._.cartesianProductWith-zeroˡ
d_cartesianProductWith'45'zero'737'_3228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cartesianProductWith'45'zero'737'_3228 = erased
-- Data.List.Properties._.cartesianProductWith-zeroʳ
d_cartesianProductWith'45'zero'691'_3232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cartesianProductWith'45'zero'691'_3232 = erased
-- Data.List.Properties._.cartesianProductWith-distribʳ-++
d_cartesianProductWith'45'distrib'691''45''43''43'_3244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cartesianProductWith'45'distrib'691''45''43''43'_3244 = erased
-- Data.List.Properties._.alignWith-cong
d_alignWith'45'cong_3276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny) ->
  (MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny) ->
  (MAlonzo.Code.Data.These.Base.T_These_38 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alignWith'45'cong_3276 = erased
-- Data.List.Properties._.length-alignWith
d_length'45'alignWith_3312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'alignWith_3312 = erased
-- Data.List.Properties._.alignWith-map
d_alignWith'45'map_3334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alignWith'45'map_3334 = erased
-- Data.List.Properties._.map-alignWith
d_map'45'alignWith_3366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'alignWith_3366 = erased
-- Data.List.Properties._.alignWith-flip
d_alignWith'45'flip_3390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alignWith'45'flip_3390 = erased
-- Data.List.Properties._.alignWith-comm
d_alignWith'45'comm_3424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny) ->
  (MAlonzo.Code.Data.These.Base.T_These_38 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_alignWith'45'comm_3424 = erased
-- Data.List.Properties.align-map
d_align'45'map_3440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_align'45'map_3440 = erased
-- Data.List.Properties.align-flip
d_align'45'flip_3454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_align'45'flip_3454 = erased
-- Data.List.Properties._.zipWith-cong
d_zipWith'45'cong_3480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zipWith'45'cong_3480 = erased
-- Data.List.Properties._.zipWith-zeroˡ
d_zipWith'45'zero'737'_3514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zipWith'45'zero'737'_3514 = erased
-- Data.List.Properties._.zipWith-zeroʳ
d_zipWith'45'zero'691'_3522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zipWith'45'zero'691'_3522 = erased
-- Data.List.Properties._.length-zipWith
d_length'45'zipWith_3532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'zipWith_3532 = erased
-- Data.List.Properties._.zipWith-map
d_zipWith'45'map_3562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zipWith'45'map_3562 = erased
-- Data.List.Properties._.map-zipWith
d_map'45'zipWith_3606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'zipWith_3606 = erased
-- Data.List.Properties._.zipWith-flip
d_zipWith'45'flip_3636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zipWith'45'flip_3636 = erased
-- Data.List.Properties._.zipWith-comm
d_zipWith'45'comm_3674 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zipWith'45'comm_3674 = erased
-- Data.List.Properties.zip-map
d_zip'45'map_3690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zip'45'map_3690 = erased
-- Data.List.Properties.zip-flip
d_zip'45'flip_3708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zip'45'flip_3708 = erased
-- Data.List.Properties.unalignWith-this
d_unalignWith'45'this_3716 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unalignWith'45'this_3716 = erased
-- Data.List.Properties.unalignWith-that
d_unalignWith'45'that_3726 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unalignWith'45'that_3726 = erased
-- Data.List.Properties._.unalignWith-cong
d_unalignWith'45'cong_3748 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.These.Base.T_These_38) ->
  (AgdaAny -> MAlonzo.Code.Data.These.Base.T_These_38) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unalignWith'45'cong_3748 = erased
-- Data.List.Properties._.unalignWith-map
d_unalignWith'45'map_3812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.These.Base.T_These_38) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unalignWith'45'map_3812 = erased
-- Data.List.Properties._.map-unalignWith
d_map'45'unalignWith_3864 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.These.Base.T_These_38) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'unalignWith_3864 = erased
-- Data.List.Properties._.unalignWith-alignWith
d_unalignWith'45'alignWith_3928 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.These.Base.T_These_38) ->
  (MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny) ->
  (MAlonzo.Code.Data.These.Base.T_These_38 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unalignWith'45'alignWith_3928 = erased
-- Data.List.Properties._.unzipWith-cong
d_unzipWith'45'cong_3976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unzipWith'45'cong_3976 = erased
-- Data.List.Properties._.length-unzipWith₁
d_length'45'unzipWith'8321'_4000 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'unzipWith'8321'_4000 = erased
-- Data.List.Properties._.length-unzipWith₂
d_length'45'unzipWith'8322'_4008 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'unzipWith'8322'_4008 = erased
-- Data.List.Properties._.zipWith-unzipWith
d_zipWith'45'unzipWith_4016 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zipWith'45'unzipWith_4016 = erased
-- Data.List.Properties._.unzipWith-zipWith
d_unzipWith'45'zipWith_4036 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unzipWith'45'zipWith_4036 = erased
-- Data.List.Properties._.unzipWith-map
d_unzipWith'45'map_4060 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unzipWith'45'map_4060 = erased
-- Data.List.Properties._.map-unzipWith
d_map'45'unzipWith_4074 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'unzipWith_4074 = erased
-- Data.List.Properties._.unzipWith-swap
d_unzipWith'45'swap_4088 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unzipWith'45'swap_4088 = erased
-- Data.List.Properties._.unzipWith-++
d_unzipWith'45''43''43'_4098 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unzipWith'45''43''43'_4098 = erased
-- Data.List.Properties.unzip-map
d_unzip'45'map_4112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unzip'45'map_4112 = erased
-- Data.List.Properties.unzip-swap
d_unzip'45'swap_4120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unzip'45'swap_4120 = erased
-- Data.List.Properties.zip-unzip
d_zip'45'unzip_4124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zip'45'unzip_4124 = erased
-- Data.List.Properties.unzip-zip
d_unzip'45'zip_4132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unzip'45'zip_4132 = erased
-- Data.List.Properties.foldr-universal
d_foldr'45'universal_4146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  ([AgdaAny] -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny ->
   [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldr'45'universal_4146 = erased
-- Data.List.Properties.foldr-cong
d_foldr'45'cong_4184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldr'45'cong_4184 = erased
-- Data.List.Properties.foldr-fusion
d_foldr'45'fusion_4212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldr'45'fusion_4212 = erased
-- Data.List.Properties.id-is-foldr
d_id'45'is'45'foldr_4228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_id'45'is'45'foldr_4228 = erased
-- Data.List.Properties.++-is-foldr
d_'43''43''45'is'45'foldr_4238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45'is'45'foldr_4238 = erased
-- Data.List.Properties.foldr-++
d_foldr'45''43''43'_4260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldr'45''43''43'_4260 = erased
-- Data.List.Properties.map-is-foldr
d_map'45'is'45'foldr_4284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'is'45'foldr_4284 = erased
-- Data.List.Properties.foldr-∷ʳ
d_foldr'45''8759''691'_4306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldr'45''8759''691'_4306 = erased
-- Data.List.Properties.foldr-map
d_foldr'45'map_4332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldr'45'map_4332 = erased
-- Data.List.Properties._.foldr-forcesᵇ
d_foldr'45'forces'7495'_4370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_foldr'45'forces'7495'_4370 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_foldr'45'forces'7495'_4370 v4 v5 v6 v7 v8
du_foldr'45'forces'7495'_4370 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_foldr'45'forces'7495'_4370 v0 v1 v2 v3 v4
  = case coe v3 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v5 v6
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   v1 v5
                   (coe
                      MAlonzo.Code.Data.List.Base.du_foldr_216 (coe v0) (coe v2)
                      (coe v6))
                   v4))
             (coe
                du_foldr'45'forces'7495'_4370 (coe v0) (coe v1) (coe v2) (coe v6)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      v1 v5
                      (coe
                         MAlonzo.Code.Data.List.Base.du_foldr_216 (coe v0) (coe v2)
                         (coe v6))
                      v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Properties._.foldr-preservesᵇ
d_foldr'45'preserves'7495'_4392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_foldr'45'preserves'7495'_4392 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_foldr'45'preserves'7495'_4392 v4 v5 v6 v7 v8 v9
du_foldr'45'preserves'7495'_4392 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_foldr'45'preserves'7495'_4392 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50 -> coe v4
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v8 v9
        -> case coe v3 of
             (:) v10 v11
               -> coe
                    v1 v10
                    (coe
                       MAlonzo.Code.Data.List.Base.du_foldr_216 (coe v0) (coe v2)
                       (coe v11))
                    v8
                    (coe
                       du_foldr'45'preserves'7495'_4392 (coe v0) (coe v1) (coe v2)
                       (coe v11) (coe v4) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Properties._.foldr-preservesʳ
d_foldr'45'preserves'691'_4412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> [AgdaAny] -> AgdaAny
d_foldr'45'preserves'691'_4412 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_foldr'45'preserves'691'_4412 v4 v5 v6 v7 v8
du_foldr'45'preserves'691'_4412 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> [AgdaAny] -> AgdaAny
du_foldr'45'preserves'691'_4412 v0 v1 v2 v3 v4
  = case coe v4 of
      [] -> coe v3
      (:) v5 v6
        -> coe
             v1 v5
             (coe
                MAlonzo.Code.Data.List.Base.du_foldr_216 (coe v0) (coe v2)
                (coe v6))
             (coe
                du_foldr'45'preserves'691'_4412 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Properties._.foldr-preservesᵒ
d_foldr'45'preserves'7506'_4432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_foldr'45'preserves'7506'_4432 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_foldr'45'preserves'7506'_4432 v4 v5 v6 v7 v8
du_foldr'45'preserves'7506'_4432 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_foldr'45'preserves'7506'_4432 v0 v1 v2 v3 v4
  = case coe v3 of
      []
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5 -> coe v5
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v5 v6
        -> case coe v4 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
               -> coe
                    v1 v5
                    (coe
                       MAlonzo.Code.Data.List.Base.du_foldr_216 (coe v0) (coe v2)
                       (coe v6))
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe
                          du_foldr'45'preserves'7506'_4432 (coe v0) (coe v1) (coe v2)
                          (coe v6) (coe v4)))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v10
                      -> coe
                           v1 v5
                           (coe
                              MAlonzo.Code.Data.List.Base.du_foldr_216 (coe v0) (coe v2)
                              (coe v6))
                           (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v10))
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v10
                      -> coe
                           v1 v5
                           (coe
                              MAlonzo.Code.Data.List.Base.du_foldr_216 (coe v0) (coe v2)
                              (coe v6))
                           (coe
                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                              (coe
                                 du_foldr'45'preserves'7506'_4432 (coe v0) (coe v1) (coe v2)
                                 (coe v6)
                                 (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v10))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Properties.foldl-cong
d_foldl'45'cong_4480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldl'45'cong_4480 = erased
-- Data.List.Properties.foldl-++
d_foldl'45''43''43'_4506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldl'45''43''43'_4506 = erased
-- Data.List.Properties.foldl-∷ʳ
d_foldl'45''8759''691'_4532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldl'45''8759''691'_4532 = erased
-- Data.List.Properties.foldl-map
d_foldl'45'map_4558 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldl'45'map_4558 = erased
-- Data.List.Properties.concat-map
d_concat'45'map_4578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [[AgdaAny]] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_concat'45'map_4578 = erased
-- Data.List.Properties.concat-++
d_concat'45''43''43'_4600 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [[AgdaAny]] ->
  [[AgdaAny]] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_concat'45''43''43'_4600 = erased
-- Data.List.Properties.concat-concat
d_concat'45'concat_4618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [[[AgdaAny]]] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_concat'45'concat_4618 = erased
-- Data.List.Properties.concat-map-[_]
d_concat'45'map'45''91'_'93'_4626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_concat'45'map'45''91'_'93'_4626 = erased
-- Data.List.Properties.concat-[_]
d_concat'45''91'_'93'_4634 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_concat'45''91'_'93'_4634 = erased
-- Data.List.Properties.concatMap-cong
d_concatMap'45'cong_4642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  (AgdaAny -> [AgdaAny]) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_concatMap'45'cong_4642 = erased
-- Data.List.Properties.concatMap-pure
d_concatMap'45'pure_4646 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_concatMap'45'pure_4646 = erased
-- Data.List.Properties.concatMap-map
d_concatMap'45'map_4652 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_concatMap'45'map_4652 = erased
-- Data.List.Properties.map-concatMap
d_map'45'concatMap_4662 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> [AgdaAny]) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'concatMap_4662 = erased
-- Data.List.Properties.concatMap-++
d_concatMap'45''43''43'_4676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_concatMap'45''43''43'_4676 = erased
-- Data.List.Properties.catMaybes-concatMap
d_catMaybes'45'concatMap_4688 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [Maybe AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_catMaybes'45'concatMap_4688 = erased
-- Data.List.Properties.length-catMaybes
d_length'45'catMaybes_4700 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [Maybe AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_length'45'catMaybes_4700 ~v0 ~v1 v2
  = du_length'45'catMaybes_4700 v2
du_length'45'catMaybes_4700 ::
  [Maybe AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_length'45'catMaybes_4700 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe
                MAlonzo.Code.Data.List.Base.du_length_268
                (coe MAlonzo.Code.Data.List.Base.du_catMaybes_256 v0))
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe du_length'45'catMaybes_4700 (coe v2))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe du_length'45'catMaybes_4700 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Properties.catMaybes-++
d_catMaybes'45''43''43'_4710 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [Maybe AgdaAny] ->
  [Maybe AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_catMaybes'45''43''43'_4710 = erased
-- Data.List.Properties.map-catMaybes
d_map'45'catMaybes_4726 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [Maybe AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'catMaybes_4726 = erased
-- Data.List.Properties.Any-catMaybes⁺
d_Any'45'catMaybes'8314'_4744 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [Maybe AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_Any'45'catMaybes'8314'_4744 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_Any'45'catMaybes'8314'_4744 v4 v5
du_Any'45'catMaybes'8314'_4744 ::
  [Maybe AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_Any'45'catMaybes'8314'_4744 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> case coe v1 of
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v7
                      -> case coe v7 of
                           MAlonzo.Code.Data.Maybe.Relation.Unary.Any.C_just_30 v9
                             -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v9
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v7
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                           (coe du_Any'45'catMaybes'8314'_4744 (coe v3) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> case coe v1 of
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v6
                      -> coe du_Any'45'catMaybes'8314'_4744 (coe v3) (coe v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Properties.mapMaybe-cong
d_mapMaybe'45'cong_4766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mapMaybe'45'cong_4766 = erased
-- Data.List.Properties.mapMaybe-just
d_mapMaybe'45'just_4772 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mapMaybe'45'just_4772 = erased
-- Data.List.Properties.mapMaybe-nothing
d_mapMaybe'45'nothing_4784 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mapMaybe'45'nothing_4784 = erased
-- Data.List.Properties._.mapMaybe-concatMap
d_mapMaybe'45'concatMap_4800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Maybe AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mapMaybe'45'concatMap_4800 = erased
-- Data.List.Properties._.length-mapMaybe
d_length'45'mapMaybe_4806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Maybe AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_length'45'mapMaybe_4806 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_length'45'mapMaybe_4806 v4 v5
du_length'45'mapMaybe_4806 ::
  (AgdaAny -> Maybe AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_length'45'mapMaybe_4806 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
         (\ v2 v3 v4 ->
            coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 v4))
      (coe
         MAlonzo.Code.Data.List.Base.du_length_268
         (coe
            MAlonzo.Code.Data.List.Base.du_mapMaybe_258 (coe v0) (coe v1)))
      (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
            (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
            (\ v2 v3 v4 v5 v6 ->
               coe
                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v5
                 v6))
         (coe
            MAlonzo.Code.Data.List.Base.du_length_268
            (coe
               MAlonzo.Code.Data.List.Base.du_mapMaybe_258 (coe v0) (coe v1)))
         (coe
            MAlonzo.Code.Data.List.Base.du_length_268
            (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe v0) (coe v1)))
         (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
               (\ v2 v3 v4 v5 v6 ->
                  coe
                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v5
                    v6))
            (coe
               MAlonzo.Code.Data.List.Base.du_length_268
               (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe v0) (coe v1)))
            (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
            (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
               (coe MAlonzo.Code.Data.List.Base.du_length_268 v1))
            (coe
               MAlonzo.Code.Data.Nat.Properties.du_'8804''45'reflexive_2896
               (coe
                  MAlonzo.Code.Data.List.Base.du_length_268
                  (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe v0) (coe v1)))))
         (coe
            du_length'45'catMaybes_4700
            (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe v0) (coe v1))))
-- Data.List.Properties._.mapMaybe-++
d_mapMaybe'45''43''43'_4818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Maybe AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mapMaybe'45''43''43'_4818 = erased
-- Data.List.Properties._.mapMaybe-map
d_mapMaybe'45'map_4838 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mapMaybe'45'map_4838 = erased
-- Data.List.Properties._.map-mapMaybe
d_map'45'mapMaybe_4854 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> Maybe AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'mapMaybe_4854 = erased
-- Data.List.Properties._.mapMaybe-map-retract
d_mapMaybe'45'map'45'retract_4870 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mapMaybe'45'map'45'retract_4870 = erased
-- Data.List.Properties._.mapMaybe-map-none
d_mapMaybe'45'map'45'none_4890 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mapMaybe'45'map'45'none_4890 = erased
-- Data.List.Properties.mapMaybeIsInj₁∘mapInj₁
d_mapMaybeIsInj'8321''8728'mapInj'8321'_4898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mapMaybeIsInj'8321''8728'mapInj'8321'_4898 = erased
-- Data.List.Properties.mapMaybeIsInj₁∘mapInj₂
d_mapMaybeIsInj'8321''8728'mapInj'8322'_4904 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mapMaybeIsInj'8321''8728'mapInj'8322'_4904 = erased
-- Data.List.Properties.mapMaybeIsInj₂∘mapInj₂
d_mapMaybeIsInj'8322''8728'mapInj'8322'_4910 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mapMaybeIsInj'8322''8728'mapInj'8322'_4910 = erased
-- Data.List.Properties.mapMaybeIsInj₂∘mapInj₁
d_mapMaybeIsInj'8322''8728'mapInj'8321'_4916 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mapMaybeIsInj'8322''8728'mapInj'8321'_4916 = erased
-- Data.List.Properties.length-applyUpTo
d_length'45'applyUpTo_4924 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (Integer -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'applyUpTo_4924 = erased
-- Data.List.Properties.lookup-applyUpTo
d_lookup'45'applyUpTo_4938 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (Integer -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'applyUpTo_4938 = erased
-- Data.List.Properties.applyUpTo-∷ʳ
d_applyUpTo'45''8759''691'_4954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (Integer -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_applyUpTo'45''8759''691'_4954 = erased
-- Data.List.Properties.map-applyUpTo
d_map'45'applyUpTo_4970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (Integer -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'applyUpTo_4970 = erased
-- Data.List.Properties._.length-applyDownFrom
d_length'45'applyDownFrom_4994 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (Integer -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'applyDownFrom_4994 = erased
-- Data.List.Properties._.lookup-applyDownFrom
d_lookup'45'applyDownFrom_5002 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (Integer -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'applyDownFrom_5002 = erased
-- Data.List.Properties._.applyDownFrom-∷ʳ
d_applyDownFrom'45''8759''691'_5012 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (Integer -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_applyDownFrom'45''8759''691'_5012 = erased
-- Data.List.Properties._.map-applyDownFrom
d_map'45'applyDownFrom_5022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'applyDownFrom_5022 = erased
-- Data.List.Properties.length-upTo
d_length'45'upTo_5034 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'upTo_5034 = erased
-- Data.List.Properties.lookup-upTo
d_lookup'45'upTo_5040 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'upTo_5040 = erased
-- Data.List.Properties.upTo-∷ʳ
d_upTo'45''8759''691'_5044 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_upTo'45''8759''691'_5044 = erased
-- Data.List.Properties.map-upTo
d_map'45'upTo_5050 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (Integer -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'upTo_5050 = erased
-- Data.List.Properties.length-downFrom
d_length'45'downFrom_5054 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'downFrom_5054 = erased
-- Data.List.Properties.lookup-downFrom
d_lookup'45'downFrom_5060 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'downFrom_5060 = erased
-- Data.List.Properties.downFrom-∷ʳ
d_downFrom'45''8759''691'_5064 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_downFrom'45''8759''691'_5064 = erased
-- Data.List.Properties.map-downFrom
d_map'45'downFrom_5070 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (Integer -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'downFrom_5070 = erased
-- Data.List.Properties.tabulate-cong
d_tabulate'45'cong_5078 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tabulate'45'cong_5078 = erased
-- Data.List.Properties.tabulate-lookup
d_tabulate'45'lookup_5088 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tabulate'45'lookup_5088 = erased
-- Data.List.Properties.length-tabulate
d_length'45'tabulate_5100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'tabulate_5100 = erased
-- Data.List.Properties.lookup-tabulate
d_lookup'45'tabulate_5118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'tabulate_5118 = erased
-- Data.List.Properties.map-tabulate
d_map'45'tabulate_5132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'tabulate_5132 = erased
-- Data.List.Properties.length-%=
d_length'45''37''61'_5152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45''37''61'_5152 = erased
-- Data.List.Properties.length-∷=
d_length'45''8759''61'_5174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45''8759''61'_5174 = erased
-- Data.List.Properties.map-∷=
d_map'45''8759''61'_5192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45''8759''61'_5192 = erased
-- Data.List.Properties.length-insertAt
d_length'45'insertAt_5220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'insertAt_5220 = erased
-- Data.List.Properties.length-removeAt
d_length'45'removeAt_5238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'removeAt_5238 = erased
-- Data.List.Properties.length-removeAt′
d_length'45'removeAt'8242'_5254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'removeAt'8242'_5254 = erased
-- Data.List.Properties.map-removeAt
d_map'45'removeAt_5272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'removeAt_5272 = erased
-- Data.List.Properties.removeAt-insertAt
d_removeAt'45'insertAt_5296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_removeAt'45'insertAt_5296 = erased
-- Data.List.Properties.insertAt-removeAt
d_insertAt'45'removeAt_5316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_insertAt'45'removeAt_5316 = erased
-- Data.List.Properties.length-take
d_length'45'take_5334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'take_5334 = erased
-- Data.List.Properties.take-map
d_take'45'map_5352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'45'map_5352 = erased
-- Data.List.Properties.take-suc
d_take'45'suc_5372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'45'suc_5372 = erased
-- Data.List.Properties.take-suc-tabulate
d_take'45'suc'45'tabulate_5394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'45'suc'45'tabulate_5394 = erased
-- Data.List.Properties.take-all
d_take'45'all_5412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'45'all_5412 = erased
-- Data.List.Properties.take-[]
d_take'45''91''93'_5426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'45''91''93'_5426 = erased
-- Data.List.Properties.take-take
d_take'45'take_5436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'45'take_5436 = erased
-- Data.List.Properties.take-drop
d_take'45'drop_5466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'45'drop_5466 = erased
-- Data.List.Properties.length-drop
d_length'45'drop_5488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'drop_5488 = erased
-- Data.List.Properties.drop-map
d_drop'45'map_5506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'map_5506 = erased
-- Data.List.Properties.drop-[]
d_drop'45''91''93'_5520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''91''93'_5520 = erased
-- Data.List.Properties.take++drop≡id
d_take'43''43'drop'8801'id_5528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'43''43'drop'8801'id_5528 = erased
-- Data.List.Properties.drop-take-suc
d_drop'45'take'45'suc_5548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'take'45'suc_5548 = erased
-- Data.List.Properties.drop-take-suc-tabulate
d_drop'45'take'45'suc'45'tabulate_5568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'take'45'suc'45'tabulate_5568 = erased
-- Data.List.Properties.drop-drop
d_drop'45'drop_5588 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'drop_5588 = erased
-- Data.List.Properties.drop-all
d_drop'45'all_5610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'all_5610 = erased
-- Data.List.Properties.length-replicate
d_length'45'replicate_5626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'replicate_5626 = erased
-- Data.List.Properties.lookup-replicate
d_lookup'45'replicate_5636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'replicate_5636 = erased
-- Data.List.Properties.map-replicate
d_map'45'replicate_5654 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'replicate_5654 = erased
-- Data.List.Properties.zipWith-replicate
d_zipWith'45'replicate_5676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zipWith'45'replicate_5676 = erased
-- Data.List.Properties.length-iterate
d_length'45'iterate_5700 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'iterate_5700 = erased
-- Data.List.Properties.iterate-id
d_iterate'45'id_5716 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_iterate'45'id_5716 = erased
-- Data.List.Properties.lookup-iterate
d_lookup'45'iterate_5734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'iterate_5734 = erased
-- Data.List.Properties.splitAt-defn
d_splitAt'45'defn_5752 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'45'defn_5752 = erased
-- Data.List.Properties._.splitAt-map
d_splitAt'45'map_5778 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAt'45'map_5778 = erased
-- Data.List.Properties._.takeWhile++dropWhile
d_takeWhile'43''43'dropWhile_5806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_takeWhile'43''43'dropWhile_5806 = erased
-- Data.List.Properties._.span-defn
d_span'45'defn_5826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_span'45'defn_5826 = erased
-- Data.List.Properties._.length-filter
d_length'45'filter_5860 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_length'45'filter_5860 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_length'45'filter_5860 v4 v5
du_length'45'filter_5860 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_length'45'filter_5860 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      (:) v2 v3
        -> let v4 = coe du_length'45'filter_5860 (coe v0) (coe v3) in
           coe
             (let v5
                    = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                        (coe v0 v2) in
              coe
                (if coe v5
                   then coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
                   else coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Properties._.filter-all
d_filter'45'all_5886 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_filter'45'all_5886 = erased
-- Data.List.Properties._.filter-notAll
d_filter'45'notAll_5922 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_filter'45'notAll_5922 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_filter'45'notAll_5922 v4 v5 v6
du_filter'45'notAll_5922 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_filter'45'notAll_5922 v0 v1 v2
  = case coe v1 of
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v7
               -> let v8 = coe v0 v3 in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                         -> if coe v9
                              then coe
                                     seq (coe v10)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                        erased)
                              else coe
                                     MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                     (coe du_length'45'filter_5860 (coe v0) (coe v4))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v7
               -> let v8
                        = coe du_filter'45'notAll_5922 (coe v0) (coe v4) (coe v7) in
                  coe
                    (let v9
                           = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                               (coe v0 v3) in
                     coe
                       (if coe v9
                          then coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8
                          else coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Properties._.filter-some
d_filter'45'some_5978 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_filter'45'some_5978 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_filter'45'some_5978 v4 v5 v6
du_filter'45'some_5978 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_filter'45'some_5978 v0 v1 v2
  = case coe v1 of
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v7
               -> let v8 = coe v0 v3 in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                         -> if coe v9
                              then coe
                                     MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                     (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                              else coe
                                     seq (coe v10)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                        erased)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v7
               -> let v8
                        = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                            (coe v0 v3) in
                  coe
                    (coe
                       seq (coe v8)
                       (coe du_filter'45'some_5978 (coe v0) (coe v4) (coe v7)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Properties._.filter-none
d_filter'45'none_6028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_filter'45'none_6028 = erased
-- Data.List.Properties._.filter-complete
d_filter'45'complete_6062 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_filter'45'complete_6062 = erased
-- Data.List.Properties._.filter-accept
d_filter'45'accept_6094 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_filter'45'accept_6094 = erased
-- Data.List.Properties._.filter-reject
d_filter'45'reject_6118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  [AgdaAny] ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_filter'45'reject_6118 = erased
-- Data.List.Properties._.filter-idem
d_filter'45'idem_6138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_filter'45'idem_6138 = erased
-- Data.List.Properties._.filter-++
d_filter'45''43''43'_6168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_filter'45''43''43'_6168 = erased
-- Data.List.Properties._.filter-≐
d_filter'45''8784'_6220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_filter'45''8784'_6220 = erased
-- Data.List.Properties._.length-derun
d_length'45'derun_6266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_length'45'derun_6266 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_length'45'derun_6266 v4 v5
du_length'45'derun_6266 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_length'45'derun_6266 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
             (coe
                MAlonzo.Code.Data.List.Base.du_length_268
                (coe MAlonzo.Code.Data.List.Base.du_derun_836 (coe v0) (coe v1)))
      (:) v2 v3
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                    (coe
                       MAlonzo.Code.Data.List.Base.du_length_268
                       (coe MAlonzo.Code.Data.List.Base.du_derun_836 (coe v0) (coe v1)))
             (:) v4 v5
               -> let v6 = coe du_length'45'derun_6266 (coe v0) (coe v3) in
                  coe
                    (let v7
                           = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                               (coe v0 v2 v4) in
                     coe
                       (if coe v7
                          then coe v6
                          else coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Properties._.length-deduplicate
d_length'45'deduplicate_6300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_length'45'deduplicate_6300 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_length'45'deduplicate_6300 v4 v5
du_length'45'deduplicate_6300 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_length'45'deduplicate_6300 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      (:) v2 v3
        -> coe
             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                (\ v4 v5 v6 ->
                   coe MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998 v6))
             (coe
                MAlonzo.Code.Data.List.Base.du_length_268
                (coe
                   MAlonzo.Code.Data.List.Base.du_deduplicate_882 (coe v0) (coe v1)))
             (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                   (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                   (\ v4 v5 v6 v7 v8 ->
                      coe
                        MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v7
                        v8))
                (addInt
                   (coe (1 :: Integer))
                   (coe
                      MAlonzo.Code.Data.List.Base.du_length_268
                      (coe
                         MAlonzo.Code.Data.List.Base.du_filter_648
                         (coe
                            (\ v4 ->
                               coe
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_76
                                 (coe v0 v2 v4)))
                         (coe du_r_6310 (coe v0) (coe v3)))))
                (addInt
                   (coe (1 :: Integer))
                   (coe
                      MAlonzo.Code.Data.List.Base.du_length_268
                      (coe du_r_6310 (coe v0) (coe v3))))
                (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_310
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                      (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950)
                      (\ v4 v5 v6 v7 v8 ->
                         coe
                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128 v7
                           v8))
                   (addInt
                      (coe (1 :: Integer))
                      (coe
                         MAlonzo.Code.Data.List.Base.du_length_268
                         (coe du_r_6310 (coe v0) (coe v3))))
                   (addInt
                      (coe (1 :: Integer))
                      (coe MAlonzo.Code.Data.List.Base.du_length_268 v3))
                   (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                         (coe MAlonzo.Code.Data.Nat.Properties.d_'8804''45'isPreorder_2950))
                      (coe
                         addInt (coe (1 :: Integer))
                         (coe MAlonzo.Code.Data.List.Base.du_length_268 v3)))
                   (coe
                      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                      (coe du_length'45'deduplicate_6300 (coe v0) (coe v3))))
                (coe
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                   (coe
                      du_length'45'filter_5860
                      (coe
                         (\ v4 ->
                            coe
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_76
                              (coe v0 v2 v4)))
                      (coe du_r_6310 (coe v0) (coe v3)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Properties._._.r
d_r_6310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> [AgdaAny] -> [AgdaAny]
d_r_6310 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 = du_r_6310 v4 v6
du_r_6310 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny]
du_r_6310 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_deduplicate_882 (coe v0) (coe v1)
-- Data.List.Properties._.derun-reject
d_derun'45'reject_6318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_derun'45'reject_6318 = erased
-- Data.List.Properties._.derun-accept
d_derun'45'accept_6356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_derun'45'accept_6356 = erased
-- Data.List.Properties._.partition-defn
d_partition'45'defn_6400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_partition'45'defn_6400 = erased
-- Data.List.Properties._.length-partition
d_length'45'partition_6434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_length'45'partition_6434 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_length'45'partition_6434 v4 v5
du_length'45'partition_6434 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_length'45'partition_6434 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      (:) v2 v3
        -> let v4 = coe du_length'45'partition_6434 (coe v0) (coe v3) in
           coe
             (let v5
                    = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                        (coe v0 v2) in
              coe
                (if coe v5
                   then coe
                          MAlonzo.Code.Data.Product.Base.du_map_128
                          (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34)
                          (coe (\ v6 v7 -> v7)) (coe v4)
                   else coe
                          MAlonzo.Code.Data.Product.Base.du_map_128 (coe (\ v6 -> v6))
                          (coe (\ v6 -> coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34))
                          (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Properties._.partition-is-foldr
d_partition'45'is'45'foldr_6464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_partition'45'is'45'foldr_6464 = erased
-- Data.List.Properties.ʳ++-defn
d_'691''43''43''45'defn_6496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'691''43''43''45'defn_6496 = erased
-- Data.List.Properties.++-ʳ++
d_'43''43''45''691''43''43'_6512 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''43''45''691''43''43'_6512 = erased
-- Data.List.Properties.ʳ++-ʳ++
d_'691''43''43''45''691''43''43'_6528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'691''43''43''45''691''43''43'_6528 = erased
-- Data.List.Properties.length-ʳ++
d_length'45''691''43''43'_6542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45''691''43''43'_6542 = erased
-- Data.List.Properties.map-ʳ++
d_map'45''691''43''43'_6556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45''691''43''43'_6556 = erased
-- Data.List.Properties.foldr-ʳ++
d_foldr'45''691''43''43'_6576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldr'45''691''43''43'_6576 = erased
-- Data.List.Properties.foldl-ʳ++
d_foldl'45''691''43''43'_6600 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldl'45''691''43''43'_6600 = erased
-- Data.List.Properties.unfold-reverse
d_unfold'45'reverse_6620 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unfold'45'reverse_6620 = erased
-- Data.List.Properties.reverse-++
d_reverse'45''43''43'_6630 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45''43''43'_6630 = erased
-- Data.List.Properties.reverse-selfInverse
d_reverse'45'selfInverse_6636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45'selfInverse_6636 = erased
-- Data.List.Properties.reverse-involutive
d_reverse'45'involutive_6646 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45'involutive_6646 = erased
-- Data.List.Properties.reverse-injective
d_reverse'45'injective_6648 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45'injective_6648 = erased
-- Data.List.Properties.length-reverse
d_length'45'reverse_6652 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45'reverse_6652 = erased
-- Data.List.Properties.reverse-map
d_reverse'45'map_6658 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45'map_6658 = erased
-- Data.List.Properties.reverse-foldr
d_reverse'45'foldr_6668 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45'foldr_6668 = erased
-- Data.List.Properties.reverse-foldl
d_reverse'45'foldl_6682 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45'foldl_6682 = erased
-- Data.List.Properties.reverse-applyUpTo
d_reverse'45'applyUpTo_6694 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (Integer -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45'applyUpTo_6694 = erased
-- Data.List.Properties.reverse-upTo
d_reverse'45'upTo_6706 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45'upTo_6706 = erased
-- Data.List.Properties.reverse-applyDownFrom
d_reverse'45'applyDownFrom_6712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (Integer -> AgdaAny) ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45'applyDownFrom_6712 = erased
-- Data.List.Properties.reverse-downFrom
d_reverse'45'downFrom_6724 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45'downFrom_6724 = erased
-- Data.List.Properties.∷ʳ-injective
d_'8759''691''45'injective_6730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8759''691''45'injective_6730 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6
  = du_'8759''691''45'injective_6730 v4 v5
du_'8759''691''45'injective_6730 ::
  [AgdaAny] -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8759''691''45'injective_6730 v0 v1
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      (:) v2 v3
        -> case coe v1 of
             (:) v4 v5
               -> let v6 = coe du_'8759''45'injective_48 in
                  coe
                    (coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Data.Product.Base.du_map_128 erased
                          (coe (\ v7 v8 -> v8))
                          (coe du_'8759''691''45'injective_6730 (coe v3) (coe v5))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Properties.∷ʳ-injectiveˡ
d_'8759''691''45'injective'737'_6754 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8759''691''45'injective'737'_6754 = erased
-- Data.List.Properties.∷ʳ-injectiveʳ
d_'8759''691''45'injective'691'_6766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8759''691''45'injective'691'_6766 = erased
-- Data.List.Properties.∷ʳ-++
d_'8759''691''45''43''43'_6780 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8759''691''45''43''43'_6780 = erased
-- Data.List.Properties._.uncons-map
d_uncons'45'map_6798 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_uncons'45'map_6798 = erased
-- Data.List.Properties._.head-map
d_head'45'map_6814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_head'45'map_6814 = erased
-- Data.List.Properties._.last-map
d_last'45'map_6826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_last'45'map_6826 = erased
-- Data.List.Properties._.tail-map
d_tail'45'map_6844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tail'45'map_6844 = erased
-- Data.List.Properties.map-id₂
d_map'45'id'8322'_6850 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'id'8322'_6850 = erased
-- Data.List.Properties.map-cong₂
d_map'45'cong'8322'_6852 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'cong'8322'_6852 = erased
-- Data.List.Properties.map-compose
d_map'45'compose_6854 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'compose_6854 = erased
-- Data.List.Properties.map-++-commute
d_map'45''43''43''45'commute_6856 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45''43''43''45'commute_6856 = erased
-- Data.List.Properties.reverse-map-commute
d_reverse'45'map'45'commute_6858 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45'map'45'commute_6858 = erased
-- Data.List.Properties.reverse-++-commute
d_reverse'45''43''43''45'commute_6860 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45''43''43''45'commute_6860 = erased
-- Data.List.Properties.zipWith-identityˡ
d_zipWith'45'identity'737'_6862 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zipWith'45'identity'737'_6862 = erased
-- Data.List.Properties.zipWith-identityʳ
d_zipWith'45'identity'691'_6864 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zipWith'45'identity'691'_6864 = erased
-- Data.List.Properties.ʳ++-++
d_'691''43''43''45''43''43'_6866 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'691''43''43''45''43''43'_6866 = erased
-- Data.List.Properties.take++drop
d_take'43''43'drop_6868 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_take'43''43'drop_6868 = erased
-- Data.List.Properties.length-─
d_length'45''9472'_6870 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_length'45''9472'_6870 = erased
-- Data.List.Properties.map-─
d_map'45''9472'_6872 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45''9472'_6872 = erased
-- Data.List.Properties.scanr-defn
d_scanr'45'defn_6878 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scanr'45'defn_6878 = erased
-- Data.List.Properties.scanl-defn
d_scanl'45'defn_6918 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_scanl'45'defn_6918 = erased
-- Data.List.Properties.concat-[-]
d_concat'45''91''45''93'_6938 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_concat'45''91''45''93'_6938 = erased
-- Data.List.Properties.sum-++
d_sum'45''43''43'_6944 ::
  [Integer] ->
  [Integer] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sum'45''43''43'_6944 = erased
-- Data.List.Properties.sum-++-commute
d_sum'45''43''43''45'commute_6956 ::
  [Integer] ->
  [Integer] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sum'45''43''43''45'commute_6956 = erased
-- Data.List.Properties.∈⇒∣product
d_'8712''8658''8739'product_6962 ::
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'8712''8658''8739'product_6962 ~v0 v1 v2
  = du_'8712''8658''8739'product_6962 v1 v2
du_'8712''8658''8739'product_6962 ::
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'8712''8658''8739'product_6962 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v6
               -> coe
                    MAlonzo.Code.Data.Nat.Divisibility.du_m'8739'm'42'n_346
                    (coe MAlonzo.Code.Data.List.Base.d_product_1074 v3)
             MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v6
               -> coe
                    MAlonzo.Code.Data.Nat.Divisibility.du_'8739'n'8658''8739'm'42'n_374
                    v2 (coe du_'8712''8658''8739'product_6962 (coe v3) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Properties.product≢0
d_product'8802'0_6976 ::
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_product'8802'0_6976 ~v0 v1 = du_product'8802'0_6976 v1
du_product'8802'0_6976 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_product'8802'0_6976 v0
  = case coe v0 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_constructor_120
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v3 v4
        -> coe MAlonzo.Code.Data.Nat.Properties.du_m'42'n'8802'0_3958
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Properties.∈⇒≤product
d_'8712''8658''8804'product_6990 ::
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8712''8658''8804'product_6990 ~v0 v1 v2 v3
  = du_'8712''8658''8804'product_6990 v1 v2 v3
du_'8712''8658''8804'product_6990 ::
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8712''8658''8804'product_6990 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v11
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'42'n_4268 (coe v3)
                           (coe MAlonzo.Code.Data.List.Base.d_product_1074 v4)
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v11
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_m'8804'n'8658'm'8804'o'42'n_4290
                           (coe
                              MAlonzo.Code.Data.List.Base.du_foldr_216 (coe mulInt)
                              (coe (1 :: Integer)) (coe v4))
                           (coe v3)
                           (coe du_'8712''8658''8804'product_6990 (coe v4) (coe v8) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
