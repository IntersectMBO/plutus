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

module MAlonzo.Code.Class.Functor.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive

-- Class.Functor.Core.Functor
d_Functor_14 a0 = ()
newtype T_Functor_14
  = C_Functor'46'constructor_121 (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
                                  () ->
                                  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
                                  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny)
-- Class.Functor.Core.Functor._<$>_
d__'60''36''62'__20 ::
  T_Functor_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__20 v0
  = case coe v0 of
      C_Functor'46'constructor_121 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Functor.Core.Functor.fmap
d_fmap_22 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Functor_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_22 ~v0 v1 = du_fmap_22 v1
du_fmap_22 ::
  T_Functor_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmap_22 v0 = coe d__'60''36''62'__20 (coe v0)
-- Class.Functor.Core.Functor._<$_
d__'60''36'__24 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Functor_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__24 ~v0 v1 v2 ~v3 v4 ~v5 v6 v7
  = du__'60''36'__24 v1 v2 v4 v6 v7
du__'60''36'__24 ::
  T_Functor_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__24 v0 v1 v2 v3 v4
  = coe d__'60''36''62'__20 v0 v2 erased v1 erased (\ v5 -> v3) v4
-- Class.Functor.Core.Functor._<&>_
d__'60''38''62'__30 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Functor_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__30 ~v0 v1 v2 ~v3 v4 ~v5 v6 v7
  = du__'60''38''62'__30 v1 v2 v4 v6 v7
du__'60''38''62'__30 ::
  T_Functor_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__30 v0 v1 v2 v3 v4
  = coe d__'60''36''62'__20 v0 v1 erased v2 erased v4 v3
-- Class.Functor.Core._._<$_
d__'60''36'__34 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Functor_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__34 ~v0 v1 = du__'60''36'__34 v1
du__'60''36'__34 ::
  T_Functor_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__34 v0 v1 v2 v3 v4 v5 v6
  = coe du__'60''36'__24 (coe v0) v1 v3 v5 v6
-- Class.Functor.Core._._<$>_
d__'60''36''62'__36 ::
  T_Functor_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__36 v0 = coe d__'60''36''62'__20 (coe v0)
-- Class.Functor.Core._._<&>_
d__'60''38''62'__38 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Functor_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__38 ~v0 v1 = du__'60''38''62'__38 v1
du__'60''38''62'__38 ::
  T_Functor_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__38 v0 v1 v2 v3 v4 v5 v6
  = coe du__'60''38''62'__30 (coe v0) v1 v3 v5 v6
-- Class.Functor.Core._.fmap
d_fmap_40 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Functor_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_40 ~v0 v1 = du_fmap_40 v1
du_fmap_40 ::
  T_Functor_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmap_40 v0 = coe du_fmap_22 (coe v0)
-- Class.Functor.Core.FunctorLaws
d_FunctorLaws_46 a0 a1 = ()
data T_FunctorLaws_46 = C_FunctorLaws'46'constructor_8593
-- Class.Functor.Core.FunctorLaws.fmap-id
d_fmap'45'id_76 ::
  T_FunctorLaws_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'id_76 = erased
-- Class.Functor.Core.FunctorLaws.fmap-∘
d_fmap'45''8728'_90 ::
  T_FunctorLaws_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45''8728'_90 = erased
-- Class.Functor.Core._.fmap-id
d_fmap'45'id_94 ::
  T_FunctorLaws_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'id_94 = erased
-- Class.Functor.Core._.fmap-∘
d_fmap'45''8728'_96 ::
  T_FunctorLaws_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45''8728'_96 = erased
