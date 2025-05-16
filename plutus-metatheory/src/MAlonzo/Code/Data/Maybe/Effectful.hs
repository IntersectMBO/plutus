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

module MAlonzo.Code.Data.Maybe.Effectful where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Maybe qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Maybe.Base qualified
import MAlonzo.Code.Effect.Applicative qualified
import MAlonzo.Code.Effect.Choice qualified
import MAlonzo.Code.Effect.Empty qualified
import MAlonzo.Code.Effect.Functor qualified
import MAlonzo.Code.Effect.Monad qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Maybe.Effectful.functor
d_functor_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_functor_22 ~v0 = du_functor_22
du_functor_22 :: MAlonzo.Code.Effect.Functor.T_RawFunctor_24
du_functor_22
  = coe
      MAlonzo.Code.Effect.Functor.C_RawFunctor'46'constructor_241
      (coe (\ v0 v1 v2 -> coe MAlonzo.Code.Data.Maybe.Base.du_map_64 v2))
-- Data.Maybe.Effectful.applicative
d_applicative_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
d_applicative_24 ~v0 = du_applicative_24
du_applicative_24 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
du_applicative_24
  = coe
      MAlonzo.Code.Effect.Applicative.C_RawApplicative'46'constructor_453
      (coe du_functor_22)
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16))
      (coe
         (\ v0 v1 ->
            coe
              MAlonzo.Code.Data.Maybe.Base.du_maybe_32
              (coe MAlonzo.Code.Data.Maybe.Base.du_map_64)
              (let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
               coe (coe (\ v3 -> v2)))))
-- Data.Maybe.Effectful.empty
d_empty_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Empty.T_RawEmpty_16
d_empty_26 ~v0 = du_empty_26
du_empty_26 :: MAlonzo.Code.Effect.Empty.T_RawEmpty_16
du_empty_26
  = coe
      MAlonzo.Code.Effect.Empty.C_RawEmpty'46'constructor_129
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Data.Maybe.Effectful.choice
d_choice_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Choice.T_RawChoice_16
d_choice_28 ~v0 = du_choice_28
du_choice_28 :: MAlonzo.Code.Effect.Choice.T_RawChoice_16
du_choice_28
  = coe
      MAlonzo.Code.Effect.Choice.C_RawChoice'46'constructor_149
      (\ v0 v1 v2 ->
         coe MAlonzo.Code.Data.Maybe.Base.du__'60''8739''62'__80 v1 v2)
-- Data.Maybe.Effectful.applicativeZero
d_applicativeZero_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicativeZero_120
d_applicativeZero_30 ~v0 = du_applicativeZero_30
du_applicativeZero_30 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicativeZero_120
du_applicativeZero_30
  = coe
      MAlonzo.Code.Effect.Applicative.C_RawApplicativeZero'46'constructor_8049
      (coe du_applicative_24) (coe du_empty_26)
-- Data.Maybe.Effectful.alternative
d_alternative_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Applicative.T_RawAlternative_180
d_alternative_32 ~v0 = du_alternative_32
du_alternative_32 ::
  MAlonzo.Code.Effect.Applicative.T_RawAlternative_180
du_alternative_32
  = coe
      MAlonzo.Code.Effect.Applicative.C_RawAlternative'46'constructor_9897
      (coe du_applicativeZero_30) (coe du_choice_28)
-- Data.Maybe.Effectful.monad
d_monad_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Monad.T_RawMonad_24
d_monad_34 ~v0 = du_monad_34
du_monad_34 :: MAlonzo.Code.Effect.Monad.T_RawMonad_24
du_monad_34
  = coe
      MAlonzo.Code.Effect.Monad.C_RawMonad'46'constructor_319
      (coe du_applicative_24)
      (coe
         (\ v0 v1 v2 v3 ->
            coe MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72 v2 v3))
-- Data.Maybe.Effectful.join
d_join_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Maybe (Maybe AgdaAny) -> Maybe AgdaAny
d_join_36 ~v0 ~v1 = du_join_36
du_join_36 :: Maybe (Maybe AgdaAny) -> Maybe AgdaAny
du_join_36
  = coe MAlonzo.Code.Effect.Monad.du_join_158 (coe du_monad_34)
-- Data.Maybe.Effectful.monadZero
d_monadZero_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Monad.T_RawMonadZero_206
d_monadZero_38 ~v0 = du_monadZero_38
du_monadZero_38 :: MAlonzo.Code.Effect.Monad.T_RawMonadZero_206
du_monadZero_38
  = coe
      MAlonzo.Code.Effect.Monad.C_RawMonadZero'46'constructor_7131
      (coe du_monad_34) (coe du_empty_26)
-- Data.Maybe.Effectful.monadPlus
d_monadPlus_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Monad.T_RawMonadPlus_284
d_monadPlus_40 ~v0 = du_monadPlus_40
du_monadPlus_40 :: MAlonzo.Code.Effect.Monad.T_RawMonadPlus_284
du_monadPlus_40
  = coe
      MAlonzo.Code.Effect.Monad.C_RawMonadPlus'46'constructor_9035
      (coe du_monadZero_38) (coe du_choice_28)
-- Data.Maybe.Effectful.TraversableA.sequenceA
d_sequenceA_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  () -> Maybe AgdaAny -> AgdaAny
d_sequenceA_88 ~v0 ~v1 ~v2 v3 ~v4 v5 = du_sequenceA_88 v3 v5
du_sequenceA_88 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  Maybe AgdaAny -> AgdaAny
du_sequenceA_88 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
             (MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v0)) erased
             erased (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16) v2
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Effect.Applicative.d_pure_32 v0 erased v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Effectful.TraversableA.mapA
d_mapA_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> AgdaAny
d_mapA_92 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 = du_mapA_92 v3 v7 v8
du_mapA_92 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> AgdaAny
du_mapA_92 v0 v1 v2
  = coe
      du_sequenceA_88 (coe v0)
      (coe MAlonzo.Code.Data.Maybe.Base.du_map_64 v1 v2)
-- Data.Maybe.Effectful.TraversableA.forA
d_forA_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> Maybe AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_forA_96 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 = du_forA_96 v3 v7 v8
du_forA_96 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  Maybe AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_forA_96 v0 v1 v2 = coe du_mapA_92 (coe v0) (coe v2) (coe v1)
-- Data.Maybe.Effectful.TraversableM._.forA
d_forA_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> Maybe AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_forA_162 ~v0 ~v1 ~v2 v3 = du_forA_162 v3
du_forA_162 ::
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> Maybe AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du_forA_162 v0 v1 v2 v3 v4 v5
  = coe
      du_forA_96
      (coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0)) v4 v5
-- Data.Maybe.Effectful.TraversableM._.mapA
d_mapA_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> AgdaAny
d_mapA_164 ~v0 ~v1 ~v2 v3 = du_mapA_164 v3
du_mapA_164 ::
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> AgdaAny
du_mapA_164 v0 v1 v2 v3 v4 v5
  = coe
      du_mapA_92
      (coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0)) v4 v5
-- Data.Maybe.Effectful.TraversableM._.sequenceA
d_sequenceA_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  () -> Maybe AgdaAny -> AgdaAny
d_sequenceA_166 ~v0 ~v1 ~v2 v3 = du_sequenceA_166 v3
du_sequenceA_166 ::
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  () -> Maybe AgdaAny -> AgdaAny
du_sequenceA_166 v0 v1 v2
  = coe
      du_sequenceA_88
      (coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0)) v2
