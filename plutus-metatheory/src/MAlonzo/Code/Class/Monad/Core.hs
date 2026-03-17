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

module MAlonzo.Code.Class.Monad.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Applicative.Core
import qualified MAlonzo.Code.Class.Functor.Core
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base

-- Class.Monad.Core.Monad
d_Monad_8 a0 = ()
data T_Monad_8
  = C_Monad'46'constructor_309 MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
                               (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
                                () -> AgdaAny -> AgdaAny)
                               (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
                                () ->
                                MAlonzo.Code.Agda.Primitive.T_Level_18 ->
                                () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny)
-- Class.Monad.Core.Monad.super
d_super_18 ::
  T_Monad_8 -> MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
d_super_18 v0
  = case coe v0 of
      C_Monad'46'constructor_309 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Monad.Core.Monad.return
d_return_20 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_return_20 v0
  = case coe v0 of
      C_Monad'46'constructor_309 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Monad.Core.Monad._>>=_
d__'62''62''61'__22 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__22 v0
  = case coe v0 of
      C_Monad'46'constructor_309 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Monad.Core.Monad._>>_
d__'62''62'__24 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__24 ~v0 v1 v2 ~v3 v4 ~v5 v6 v7
  = du__'62''62'__24 v1 v2 v4 v6 v7
du__'62''62'__24 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__24 v0 v1 v2 v3 v4
  = coe d__'62''62''61'__22 v0 v1 erased v2 erased v3 (\ v5 -> v4)
-- Class.Monad.Core.Monad._=<<_
d__'61''60''60'__32 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'61''60''60'__32 ~v0 v1 v2 ~v3 v4 ~v5 v6 v7
  = du__'61''60''60'__32 v1 v2 v4 v6 v7
du__'61''60''60'__32 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'61''60''60'__32 v0 v1 v2 v3 v4
  = coe d__'62''62''61'__22 v0 v1 erased v2 erased v4 v3
-- Class.Monad.Core.Monad._≫=_
d__'8811''61'__38 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'8811''61'__38 ~v0 v1 = du__'8811''61'__38 v1
du__'8811''61'__38 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'8811''61'__38 v0 = coe d__'62''62''61'__22 (coe v0)
-- Class.Monad.Core.Monad._≫_
d__'8811'__40 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8811'__40 ~v0 v1 = du__'8811'__40 v1
du__'8811'__40 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8811'__40 v0 v1 v2 v3 v4 v5 v6
  = coe du__'62''62'__24 (coe v0) v1 v3 v5 v6
-- Class.Monad.Core.Monad._=≪_
d__'61''8810'__42 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'61''8810'__42 ~v0 v1 = du__'61''8810'__42 v1
du__'61''8810'__42 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'61''8810'__42 v0 v1 v2 v3 v4 v5 v6
  = coe du__'61''60''60'__32 (coe v0) v1 v3 v5 v6
-- Class.Monad.Core.Monad._>=>_
d__'62''61''62'__44 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'62''61''62'__44 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 ~v7 v8 v9 v10
  = du__'62''61''62'__44 v1 v4 v6 v8 v9 v10
du__'62''61''62'__44 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'62''61''62'__44 v0 v1 v2 v3 v4 v5
  = coe
      du__'61''60''60'__32 (coe v0) (coe v1) (coe v2) (coe v4)
      (coe v3 v5)
-- Class.Monad.Core.Monad._<=<_
d__'60''61''60'__50 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''61''60'__50 ~v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9
  = du__'60''61''60'__50 v1 v2 v4 v8 v9
du__'60''61''60'__50 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''61''60'__50 v0 v1 v2 v3 v4
  = coe
      du__'62''61''62'__44 (coe v0) (coe v1) (coe v2) (coe v4) (coe v3)
-- Class.Monad.Core.Monad.join
d_join_56 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_join_56 ~v0 v1 v2 ~v3 v4 = du_join_56 v1 v2 v4
du_join_56 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> AgdaAny -> AgdaAny
du_join_56 v0 v1 v2
  = coe d__'62''62''61'__22 v0 v1 erased v1 erased v2 (\ v3 -> v3)
-- Class.Monad.Core.Monad.Functor-M
d_Functor'45'M_60 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 -> MAlonzo.Code.Class.Functor.Core.T_Functor_14
d_Functor'45'M_60 ~v0 v1 = du_Functor'45'M_60 v1
du_Functor'45'M_60 ::
  T_Monad_8 -> MAlonzo.Code.Class.Functor.Core.T_Functor_14
du_Functor'45'M_60 v0
  = coe
      MAlonzo.Code.Class.Functor.Core.C_Functor'46'constructor_121
      (coe
         (\ v1 v2 v3 v4 v5 v6 ->
            coe
              du__'61''60''60'__32 (coe v0) (coe v1) (coe v3)
              (coe (\ v7 -> coe d_return_20 v0 v3 erased (coe v5 v7))) (coe v6)))
-- Class.Monad.Core._._<=<_
d__'60''61''60'__70 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''61''60'__70 ~v0 v1 = du__'60''61''60'__70 v1
du__'60''61''60'__70 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''61''60'__70 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe du__'60''61''60'__50 (coe v0) v1 v3 v7 v8
-- Class.Monad.Core._._=<<_
d__'61''60''60'__72 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'61''60''60'__72 ~v0 v1 = du__'61''60''60'__72 v1
du__'61''60''60'__72 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'61''60''60'__72 v0 v1 v2 v3 v4 v5 v6
  = coe du__'61''60''60'__32 (coe v0) v1 v3 v5 v6
-- Class.Monad.Core._._=≪_
d__'61''8810'__74 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'61''8810'__74 ~v0 v1 = du__'61''8810'__74 v1
du__'61''8810'__74 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'61''8810'__74 v0 = coe du__'61''8810'__42 (coe v0)
-- Class.Monad.Core._._>=>_
d__'62''61''62'__76 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'62''61''62'__76 ~v0 v1 = du__'62''61''62'__76 v1
du__'62''61''62'__76 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'62''61''62'__76 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe du__'62''61''62'__44 (coe v0) v3 v5 v7 v8 v9
-- Class.Monad.Core._._>>_
d__'62''62'__78 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__78 ~v0 v1 = du__'62''62'__78 v1
du__'62''62'__78 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__78 v0 v1 v2 v3 v4 v5 v6
  = coe du__'62''62'__24 (coe v0) v1 v3 v5 v6
-- Class.Monad.Core._._>>=_
d__'62''62''61'__80 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__80 v0 = coe d__'62''62''61'__22 (coe v0)
-- Class.Monad.Core._._≫_
d__'8811'__82 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8811'__82 ~v0 v1 = du__'8811'__82 v1
du__'8811'__82 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8811'__82 v0 = coe du__'8811'__40 (coe v0)
-- Class.Monad.Core._._≫=_
d__'8811''61'__84 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'8811''61'__84 ~v0 v1 = du__'8811''61'__84 v1
du__'8811''61'__84 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'8811''61'__84 v0 = coe du__'8811''61'__38 (coe v0)
-- Class.Monad.Core._.Functor-M
d_Functor'45'M_86 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 -> MAlonzo.Code.Class.Functor.Core.T_Functor_14
d_Functor'45'M_86 ~v0 v1 = du_Functor'45'M_86 v1
du_Functor'45'M_86 ::
  T_Monad_8 -> MAlonzo.Code.Class.Functor.Core.T_Functor_14
du_Functor'45'M_86 v0 = coe du_Functor'45'M_60 (coe v0)
-- Class.Monad.Core._.join
d_join_88 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_join_88 ~v0 v1 = du_join_88 v1
du_join_88 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
du_join_88 v0 v1 v2 v3 = coe du_join_56 (coe v0) v1 v3
-- Class.Monad.Core._.return
d_return_90 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_return_90 v0 = coe d_return_20 (coe v0)
-- Class.Monad.Core._.super
d_super_92 ::
  T_Monad_8 -> MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
d_super_92 v0 = coe d_super_18 (coe v0)
-- Class.Monad.Core._.mapM
d_mapM_102 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> AgdaAny
d_mapM_102 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 v7 = du_mapM_102 v1 v4 v6 v7
du_mapM_102 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) -> [AgdaAny] -> AgdaAny
du_mapM_102 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe d_return_20 v0 v1 erased v3
      (:) v4 v5
        -> coe
             MAlonzo.Code.Class.Applicative.Core.d__'60''42''62'__22
             (d_super_18 (coe v0)) v1 erased v1 erased
             (coe
                MAlonzo.Code.Class.Applicative.Core.d__'60''42''62'__22
                (d_super_18 (coe v0)) v1 erased v1 erased
                (coe
                   MAlonzo.Code.Class.Applicative.Core.d_pure_20 (d_super_18 (coe v0))
                   v1 erased (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22))
                (coe v2 v4))
             (coe du_mapM_102 (coe v0) (coe v1) (coe v2) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Monad.Core._.concatMapM
d_concatMapM_112 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> AgdaAny
d_concatMapM_112 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 v7
  = du_concatMapM_112 v1 v4 v6 v7
du_concatMapM_112 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) -> [AgdaAny] -> AgdaAny
du_concatMapM_112 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
      (MAlonzo.Code.Class.Applicative.Core.d_super_18
         (coe d_super_18 (coe v0)))
      v1 erased v1 erased (coe MAlonzo.Code.Data.List.Base.du_concat_244)
      (coe du_mapM_102 (coe v0) (coe v1) (coe v2) (coe v3))
-- Class.Monad.Core._.forM
d_forM_118 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> (AgdaAny -> AgdaAny) -> AgdaAny
d_forM_118 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 v7 = du_forM_118 v1 v4 v6 v7
du_forM_118 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [AgdaAny] -> (AgdaAny -> AgdaAny) -> AgdaAny
du_forM_118 v0 v1 v2 v3
  = case coe v2 of
      [] -> coe d_return_20 v0 v1 erased v2
      (:) v4 v5
        -> coe
             MAlonzo.Code.Class.Applicative.Core.d__'60''42''62'__22
             (d_super_18 (coe v0)) v1 erased v1 erased
             (coe
                MAlonzo.Code.Class.Applicative.Core.d__'60''42''62'__22
                (d_super_18 (coe v0)) v1 erased v1 erased
                (coe
                   MAlonzo.Code.Class.Applicative.Core.d_pure_20 (d_super_18 (coe v0))
                   v1 erased (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22))
                (coe v3 v4))
             (coe du_forM_118 (coe v0) (coe v1) (coe v5) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Monad.Core._.concatForM
d_concatForM_126 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> (AgdaAny -> AgdaAny) -> AgdaAny
d_concatForM_126 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 v7
  = du_concatForM_126 v1 v4 v6 v7
du_concatForM_126 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [AgdaAny] -> (AgdaAny -> AgdaAny) -> AgdaAny
du_concatForM_126 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
      (MAlonzo.Code.Class.Applicative.Core.d_super_18
         (coe d_super_18 (coe v0)))
      v1 erased v1 erased (coe MAlonzo.Code.Data.List.Base.du_concat_244)
      (coe du_forM_118 (coe v0) (coe v1) (coe v2) (coe v3))
-- Class.Monad.Core._.return⊤
d_return'8868'_132 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_return'8868'_132 ~v0 v1 v2 ~v3 v4 = du_return'8868'_132 v1 v2 v4
du_return'8868'_132 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> AgdaAny -> AgdaAny
du_return'8868'_132 v0 v1 v2
  = coe
      du__'8811'__40 v0 v1 erased () erased v2
      (coe
         d_return_20 v0 () erased
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Class.Monad.Core._.void
d_void_134 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_void_134 ~v0 v1 v2 ~v3 = du_void_134 v1 v2
du_void_134 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> AgdaAny -> AgdaAny
du_void_134 v0 v1 = coe du_return'8868'_132 (coe v0) (coe v1)
-- Class.Monad.Core._.filterM
d_filterM_138 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> AgdaAny
d_filterM_138 ~v0 v1 v2 ~v3 v4 v5 = du_filterM_138 v1 v2 v4 v5
du_filterM_138 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) -> [AgdaAny] -> AgdaAny
du_filterM_138 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe d_return_20 v0 v1 erased v3
      (:) v4 v5
        -> coe
             d__'62''62''61'__22 v0 () erased v1 erased (coe v2 v4)
             (\ v6 ->
                coe
                  MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
                  (MAlonzo.Code.Class.Applicative.Core.d_super_18
                     (coe d_super_18 (coe v0)))
                  v1 erased v1 erased
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe
                        MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v6)
                        (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v4))
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                  (coe du_filterM_138 (coe v0) (coe v1) (coe v2) (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Monad.Core._.traverseM
d_traverseM_150 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> AgdaAny
d_traverseM_150 ~v0 v1 v2 ~v3 v4 ~v5 v6
  = du_traverseM_150 v1 v2 v4 v6
du_traverseM_150 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) -> [AgdaAny] -> AgdaAny
du_traverseM_150 v0 v1 v2 v3
  = coe
      du_'46'extendedlambda0_154 (coe v0) (coe v1) (coe v2) (coe v3)
-- Class.Monad.Core._..extendedlambda0
d_'46'extendedlambda0_154 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> AgdaAny
d_'46'extendedlambda0_154 ~v0 v1 v2 ~v3 v4 ~v5 v6 v7
  = du_'46'extendedlambda0_154 v1 v2 v4 v6 v7
du_'46'extendedlambda0_154 ::
  T_Monad_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) -> [AgdaAny] -> AgdaAny
du_'46'extendedlambda0_154 v0 v1 v2 v3 v4
  = case coe v4 of
      [] -> coe d_return_20 v0 v2 erased v4
      (:) v5 v6
        -> coe
             MAlonzo.Code.Class.Applicative.Core.d__'60''42''62'__22
             (d_super_18 (coe v0)) v2 erased v2 erased
             (coe
                MAlonzo.Code.Class.Applicative.Core.d__'60''42''62'__22
                (d_super_18 (coe v0)) v2 erased v2 erased
                (coe
                   MAlonzo.Code.Class.Applicative.Core.d_pure_20 (d_super_18 (coe v0))
                   v2 erased (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22))
                (coe v3 v5))
             (coe du_traverseM_150 v0 v1 v2 v3 v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Monad.Core.MonadLaws
d_MonadLaws_164 a0 a1 = ()
data T_MonadLaws_164 = C_MonadLaws'46'constructor_36521
-- Class.Monad.Core.MonadLaws.>>=-identityˡ
d_'62''62''61''45'identity'737'_210 ::
  T_MonadLaws_164 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61''45'identity'737'_210 = erased
-- Class.Monad.Core.MonadLaws.>>=-identityʳ
d_'62''62''61''45'identity'691'_216 ::
  T_MonadLaws_164 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61''45'identity'691'_216 = erased
-- Class.Monad.Core.MonadLaws.>>=-assoc
d_'62''62''61''45'assoc_232 ::
  T_MonadLaws_164 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61''45'assoc_232 = erased
-- Class.Monad.Core._.>>=-assoc
d_'62''62''61''45'assoc_236 ::
  T_MonadLaws_164 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61''45'assoc_236 = erased
-- Class.Monad.Core._.>>=-identityʳ
d_'62''62''61''45'identity'691'_238 ::
  T_MonadLaws_164 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61''45'identity'691'_238 = erased
-- Class.Monad.Core._.>>=-identityˡ
d_'62''62''61''45'identity'737'_240 ::
  T_MonadLaws_164 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''62''61''45'identity'737'_240 = erased
-- Class.Monad.Core.Monad₀
d_Monad'8320'_244 a0 = ()
data T_Monad'8320'_244
  = C_Monad'8320''46'constructor_36969 T_Monad_8
                                       MAlonzo.Code.Class.Applicative.Core.T_Applicative'8320'_84
-- Class.Monad.Core.Monad₀.isMonad
d_isMonad_252 :: T_Monad'8320'_244 -> T_Monad_8
d_isMonad_252 v0
  = case coe v0 of
      C_Monad'8320''46'constructor_36969 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Monad.Core.Monad₀.isApplicative₀
d_isApplicative'8320'_254 ::
  T_Monad'8320'_244 ->
  MAlonzo.Code.Class.Applicative.Core.T_Applicative'8320'_84
d_isApplicative'8320'_254 v0
  = case coe v0 of
      C_Monad'8320''46'constructor_36969 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Monad.Core.mkMonad₀
d_mkMonad'8320'_258 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Class.Applicative.Core.T_Applicative'8320'_84 ->
  T_Monad'8320'_244
d_mkMonad'8320'_258 ~v0 v1 v2 = du_mkMonad'8320'_258 v1 v2
du_mkMonad'8320'_258 ::
  T_Monad_8 ->
  MAlonzo.Code.Class.Applicative.Core.T_Applicative'8320'_84 ->
  T_Monad'8320'_244
du_mkMonad'8320'_258 v0 v1
  = coe C_Monad'8320''46'constructor_36969 (coe v0) (coe v1)
-- Class.Monad.Core.Monad⁺
d_Monad'8314'_262 a0 = ()
data T_Monad'8314'_262
  = C_Monad'8314''46'constructor_37343 T_Monad_8
                                       MAlonzo.Code.Class.Applicative.Core.T_Alternative_104
-- Class.Monad.Core.Monad⁺.isMonad
d_isMonad_270 :: T_Monad'8314'_262 -> T_Monad_8
d_isMonad_270 v0
  = case coe v0 of
      C_Monad'8314''46'constructor_37343 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Monad.Core.Monad⁺.isAlternative
d_isAlternative_272 ::
  T_Monad'8314'_262 ->
  MAlonzo.Code.Class.Applicative.Core.T_Alternative_104
d_isAlternative_272 v0
  = case coe v0 of
      C_Monad'8314''46'constructor_37343 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Monad.Core.mkMonad⁺
d_mkMonad'8314'_276 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  T_Monad_8 ->
  MAlonzo.Code.Class.Applicative.Core.T_Alternative_104 ->
  T_Monad'8314'_262
d_mkMonad'8314'_276 ~v0 v1 v2 = du_mkMonad'8314'_276 v1 v2
du_mkMonad'8314'_276 ::
  T_Monad_8 ->
  MAlonzo.Code.Class.Applicative.Core.T_Alternative_104 ->
  T_Monad'8314'_262
du_mkMonad'8314'_276 v0 v1
  = coe C_Monad'8314''46'constructor_37343 (coe v0) (coe v1)
