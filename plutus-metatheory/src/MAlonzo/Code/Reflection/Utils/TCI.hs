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

module MAlonzo.Code.Reflection.Utils.TCI where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Applicative.Core
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Class.DecEq.Instances
import qualified MAlonzo.Code.Class.Functor.Core
import qualified MAlonzo.Code.Class.Functor.Instances
import qualified MAlonzo.Code.Class.Monad.Core
import qualified MAlonzo.Code.Class.MonadError
import qualified MAlonzo.Code.Class.MonadReader
import qualified MAlonzo.Code.Class.MonadTC
import qualified MAlonzo.Code.Class.Traversable.Core
import qualified MAlonzo.Code.Class.Traversable.Instances
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.NonEmpty.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Meta.Prelude
import qualified MAlonzo.Code.Reflection.Debug
import qualified MAlonzo.Code.Reflection.Utils.Core
import qualified MAlonzo.Code.Reflection.Utils.Metas
import qualified MAlonzo.Code.Reflection.Utils.Substitute
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Reflection.Utils.TCI.fresh-level
d_fresh'45'level_18 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny
d_fresh'45'level_18 ~v0 v1 ~v2 ~v3 v4 = du_fresh'45'level_18 v1 v4
du_fresh'45'level_18 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny
du_fresh'45'level_18 v0 v1
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased
      (coe
         MAlonzo.Code.Class.MonadTC.du_newMeta_392 v1
         (coe
            MAlonzo.Code.Agda.Builtin.Reflection.C_def_184
            (coe
               (MAlonzo.RTE.QName
                  (18 :: Integer) (10880583612240331187 :: Integer)
                  "Agda.Primitive.Level"
                  (MAlonzo.RTE.Fixity MAlonzo.RTE.NonAssoc MAlonzo.RTE.Unrelated)))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      (coe MAlonzo.Code.Class.MonadTC.d_unquoteTC_146 v1 () erased)
-- Reflection.Utils.TCI.withHole
d_withHole_20 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  (MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny) ->
  AgdaAny
d_withHole_20 ~v0 v1 ~v2 ~v3 v4 v5 v6 = du_withHole_20 v1 v4 v5 v6
du_withHole_20 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  (MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny) ->
  AgdaAny
du_withHole_20 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (coe MAlonzo.Code.Class.MonadTC.du_newMeta_392 v1 v2)
      (\ v4 ->
         coe
           MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
           (coe ()) (coe v3 v4)
           (coe MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased v4))
-- Reflection.Utils.TCI.apply
d_apply_28 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
d_apply_28 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_apply_28 v1 v2 v3 v4 v5 v6 v7
du_apply_28 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
du_apply_28 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      []
        -> coe
             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v5))
      (:) v7 v8
        -> coe
             MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
             erased (coe MAlonzo.Code.Class.MonadTC.d_reduce_142 v3 v4)
             (\ v9 ->
                coe
                  MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                  erased
                  (coe
                     du_apply'8321'_46 (coe v0) (coe v1) (coe v3) (coe v9) (coe v5)
                     (coe v7))
                  (coe
                     du_'46'extendedlambda0_100 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe v8)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.TCI._.apply₁
d_apply'8321'_46 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 -> AgdaAny
d_apply'8321'_46 ~v0 v1 v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_apply'8321'_46 v1 v2 v4 v9 v10 v11
du_apply'8321'_46 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 -> AgdaAny
du_apply'8321'_46 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Class.MonadTC.du_error1_724 (coe v1) (coe ())
              (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
              (coe ("apply: not a \928-type" :: Data.Text.Text)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Reflection.C_pi_202 v7 v8
           -> case coe v7 of
                MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v9 v10
                  -> case coe v9 of
                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82 v11 v12
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v13 v14
                                -> coe
                                     MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased
                                     () erased (coe du_fresh'45'level_18 (coe v0) (coe v2))
                                     (\ v15 ->
                                        coe
                                          MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 ()
                                          erased () erased
                                          (coe du_fresh'45'level_18 (coe v0) (coe v2))
                                          (\ v16 ->
                                             coe
                                               MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0
                                               () erased () erased
                                               (coe
                                                  MAlonzo.Code.Class.MonadTC.d_unquoteTC_146 v2 ()
                                                  erased v10)
                                               (\ v17 ->
                                                  coe
                                                    MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22
                                                    v0 () erased () erased
                                                    (coe
                                                       MAlonzo.Code.Class.MonadTC.d_unquoteTC_146 v2
                                                       () erased
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Reflection.C_lam_190
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                                          (coe v8)))
                                                    (\ v18 ->
                                                       coe
                                                         MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22
                                                         v0 v15 erased () erased
                                                         (coe
                                                            MAlonzo.Code.Class.MonadTC.d_unquoteTC_146
                                                            v2 v15 erased v14)
                                                         (\ v19 ->
                                                            coe
                                                              MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22
                                                              v0 () erased () erased
                                                              (coe
                                                                 MAlonzo.Code.Class.MonadTC.d_quoteTC_144
                                                                 v2 () erased (coe v18 v19))
                                                              (\ v20 ->
                                                                 seq
                                                                   (coe v11)
                                                                   (coe
                                                                      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22
                                                                      v0 () erased () erased
                                                                      (coe
                                                                         MAlonzo.Code.Class.MonadTC.d_unquoteTC_146
                                                                         v2 () erased v4)
                                                                      (\ v21 ->
                                                                         coe
                                                                           MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
                                                                           (MAlonzo.Code.Class.Applicative.Core.d_super_18
                                                                              (coe
                                                                                 MAlonzo.Code.Class.Monad.Core.d_super_18
                                                                                 (coe v0)))
                                                                           () erased () erased
                                                                           (\ v22 ->
                                                                              coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                (coe v20) (coe v22))
                                                                           (coe
                                                                              MAlonzo.Code.Class.MonadTC.d_quoteTC_144
                                                                              v2 v16 erased
                                                                              (coe v21 v19))))))))))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 v7 v8
           -> coe MAlonzo.Code.Class.MonadTC.d_blockOnMeta_164 v2 () erased v7
         _ -> coe v6)
-- Reflection.Utils.TCI._..extendedlambda0
d_'46'extendedlambda0_100 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_'46'extendedlambda0_100 ~v0 v1 v2 v3 v4 ~v5 ~v6 ~v7 v8 ~v9 v10
  = du_'46'extendedlambda0_100 v1 v2 v3 v4 v8 v10
du_'46'extendedlambda0_100 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_'46'extendedlambda0_100 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> coe
             du_apply_28 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v7)
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.TCI._-∙-_
d__'45''8729''45'__106 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d__'45''8729''45'__106 ~v0 v1 v2 v3 v4 v5 v6
  = du__'45''8729''45'__106 v1 v2 v3 v4 v5 v6
du__'45''8729''45'__106 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du__'45''8729''45'__106 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (coe MAlonzo.Code.Class.MonadTC.d_inferType_136 v3 v4)
      (\ v6 ->
         coe
           MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
           (MAlonzo.Code.Class.Applicative.Core.d_super_18
              (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
           () erased () erased
           (\ v7 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v7))
           (coe
              du_apply_28 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) (coe v4)
              (coe
                 MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                 (coe
                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                    (coe
                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                       (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                          (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                          (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                    (coe v5)))))
-- Reflection.Utils.TCI._-∗-_
d__'45''8727''45'__114 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154] -> AgdaAny
d__'45''8727''45'__114 ~v0 v1 v2 v3 v4 v5 v6
  = du__'45''8727''45'__114 v1 v2 v3 v4 v5 v6
du__'45''8727''45'__114 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154] -> AgdaAny
du__'45''8727''45'__114 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      [] -> coe MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased v4
      (:) v6 v7
        -> coe
             MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
             erased
             (coe
                du__'45''8729''45'__106 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v6))
             (\ v8 ->
                coe
                  du__'45''8727''45'__114 (coe v0) (coe v1) (coe v2) (coe v3)
                  (coe v8) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.TCI.instantiate
d_instantiate_126 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_instantiate_126 ~v0 v1 ~v2 ~v3 v4 = du_instantiate_126 v1 v4
du_instantiate_126 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_instantiate_126 v0 v1
  = coe
      MAlonzo.Code.Class.Monad.Core.du__'62''61''62'__44 (coe v0)
      (coe ()) (coe ())
      (coe MAlonzo.Code.Class.MonadTC.d_reduce_142 (coe v1))
      (coe MAlonzo.Code.Class.MonadTC.d_normalise_140 (coe v1))
-- Reflection.Utils.TCI.ensureNoMetas
d_ensureNoMetas_128 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_ensureNoMetas_128 ~v0 v1 v2 v3 v4
  = du_ensureNoMetas_128 v1 v2 v3 v4
du_ensureNoMetas_128 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_ensureNoMetas_128 v0 v1 v2 v3
  = coe
      du_'46'extendedlambda0_166 (coe v0) (coe v1) (coe v2) (coe v3)
-- Reflection.Utils.TCI._.noMetaArg
d_noMetaArg_134 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 -> AgdaAny
d_noMetaArg_134 ~v0 v1 v2 v3 v4 v5
  = du_noMetaArg_134 v1 v2 v3 v4 v5
du_noMetaArg_134 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 -> AgdaAny
du_noMetaArg_134 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v5 v6
        -> coe du_ensureNoMetas_128 v0 v1 v2 v3 v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.TCI._.noMetaArgs
d_noMetaArgs_138 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
d_noMetaArgs_138 ~v0 v1 v2 v3 v4 v5
  = du_noMetaArgs_138 v1 v2 v3 v4 v5
du_noMetaArgs_138 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
du_noMetaArgs_138 v0 v1 v2 v3 v4
  = case coe v4 of
      []
        -> coe
             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (:) v5 v6
        -> coe
             MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
             (coe ())
             (coe du_noMetaArg_134 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
             (coe
                du_noMetaArgs_138 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.TCI._.noMetaClause
d_noMetaClause_144 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160 -> AgdaAny
d_noMetaClause_144 ~v0 v1 v2 v3 v4 v5
  = du_noMetaClause_144 v1 v2 v3 v4 v5
du_noMetaClause_144 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160 -> AgdaAny
du_noMetaClause_144 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272 v5 v6 v7
        -> coe du_ensureNoMetas_128 v0 v1 v2 v3 v7
      MAlonzo.Code.Agda.Builtin.Reflection.C_absurd'45'clause_278 v5 v6
        -> coe
             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.TCI._.noMetaClauses
d_noMetaClauses_152 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
d_noMetaClauses_152 ~v0 v1 v2 v3 v4 v5
  = du_noMetaClauses_152 v1 v2 v3 v4 v5
du_noMetaClauses_152 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
du_noMetaClauses_152 v0 v1 v2 v3 v4
  = case coe v4 of
      []
        -> coe
             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (:) v5 v6
        -> coe
             MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
             (coe ())
             (coe
                du_noMetaClause_144 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
             (coe
                du_noMetaClauses_152 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.TCI._.noMetaAbs
d_noMetaAbs_158 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 -> AgdaAny
d_noMetaAbs_158 ~v0 v1 v2 v3 v4 v5
  = du_noMetaAbs_158 v1 v2 v3 v4 v5
du_noMetaAbs_158 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 -> AgdaAny
du_noMetaAbs_158 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v5 v6
        -> coe du_ensureNoMetas_128 v0 v1 v2 v3 v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.TCI._.noMetaSort
d_noMetaSort_162 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Sort_156 -> AgdaAny
d_noMetaSort_162 ~v0 v1 v2 v3 v4 v5
  = du_noMetaSort_162 v1 v2 v3 v4 v5
du_noMetaSort_162 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Sort_156 -> AgdaAny
du_noMetaSort_162 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Reflection.C_set_220 v6
           -> coe du_ensureNoMetas_128 v0 v1 v2 v3 v6
         _ -> coe v5)
-- Reflection.Utils.TCI._..extendedlambda0
d_'46'extendedlambda0_166 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_'46'extendedlambda0_166 ~v0 v1 v2 v3 v4 v5
  = du_'46'extendedlambda0_166 v1 v2 v3 v4 v5
du_'46'extendedlambda0_166 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_'46'extendedlambda0_166 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_var_172 v5 v6
        -> coe
             du_noMetaArgs_138 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6)
      MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 v5 v6
        -> coe
             du_noMetaArgs_138 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6)
      MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 v5 v6
        -> coe
             du_noMetaArgs_138 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6)
      MAlonzo.Code.Agda.Builtin.Reflection.C_lam_190 v5 v6
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v7 v8
               -> coe du_ensureNoMetas_128 v0 v1 v2 v3 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196 v5 v6
        -> coe
             MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
             (coe ())
             (coe
                du_noMetaClauses_152 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
             (coe
                du_noMetaArgs_138 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
      MAlonzo.Code.Agda.Builtin.Reflection.C_pi_202 v5 v6
        -> coe
             MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
             (coe ())
             (coe du_noMetaArg_134 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
             (coe du_noMetaAbs_158 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
      MAlonzo.Code.Agda.Builtin.Reflection.C_agda'45'sort_206 v5
        -> coe
             du_noMetaSort_162 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
      MAlonzo.Code.Agda.Builtin.Reflection.C_lit_210 v5
        -> coe
             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 v5 v6
        -> coe MAlonzo.Code.Class.MonadTC.d_blockOnMeta_164 v3 () erased v5
      MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216
        -> coe
             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.TCI.NewMeta.unifyStrict
d_unifyStrict_200 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_unifyStrict_200 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_unifyStrict_200 v1 v3 v4 v5 v6
du_unifyStrict_200 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_unifyStrict_200 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> coe
             MAlonzo.Code.Class.MonadTC.du_withAppendDebugPath_590 (coe v1)
             (coe ()) (coe ("unifyStrict" :: Data.Text.Text))
             (coe
                MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
                (coe ())
                (coe
                   MAlonzo.Code.Class.MonadTC.du_debugLog_570 (coe v0) (coe v2)
                   (coe v1)
                   (coe
                      MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v5)
                      (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                      (coe
                         MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                         (coe (" :=? " :: Data.Text.Text))
                         (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                         (coe
                            MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v4)
                            (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                (coe
                   MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                   erased (coe MAlonzo.Code.Class.MonadTC.du_newMeta_392 v2 v6)
                   (\ v7 ->
                      coe
                        MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
                        (coe ())
                        (coe
                           MAlonzo.Code.Class.MonadTC.du_noConstraints_604 v1 ()
                           (coe
                              MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
                              (coe ()) (coe MAlonzo.Code.Class.MonadTC.d_unify_132 v2 v7 v4)
                              (coe MAlonzo.Code.Class.MonadTC.d_unify_132 v2 v5 v7)))
                        (coe
                           MAlonzo.Code.Class.MonadTC.du_debugLog_570 (coe v0) (coe v2)
                           (coe v1)
                           (coe
                              MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v5)
                              (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                              (coe
                                 MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                 (coe (" :=  " :: Data.Text.Text))
                                 (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                 (coe
                                    MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v4)
                                    (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.TCI.printTerm
d_printTerm_210 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_printTerm_210 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_printTerm_210 v1 v3 v4 v5 v6
du_printTerm_210 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_printTerm_210 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (coe MAlonzo.Code.Class.MonadTC.d_inferType_136 v2 v4)
      (\ v5 ->
         coe
           MAlonzo.Code.Class.MonadTC.du_debugLog_570 (coe v0) (coe v2)
           (coe v1)
           (coe
              MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v3)
              (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
              (coe
                 MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                 (coe (": {" :: Data.Text.Text))
                 (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                 (coe
                    MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v5)
                    (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                    (coe
                       MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                       (coe (" \8715 " :: Data.Text.Text))
                       (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                       (coe
                          MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v4)
                          (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                          (coe
                             MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                             (coe ("}\n" :: Data.Text.Text))
                             (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
-- Reflection.Utils.TCI.NoMeta.unifyStrict
d_unifyStrict_220 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_unifyStrict_220 ~v0 v1 v2 v3 v4 v5 v6
  = du_unifyStrict_220 v1 v2 v3 v4 v5 v6
du_unifyStrict_220 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_unifyStrict_220 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> coe
             MAlonzo.Code.Class.MonadTC.du_withAppendDebugPath_590 (coe v2)
             (coe ()) (coe ("unifyStrictNoMeta" :: Data.Text.Text))
             (coe
                MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
                (coe ())
                (coe
                   MAlonzo.Code.Class.MonadTC.du_debugLog_570 (coe v0) (coe v3)
                   (coe v2)
                   (coe
                      MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                      (coe
                         ("\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\8212\nx"
                          ::
                          Data.Text.Text))
                      (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                      (coe
                         MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v5)
                         (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                (coe
                   MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
                   (coe ()) (coe MAlonzo.Code.Class.MonadTC.d_unify_132 v3 v6 v5)
                   (coe
                      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                      erased (coe MAlonzo.Code.Class.MonadTC.d_normalise_140 v3 v6)
                      (\ v8 ->
                         coe
                           MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
                           (coe ())
                           (coe
                              du_printTerm_210 (coe v0) (coe v2) (coe v3)
                              (coe ("hole\8242" :: Data.Text.Text)) (coe v8))
                           (coe
                              MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
                              (coe ()) (coe du_ensureNoMetas_128 v0 v1 v2 v3 v8)
                              (coe
                                 MAlonzo.Code.Class.MonadTC.du_debugLog1_728 (coe v0) (coe v3)
                                 (coe v2)
                                 (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                 (coe ("No metas found :)\n" :: Data.Text.Text))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.TCI.unifyStricts
d_unifyStricts_230 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154] -> AgdaAny
d_unifyStricts_230 ~v0 v1 v2 v3 v4 v5 v6
  = du_unifyStricts_230 v1 v2 v3 v4 v5 v6
du_unifyStricts_230 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154] -> AgdaAny
du_unifyStricts_230 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.NonEmpty.Base.du_foldl'8321'_174
      (\ v6 v7 ->
         coe
           MAlonzo.Code.Class.MonadError.d_catch_28 v1 () erased v6
           (\ v8 -> v7))
      (coe
         MAlonzo.Code.Data.List.NonEmpty.Base.du__'8759''691'__284
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe du_unifyStrict_200 (coe v0) (coe v2) (coe v3) (coe v4))
            (coe v5))
         (coe
            MAlonzo.Code.Class.MonadTC.du_error1_724 (coe v1) (coe ())
            (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
            (coe ("\8709" :: Data.Text.Text))))
-- Reflection.Utils.TCI.compatible?
d_compatible'63'_242 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_compatible'63'_242 ~v0 v1 v2 ~v3 v4 v5 v6
  = du_compatible'63'_242 v1 v2 v4 v5 v6
du_compatible'63'_242 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_compatible'63'_242 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased
      (coe
         MAlonzo.Code.Class.MonadTC.d_runSpeculative_172 v2 () erased
         (coe
            MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
            (MAlonzo.Code.Class.Applicative.Core.d_super_18
               (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
            () erased () erased
            (\ v5 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
            (coe
               MAlonzo.Code.Class.MonadError.d_catch_28 v1 () erased
               (coe
                  MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
                  (coe ())
                  (coe
                     MAlonzo.Code.Class.MonadTC.d_unify_132 v2
                     (coe
                        MAlonzo.Code.Reflection.Utils.Substitute.d_varsToUnknown_248 v3)
                     (coe
                        MAlonzo.Code.Reflection.Utils.Substitute.d_varsToUnknown_248 v4))
                  (coe
                     MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)))
               (\ v5 ->
                  coe
                    MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)))))
      (coe MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased)
-- Reflection.Utils.TCI.logTelescope
d_logTelescope_254 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_logTelescope_254 ~v0 v1 v2 v3 v4 v5
  = du_logTelescope_254 v1 v2 v3 v4 v5
du_logTelescope_254 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
du_logTelescope_254 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.MonadTC.du_withAppendDebugPath_590 (coe v2)
      (coe ()) (coe ("context" :: Data.Text.Text))
      (coe
         MAlonzo.Code.Class.MonadError.d_catch_28 v1 () erased
         (coe
            du_helper_262 (coe v0) (coe v2) (coe v3)
            (coe MAlonzo.Code.Data.List.Base.du_length_268 v4) (coe v4))
         (\ v5 ->
            coe
              MAlonzo.Code.Class.MonadTC.du_debugLog1_728 (coe v0) (coe v3)
              (coe v2)
              (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
              (coe ("Error while printing the context!" :: Data.Text.Text))))
-- Reflection.Utils.TCI._.helper
d_helper_262 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_helper_262 ~v0 v1 ~v2 v3 v4 ~v5 v6 v7
  = du_helper_262 v1 v3 v4 v6 v7
du_helper_262 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
du_helper_262 v0 v1 v2 v3 v4
  = case coe v4 of
      []
        -> coe
             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (:) v5 v6
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v9 v10
                      -> coe
                           MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
                           (coe ())
                           (coe
                              MAlonzo.Code.Class.MonadTC.du_debugLog_570 (coe v0) (coe v2)
                              (coe v1)
                              (coe
                                 MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                 (coe ("  " :: Data.Text.Text))
                                 (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                 (coe
                                    MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                    (case coe v7 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                         -> case coe v11 of
                                              l | (==) l ("" :: Data.Text.Text) ->
                                                  coe ("_" :: Data.Text.Text)
                                              _ -> coe v11
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> coe ("?" :: Data.Text.Text)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                    (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                    (coe
                                       MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                       (coe (" : " :: Data.Text.Text))
                                       (coe
                                          MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                       (coe
                                          MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                          (coe
                                             MAlonzo.Code.Reflection.Utils.Substitute.d_mapVars_246
                                             (\ v11 ->
                                                coe
                                                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v11
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v3
                                                     (addInt
                                                        (coe (1 :: Integer))
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_length_268
                                                           v6))))
                                             v10)
                                          (coe
                                             MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                           (coe
                              MAlonzo.Code.Class.MonadTC.du_extendContext_668 v1 ()
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                      -> case coe v11 of
                                           l | (==) l ("" :: Data.Text.Text) ->
                                               coe ("_" :: Data.Text.Text)
                                           _ -> coe v11
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> coe ("?" :: Data.Text.Text)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                 (coe v8))
                              (coe du_helper_262 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.TCI.logContext
d_logContext_286 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_logContext_286 ~v0 v1 v2 v3 v4 v5
  = du_logContext_286 v1 v2 v3 v4 v5
du_logContext_286 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
du_logContext_286 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.MonadTC.du_withAppendDebugPath_590 (coe v2)
      (coe ()) (coe ("context" :: Data.Text.Text))
      (coe
         MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
         (coe ())
         (coe
            MAlonzo.Code.Class.MonadTC.du_debugLog1_728 (coe v0) (coe v3)
            (coe v2)
            (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
            (coe ("Context:" :: Data.Text.Text)))
         (coe
            MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
            (coe ())
            (coe
               MAlonzo.Code.Class.MonadError.d_catch_28 v1 () erased
               (coe
                  du_helper_294 (coe v0) (coe v2) (coe v3)
                  (coe MAlonzo.Code.Data.List.Base.du_length_268 v4) (coe v4))
               (\ v5 ->
                  coe
                    MAlonzo.Code.Class.MonadTC.du_debugLog1_728 (coe v0) (coe v3)
                    (coe v2)
                    (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                    (coe ("Error while printing the context!" :: Data.Text.Text))))
            (coe
               MAlonzo.Code.Class.MonadError.d_catch_28 v1 () erased
               (coe
                  MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                  erased
                  (coe
                     MAlonzo.Code.Class.MonadTC.du_goalTy_744 (coe v0) (coe v3)
                     (coe v2))
                  (\ v5 ->
                     coe
                       MAlonzo.Code.Class.MonadTC.du_debugLog_570 (coe v0) (coe v3)
                       (coe v2)
                       (coe
                          MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                          (coe ("  \8866 " :: Data.Text.Text))
                          (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                          (coe
                             MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v5)
                             (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
               (\ v5 ->
                  coe
                    MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                    erased
                    (coe
                       MAlonzo.Code.Class.MonadReader.du_reader_46 (coe ()) (coe v0)
                       (coe v2) (coe ())
                       (coe (\ v6 -> MAlonzo.Code.Class.MonadTC.d_goal_54 (coe v6))))
                    (\ v6 ->
                       let v7
                             = coe
                                 MAlonzo.Code.Class.MonadTC.du_error1_724 (coe v1) (coe ())
                                 (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                 (coe ("Bug in logContext!" :: Data.Text.Text)) in
                       coe
                         (case coe v6 of
                            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                              -> coe
                                   MAlonzo.Code.Class.MonadTC.du_debugLog_570 (coe v0) (coe v3)
                                   (coe v2)
                                   (coe
                                      MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                      (coe
                                         ("Error while infering the goal type! Goal: "
                                          ::
                                          Data.Text.Text))
                                      (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                      (coe
                                         MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v8)
                                         (coe
                                            MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                            _ -> coe v7))))))
-- Reflection.Utils.TCI._.helper
d_helper_294 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_helper_294 ~v0 v1 ~v2 v3 v4 ~v5 v6 v7
  = du_helper_294 v1 v3 v4 v6 v7
du_helper_294 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  Integer -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
du_helper_294 v0 v1 v2 v3 v4
  = case coe v4 of
      []
        -> coe
             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (:) v5 v6
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v9 v10
                      -> coe
                           MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
                           (coe ())
                           (coe du_helper_294 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
                           (coe
                              MAlonzo.Code.Class.MonadTC.du_debugLog_570 (coe v0) (coe v2)
                              (coe v1)
                              (coe
                                 MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                 (coe ("  " :: Data.Text.Text))
                                 (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                 (coe
                                    MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Reflection.C_var_172
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v3
                                          (addInt
                                             (coe (1 :: Integer))
                                             (coe MAlonzo.Code.Data.List.Base.du_length_268 v6)))
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                    (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                                    (coe
                                       MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                       (coe (" : " :: Data.Text.Text))
                                       (coe
                                          MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                       (coe
                                          MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                          (coe
                                             MAlonzo.Code.Reflection.Utils.Substitute.d_mapVars_246
                                             (\ v11 ->
                                                addInt
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v3
                                                     (coe
                                                        MAlonzo.Code.Data.List.Base.du_length_268
                                                        v6))
                                                  (coe v11))
                                             v10)
                                          (coe
                                             MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.TCI.logCurrentContext
d_logCurrentContext_316 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny
d_logCurrentContext_316 ~v0 v1 v2 v3 v4
  = du_logCurrentContext_316 v1 v2 v3 v4
du_logCurrentContext_316 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny
du_logCurrentContext_316 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.MonadTC.du_markDontFail_736 (coe v0) (coe v1)
      (coe v3) (coe v2) (coe ())
      (coe ("logCurrentContext" :: Data.Text.Text))
      (coe
         MAlonzo.Code.Class.Monad.Core.du__'61''60''60'__32 (coe v0)
         (coe ()) (coe ())
         (coe du_logContext_286 (coe v0) (coe v1) (coe v2) (coe v3))
         (coe
            MAlonzo.Code.Class.MonadTC.du_getContext_678 (coe v0) (coe v2)))
-- Reflection.Utils.TCI.inDebugPath
d_inDebugPath_318 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
d_inDebugPath_318 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7 v8
  = du_inDebugPath_318 v1 v3 v4 v5 v7 v8
du_inDebugPath_318 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
du_inDebugPath_318 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Class.MonadTC.du_withAppendDebugPath_590 (coe v1)
      (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
         (coe v3)
         (coe
            MAlonzo.Code.Class.MonadTC.du_debugLog_570 (coe v0) (coe v2)
            (coe v1)
            (coe
               MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
               (coe
                  MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                  (coe ("*****" :: Data.Text.Text))
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'60''43''62'__50 (coe v4)
                     (coe ("*****" :: Data.Text.Text))))
               (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
         (coe v5))
-- Reflection.Utils.TCI.viewAndReduceTy
d_viewAndReduceTy_324 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_viewAndReduceTy_324 ~v0 v1 ~v2 v3 v4 v5
  = du_viewAndReduceTy_324 v1 v3 v4 v5
du_viewAndReduceTy_324 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_viewAndReduceTy_324 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.du__'61''60''60'__32 (coe v0)
      (coe ()) (coe ())
      (coe du_helper_332 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe
         MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
         (MAlonzo.Code.Class.Applicative.Core.d_super_18
            (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
         () erased () erased
         (\ v4 ->
            coe
              MAlonzo.Code.Data.List.Base.du_length_268
              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe MAlonzo.Code.Reflection.Utils.Core.d_viewTy_22 (coe v4))))
         (coe MAlonzo.Code.Class.MonadTC.d_normalise_140 v2 v3))
-- Reflection.Utils.TCI._.helper
d_helper_332 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  Integer -> AgdaAny
d_helper_332 ~v0 v1 ~v2 v3 v4 ~v5 v6 v7
  = du_helper_332 v1 v3 v4 v6 v7
du_helper_332 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  Integer -> AgdaAny
du_helper_332 v0 v1 v2 v3 v4
  = case coe v4 of
      0 -> coe
             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
             (MAlonzo.Code.Reflection.Utils.Core.d_viewTy_22 (coe v3))
      _ -> let v5 = subInt (coe v4) (coe (1 :: Integer)) in
           coe
             (let v6
                    = MAlonzo.Code.Reflection.Utils.Core.d_viewTy_22 (coe v3) in
              coe
                (case coe v6 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                     -> coe
                          MAlonzo.Code.Class.MonadTC.du_extendContext''_702 (coe v1) (coe ())
                          (coe
                             MAlonzo.Code.Data.List.Base.du_map_22
                             (coe
                                (\ v9 ->
                                   case coe v9 of
                                     MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v10 v11
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                            (coe v11)
                                     _ -> MAlonzo.RTE.mazUnreachableError))
                             (coe v7))
                          (coe
                             MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                             erased (coe MAlonzo.Code.Class.MonadTC.d_reduce_142 v2 v8)
                             (\ v9 ->
                                coe
                                  MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                                  erased
                                  (coe du_helper_332 (coe v0) (coe v1) (coe v2) (coe v9) (coe v5))
                                  (\ v10 ->
                                     case coe v10 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                         -> coe
                                              MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                    (coe v7) (coe v11))
                                                 (coe v12))
                                       _ -> MAlonzo.RTE.mazUnreachableError)))
                   _ -> MAlonzo.RTE.mazUnreachableError))
-- Reflection.Utils.TCI.getType'
d_getType''_366 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
d_getType''_366 ~v0 v1 ~v2 v3 v4 v5 = du_getType''_366 v1 v3 v4 v5
du_getType''_366 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
du_getType''_366 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.du__'61''60''60'__32 (coe v0)
      (coe ()) (coe ())
      (coe du_viewAndReduceTy_324 (coe v0) (coe v1) (coe v2))
      (coe MAlonzo.Code.Class.MonadTC.d_getType_160 v2 v3)
-- Reflection.Utils.TCI.getTypeDB
d_getTypeDB_370 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> Integer -> AgdaAny
d_getTypeDB_370 ~v0 v1 ~v2 v3 v4 v5 = du_getTypeDB_370 v1 v3 v4 v5
du_getTypeDB_370 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> Integer -> AgdaAny
du_getTypeDB_370 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.du__'61''60''60'__32 (coe v0)
      (coe ()) (coe ())
      (coe du_viewAndReduceTy_324 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Class.MonadTC.d_inferType_136 v2
         (coe
            MAlonzo.Code.Agda.Builtin.Reflection.C_var_172 (coe v3)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Reflection.Utils.TCI.getDataDef
d_getDataDef_374 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
d_getDataDef_374 ~v0 v1 v2 v3 v4 v5
  = du_getDataDef_374 v1 v2 v3 v4 v5
du_getDataDef_374 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
du_getDataDef_374 v0 v1 v2 v3 v4
  = coe
      du_inDebugPath_318 (coe v0) (coe v2) (coe v3) (coe ())
      (coe ("getDataDef" :: Data.Text.Text))
      (coe
         MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
         (coe ())
         (coe
            MAlonzo.Code.Class.MonadTC.du_debugLog_570 (coe v0) (coe v3)
            (coe v2)
            (coe
               MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
               (coe ("Find details for datatype: " :: Data.Text.Text))
               (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
               (coe
                  MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v4)
                  (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Name_22)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
         (coe
            MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
            erased (coe MAlonzo.Code.Class.MonadTC.d_getDefinition_162 v3 v4)
            (\ v5 ->
               let v6
                     = coe
                         MAlonzo.Code.Class.MonadTC.du_error1_724 (coe v1) (coe ())
                         (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                         (coe ("Not a data definition!" :: Data.Text.Text)) in
               coe
                 (case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'type_290 v7 v8
                      -> coe
                           MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
                           (coe ())
                           (coe
                              MAlonzo.Code.Class.MonadTC.du_debugLog'7504'_578 (coe v0) (coe v3)
                              (coe v2)
                              (coe
                                 MAlonzo.Code.Class.MonadTC.du__'8759''7496''7504'__540 (coe v0)
                                 (coe ("Constructor names: " :: Data.Text.Text))
                                 (coe
                                    MAlonzo.Code.Class.MonadTC.du_IsMErrorPart'45'String_526
                                    (coe v0))
                                 (coe
                                    MAlonzo.Code.Class.MonadTC.du__'8759''7496''7504'__540 (coe v0)
                                    (coe
                                       MAlonzo.Code.Class.MonadTC.du__'7515'_550 (coe v0) (coe v3)
                                       (coe ()) (coe v8))
                                    (coe
                                       MAlonzo.Code.Class.MonadTC.du_IsMErrorPart'45'MErrorPartWrap_532)
                                    (coe
                                       MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                           (coe
                              MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                              erased
                              (coe
                                 MAlonzo.Code.Class.Traversable.Core.du_traverse_44
                                 (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_92)
                                 (coe
                                    MAlonzo.Code.Class.Traversable.Instances.d_TraversableM'45'List_28)
                                 (coe ()) (coe ()) (coe v0)
                                 (coe
                                    (\ v9 ->
                                       coe
                                         MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
                                         (MAlonzo.Code.Class.Applicative.Core.d_super_18
                                            (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
                                         () erased () erased
                                         (\ v10 ->
                                            coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                              (coe v10))
                                         (coe
                                            du_getType''_366 (coe v0) (coe v2) (coe v3) (coe v9))))
                                 (coe v8))
                              (\ v9 ->
                                 coe
                                   MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
                                   (coe ())
                                   (coe
                                      MAlonzo.Code.Class.MonadTC.du_debugLog'7504'_578 (coe v0)
                                      (coe v3) (coe v2)
                                      (coe
                                         MAlonzo.Code.Class.MonadTC.du__'8759''7496''7504'__540
                                         (coe v0) (coe ("Result: " :: Data.Text.Text))
                                         (coe
                                            MAlonzo.Code.Class.MonadTC.du_IsMErrorPart'45'String_526
                                            (coe v0))
                                         (coe
                                            MAlonzo.Code.Class.MonadTC.du__'8759''7496''7504'__540
                                            (coe v0)
                                            (coe
                                               MAlonzo.Code.Class.MonadTC.du__'7515''8319'_556
                                               (coe v0) (coe v3) (coe v2) (coe ()) (coe v9))
                                            (coe
                                               MAlonzo.Code.Class.MonadTC.du_IsMErrorPart'45'MErrorPartWrap_532)
                                            (coe
                                               MAlonzo.Code.Class.Monad.Core.d_return_20 v0 ()
                                               erased
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                                   (coe
                                      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased
                                      () erased
                                      (coe
                                         MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
                                         (MAlonzo.Code.Class.Applicative.Core.d_super_18
                                            (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
                                         () erased () erased
                                         (\ v10 ->
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v10))
                                         (coe du_getType''_366 (coe v0) (coe v2) (coe v3) (coe v4)))
                                      (\ v10 ->
                                         coe
                                           MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                                           (coe
                                              MAlonzo.Code.Reflection.Utils.Core.C_DataDef'46'constructor_2729
                                              (coe v4) (coe v9)
                                              (coe
                                                 MAlonzo.Code.Data.List.Base.du_take_530 (coe v7)
                                                 (coe v10))
                                              (coe
                                                 MAlonzo.Code.Data.List.Base.du_drop_542 (coe v7)
                                                 (coe v10)))))))
                    _ -> coe v6))))
-- Reflection.Utils.TCI.getRecordDef
d_getRecordDef_392 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
d_getRecordDef_392 ~v0 v1 v2 v3 v4 v5
  = du_getRecordDef_392 v1 v2 v3 v4 v5
du_getRecordDef_392 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
du_getRecordDef_392 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (coe MAlonzo.Code.Class.MonadTC.d_getDefinition_162 v3 v4)
      (\ v5 ->
         let v6
               = coe
                   MAlonzo.Code.Class.MonadTC.du_error1_724 (coe v1) (coe ())
                   (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                   (coe ("Not a record definition!" :: Data.Text.Text)) in
         coe
           (case coe v5 of
              MAlonzo.Code.Agda.Builtin.Reflection.C_record'45'type_296 v7 v8
                -> coe
                     MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                     erased
                     (coe
                        MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
                        (MAlonzo.Code.Class.Applicative.Core.d_super_18
                           (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
                        () erased () erased
                        (\ v9 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v9))
                        (coe du_getType''_366 (coe v0) (coe v2) (coe v3) (coe v4)))
                     (\ v9 ->
                        coe
                          MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                          (coe
                             MAlonzo.Code.Reflection.Utils.Core.C_RecordDef'46'constructor_2859
                             (coe v7) (coe v8) (coe v9)))
              _ -> coe v6))
-- Reflection.Utils.TCI.getDataOrRecordDef
d_getDataOrRecordDef_404 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
d_getDataOrRecordDef_404 ~v0 v1 v2 v3 v4 v5
  = du_getDataOrRecordDef_404 v1 v2 v3 v4 v5
du_getDataOrRecordDef_404 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
du_getDataOrRecordDef_404 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.MonadError.d_catch_28 v1 () erased
      (coe
         MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
         (MAlonzo.Code.Class.Applicative.Core.d_super_18
            (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
         () erased () erased (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
         (coe
            du_getDataDef_374 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)))
      (\ v5 ->
         coe
           MAlonzo.Code.Class.MonadError.d_catch_28 v1 () erased
           (coe
              MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
              (MAlonzo.Code.Class.Applicative.Core.d_super_18
                 (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
              () erased () erased (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
              (coe
                 du_getRecordDef_392 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)))
           (\ v6 ->
              coe
                MAlonzo.Code.Class.MonadTC.du_error1_724 (coe v1) (coe ())
                (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                (coe
                   ("Neither a data not a record definition!" :: Data.Text.Text))))
-- Reflection.Utils.TCI.getParams
d_getParams_412 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
d_getParams_412 ~v0 v1 v2 v3 v4 v5
  = du_getParams_412 v1 v2 v3 v4 v5
du_getParams_412 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
du_getParams_412 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
      (MAlonzo.Code.Class.Applicative.Core.d_super_18
         (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
      () erased () erased
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
         (coe
            (\ v5 -> MAlonzo.Code.Reflection.Utils.Core.d_params_96 (coe v5)))
         (coe
            (\ v5 ->
               MAlonzo.Code.Reflection.Utils.Core.d_params_112 (coe v5))))
      (coe
         du_getDataOrRecordDef_404 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
-- Reflection.Utils.TCI.getParamsAndIndices
d_getParamsAndIndices_416 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
d_getParamsAndIndices_416 ~v0 v1 v2 v3 v4 v5
  = du_getParamsAndIndices_416 v1 v2 v3 v4 v5
du_getParamsAndIndices_416 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
du_getParamsAndIndices_416 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
      (MAlonzo.Code.Class.Applicative.Core.d_super_18
         (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
      () erased () erased
      (coe
         MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
         (coe
            (\ v5 ->
               coe
                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                 (coe MAlonzo.Code.Reflection.Utils.Core.d_params_96 (coe v5))
                 (coe MAlonzo.Code.Reflection.Utils.Core.d_indices_98 (coe v5))))
         (coe
            (\ v5 ->
               MAlonzo.Code.Reflection.Utils.Core.d_params_112 (coe v5))))
      (coe
         du_getDataOrRecordDef_404 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
-- Reflection.Utils.TCI.getFuel
d_getFuel_422 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_getFuel_422 ~v0 v1 v2 v3 ~v4 v5 = du_getFuel_422 v1 v2 v3 v5
du_getFuel_422 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
du_getFuel_422 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased
      (coe
         MAlonzo.Code.Class.MonadReader.du_reader_46 (coe ()) (coe v0)
         (coe v2) (coe ())
         (coe
            (\ v4 ->
               case coe v4 of
                 MAlonzo.Code.Class.MonadTC.C_TCEnv'46'constructor_205 v5 v6 v7 v8 v9 v10 v11 v12
                   -> case coe v12 of
                        MAlonzo.Code.Class.MonadTC.C_TCOptions'46'constructor_49 v13 v14
                          -> coe v14
                        _ -> MAlonzo.RTE.mazUnreachableError
                 _ -> MAlonzo.RTE.mazUnreachableError)))
      (\ v4 ->
         let v5
               = coe
                   MAlonzo.Code.Meta.Prelude.du_lookup'7495'_18
                   (coe
                      (\ v5 v6 ->
                         coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.d_'8970'_'8971'_140 ()
                           erased
                           (coe
                              MAlonzo.Code.Class.DecEq.Core.d__'8799'__16
                              MAlonzo.Code.Class.DecEq.Instances.d_DecEq'45'String_46 v5 v6)))
                   (coe v4) (coe v3) in
         coe
           (case coe v5 of
              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                -> coe MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased v6
              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                -> coe
                     MAlonzo.Code.Class.MonadTC.du_error1_724 (coe v1) (coe ())
                     (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                        (coe ("Key" :: Data.Text.Text))
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'60''43''62'__50 (coe v3)
                           (coe ("doesn't exist in the fuels map" :: Data.Text.Text))))
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Reflection.Utils.TCI.isSort
d_isSort_440 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_isSort_440 ~v0 v1 ~v2 ~v3 v4 v5 = du_isSort_440 v1 v4 v5
du_isSort_440 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_isSort_440 v0 v1 v2
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (coe MAlonzo.Code.Class.MonadTC.d_normalise_140 v1 v2)
      (\ v3 ->
         let v4
               = coe
                   MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) in
         coe
           (case coe v3 of
              MAlonzo.Code.Agda.Builtin.Reflection.C_agda'45'sort_206 v5
                -> coe
                     MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
              _ -> coe v4))
-- Reflection.Utils.TCI.isNArySort
d_isNArySort_446 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_isNArySort_446 ~v0 v1 ~v2 v3 v4 v5
  = du_isNArySort_446 v1 v3 v4 v5
du_isNArySort_446 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_isNArySort_446 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased
      (coe du_viewAndReduceTy_324 (coe v0) (coe v1) (coe v2) (coe v3))
      (\ v4 ->
         case coe v4 of
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
             -> coe
                  MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                  erased (coe du_isSort_440 (coe v0) (coe v2) (coe v6))
                  (\ v7 ->
                     coe
                       MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                          (coe MAlonzo.Code.Data.List.Base.du_length_268 v5)))
           _ -> MAlonzo.RTE.mazUnreachableError)
-- Reflection.Utils.TCI.isDefT
d_isDefT_458 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_isDefT_458 ~v0 v1 ~v2 ~v3 v4 v5 v6 = du_isDefT_458 v1 v4 v5 v6
du_isDefT_458 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_isDefT_458 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (coe MAlonzo.Code.Class.MonadTC.d_normalise_140 v1 v3)
      (\ v4 ->
         let v5
               = coe
                   MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) in
         coe
           (case coe v4 of
              MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 v6 v7
                -> coe
                     MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                     (coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_'8970'_'8971'_140 ()
                        erased
                        (coe
                           MAlonzo.Code.Class.DecEq.Core.d__'8799'__16
                           MAlonzo.Code.Class.DecEq.Instances.d_DecEq'45'Name_200 v2 v6))
              _ -> coe v5))
-- Reflection.Utils.TCI.withSafeReset
d_withSafeReset_468 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
d_withSafeReset_468 ~v0 v1 v2 v3 v4 v5
  = du_withSafeReset_468 v1 v2 v3 v4 v5
du_withSafeReset_468 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
du_withSafeReset_468 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.MonadTC.du_runAndReset_182 (coe v0) (coe v3)
      (coe ())
      (coe
         MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
         erased v4
         (\ v5 ->
            coe
              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
              (coe
                 MAlonzo.Code.Data.List.Base.du_null_262
                 (coe MAlonzo.Code.Reflection.Utils.Metas.d_findMetas_10 v5))
              (coe MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased v5)
              (coe
                 MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
                 (coe ())
                 (coe
                    MAlonzo.Code.Class.MonadTC.du_debugLog'7504'_578 (coe v0) (coe v3)
                    (coe v2)
                    (coe
                       MAlonzo.Code.Class.MonadTC.du__'8759''7496''7504'__540 (coe v0)
                       (coe ("Remaining metavariables:" :: Data.Text.Text))
                       (coe
                          MAlonzo.Code.Class.MonadTC.du_IsMErrorPart'45'IsErrorPart_522
                          (coe v0)
                          (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18))
                       (coe
                          MAlonzo.Code.Class.MonadTC.du__'8759''7496''7504'__540 (coe v0)
                          (coe
                             MAlonzo.Code.Class.MonadTC.du__'7515''8319'_556 (coe v0) (coe v3)
                             (coe v2) (coe ())
                             (coe MAlonzo.Code.Reflection.Utils.Metas.d_findMetas_10 v5))
                          (coe
                             MAlonzo.Code.Class.MonadTC.du_IsMErrorPart'45'MErrorPartWrap_532)
                          (coe
                             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                 (coe
                    MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
                    (coe ())
                    (coe
                       MAlonzo.Code.Class.MonadTC.du_debugLog_570 (coe v0) (coe v3)
                       (coe v2)
                       (coe
                          MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                          (coe ("In term: " :: Data.Text.Text))
                          (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                          (coe
                             MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v5)
                             (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                    (coe
                       MAlonzo.Code.Class.MonadTC.du_error1_724 (coe v1) (coe ())
                       (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                       (coe
                          ("Unsolved metavariables remaining in withSafeReset!"
                           ::
                           Data.Text.Text)))))))
-- Reflection.Utils.TCI.applyWithVisibility
d_applyWithVisibility_476 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154] -> AgdaAny
d_applyWithVisibility_476 ~v0 v1 v2 v3 v4 v5 v6
  = du_applyWithVisibility_476 v1 v2 v3 v4 v5 v6
du_applyWithVisibility_476 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154] -> AgdaAny
du_applyWithVisibility_476 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (coe du_getType''_366 (coe v0) (coe v2) (coe v3) (coe v4))
      (\ v6 ->
         case coe v6 of
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
             -> coe
                  MAlonzo.Code.Class.MonadTC.du_nameConstr_206 (coe v0) (coe v1)
                  (coe v3) (coe v4)
                  (coe
                     MAlonzo.Code.Data.List.Base.du_zipWith_104
                     (coe
                        (\ v9 ->
                           case coe v9 of
                             MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v10 v11
                               -> case coe v11 of
                                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v12 v13
                                      -> coe MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 (coe v12)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError))
                     (coe v7) (coe v5))
           _ -> MAlonzo.RTE.mazUnreachableError)
-- Reflection.Utils.TCI.applyWithVisibilityDB
d_applyWithVisibilityDB_490 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154] -> AgdaAny
d_applyWithVisibilityDB_490 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_applyWithVisibilityDB_490 v1 v3 v4 v5 v6
du_applyWithVisibilityDB_490 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154] -> AgdaAny
du_applyWithVisibilityDB_490 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (coe du_getTypeDB_370 (coe v0) (coe v1) (coe v2) (coe v3))
      (\ v5 ->
         case coe v5 of
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
             -> coe
                  MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                  (coe
                     MAlonzo.Code.Agda.Builtin.Reflection.C_var_172 (coe v3)
                     (coe
                        MAlonzo.Code.Data.List.Base.du_zipWith_104
                        (coe
                           (\ v8 ->
                              case coe v8 of
                                MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v9 v10
                                  -> case coe v10 of
                                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v11 v12
                                         -> coe
                                              MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                              (coe v11)
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError))
                        (coe v6) (coe v4)))
           _ -> MAlonzo.RTE.mazUnreachableError)
