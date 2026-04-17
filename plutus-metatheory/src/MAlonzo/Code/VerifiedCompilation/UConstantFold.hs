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

module MAlonzo.Code.VerifiedCompilation.UConstantFold where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Builtin.Constant.AtomicType
import qualified MAlonzo.Code.Builtin.Signature
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Equality
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.Trace
import qualified MAlonzo.Code.VerifiedCompilation.UntypedTranslation

-- VerifiedCompilation.UConstantFold.evalCF
d_evalCF_6 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Untyped.T__'8866'_14
d_evalCF_6 ~v0 v1 = du_evalCF_6 v1
du_evalCF_6 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  Maybe MAlonzo.Code.Untyped.T__'8866'_14
du_evalCF_6 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Untyped.C__'183'__22 v2 v3
           -> case coe v2 of
                MAlonzo.Code.Untyped.C__'183'__22 v4 v5
                  -> case coe v4 of
                       MAlonzo.Code.Untyped.C__'183'__22 v6 v7
                         -> case coe v6 of
                              MAlonzo.Code.Untyped.C__'183'__22 v8 v9
                                -> case coe v8 of
                                     MAlonzo.Code.Untyped.C__'183'__22 v10 v11
                                       -> case coe v10 of
                                            MAlonzo.Code.Untyped.C__'183'__22 v12 v13
                                              -> case coe v12 of
                                                   MAlonzo.Code.Untyped.C_force_24 v14
                                                     -> case coe v14 of
                                                          MAlonzo.Code.Untyped.C_builtin_44 v15
                                                            -> case coe v15 of
                                                                 MAlonzo.Code.Builtin.C_chooseData_86
                                                                   -> case coe v13 of
                                                                        MAlonzo.Code.Untyped.C_con_28 v16
                                                                          -> case coe v16 of
                                                                               MAlonzo.Code.RawU.C_tmCon_206 v17 v18
                                                                                 -> case coe v17 of
                                                                                      MAlonzo.Code.Builtin.Signature.C_atomic_12 v20
                                                                                        -> case coe
                                                                                                  v20 of
                                                                                             MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
                                                                                               -> case coe
                                                                                                         v18 of
                                                                                                    MAlonzo.Code.Utils.C_ConstrDATA_612 v21 v22
                                                                                                      -> coe
                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                           (coe
                                                                                                              v11)
                                                                                                    MAlonzo.Code.Utils.C_MapDATA_614 v21
                                                                                                      -> coe
                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                           (coe
                                                                                                              v9)
                                                                                                    MAlonzo.Code.Utils.C_ListDATA_616 v21
                                                                                                      -> coe
                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                           (coe
                                                                                                              v7)
                                                                                                    MAlonzo.Code.Utils.C_iDATA_618 v21
                                                                                                      -> coe
                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                           (coe
                                                                                                              v5)
                                                                                                    MAlonzo.Code.Utils.C_bDATA_620 v21
                                                                                                      -> coe
                                                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                           (coe
                                                                                                              v3)
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                             _ -> coe
                                                                                                    v1
                                                                                      _ -> coe v1
                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                        _ -> coe v1
                                                                 _ -> coe v1
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> coe v1
                                     _ -> coe v1
                              MAlonzo.Code.Untyped.C_force_24 v8
                                -> case coe v8 of
                                     MAlonzo.Code.Untyped.C_force_24 v9
                                       -> case coe v9 of
                                            MAlonzo.Code.Untyped.C_builtin_44 v10
                                              -> case coe v10 of
                                                   MAlonzo.Code.Builtin.C_chooseList_70
                                                     -> case coe v7 of
                                                          MAlonzo.Code.Untyped.C_con_28 v11
                                                            -> case coe v11 of
                                                                 MAlonzo.Code.RawU.C_tmCon_206 v12 v13
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.Builtin.Signature.C_list_16 v15
                                                                          -> case coe v13 of
                                                                               MAlonzo.Code.Utils.C_'91''93'_450
                                                                                 -> coe
                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                      (coe v5)
                                                                               MAlonzo.Code.Utils.C__'8759'__452 v16 v17
                                                                                 -> coe
                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                      (coe v3)
                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                        _ -> coe v1
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> coe v1
                                     MAlonzo.Code.Untyped.C_builtin_44 v9
                                       -> case coe v9 of
                                            MAlonzo.Code.Builtin.C_ifThenElse_60
                                              -> case coe v7 of
                                                   MAlonzo.Code.Untyped.C_con_28 v10
                                                     -> case coe v10 of
                                                          MAlonzo.Code.RawU.C_tmCon_206 v11 v12
                                                            -> case coe v11 of
                                                                 MAlonzo.Code.Builtin.Signature.C_atomic_12 v14
                                                                   -> case coe v14 of
                                                                        MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16
                                                                          -> coe
                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                               (coe
                                                                                  MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                                                  (coe v12) (coe v5)
                                                                                  (coe v3))
                                                                        _ -> coe v1
                                                                 _ -> coe v1
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> coe v1
                                            _ -> coe v1
                                     _ -> coe v1
                              _ -> coe v1
                       MAlonzo.Code.Untyped.C_force_24 v6
                         -> case coe v6 of
                              MAlonzo.Code.Untyped.C_builtin_44 v7
                                -> case coe v7 of
                                     MAlonzo.Code.Builtin.C_chooseUnit_62
                                       -> case coe v5 of
                                            MAlonzo.Code.Untyped.C_con_28 v8
                                              -> case coe v8 of
                                                   MAlonzo.Code.RawU.C_tmCon_206 v9 v10
                                                     -> case coe v9 of
                                                          MAlonzo.Code.Builtin.Signature.C_atomic_12 v12
                                                            -> case coe v12 of
                                                                 MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14
                                                                   -> coe
                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                        (coe v3)
                                                                 _ -> coe v1
                                                          _ -> coe v1
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> coe v1
                                     MAlonzo.Code.Builtin.C_mkCons_72
                                       -> case coe v5 of
                                            MAlonzo.Code.Untyped.C_con_28 v8
                                              -> case coe v8 of
                                                   MAlonzo.Code.RawU.C_tmCon_206 v9 v10
                                                     -> case coe v3 of
                                                          MAlonzo.Code.Untyped.C_con_28 v11
                                                            -> case coe v11 of
                                                                 MAlonzo.Code.RawU.C_tmCon_206 v12 v13
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.Builtin.Signature.C_list_16 v15
                                                                          -> let v16
                                                                                   = MAlonzo.Code.RawU.d_decTyTag_68
                                                                                       (coe v9)
                                                                                       (coe v15) in
                                                                             coe
                                                                               (case coe v16 of
                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                                    -> if coe v17
                                                                                         then coe
                                                                                                seq
                                                                                                (coe
                                                                                                   v18)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Untyped.C_con_28
                                                                                                      (coe
                                                                                                         MAlonzo.Code.RawU.C_tmCon_206
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Builtin.Signature.C_list_16
                                                                                                            v9)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Utils.C__'8759'__452
                                                                                                            (coe
                                                                                                               v10)
                                                                                                            (coe
                                                                                                               v13)))))
                                                                                         else coe
                                                                                                seq
                                                                                                (coe
                                                                                                   v18)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                                        _ -> coe v1
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> coe v1
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> coe v1
                                     MAlonzo.Code.Builtin.C_dropList_186
                                       -> case coe v5 of
                                            MAlonzo.Code.Untyped.C_con_28 v8
                                              -> case coe v8 of
                                                   MAlonzo.Code.RawU.C_tmCon_206 v9 v10
                                                     -> case coe v9 of
                                                          MAlonzo.Code.Builtin.Signature.C_atomic_12 v12
                                                            -> case coe v12 of
                                                                 MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                                   -> case coe v3 of
                                                                        MAlonzo.Code.Untyped.C_con_28 v13
                                                                          -> case coe v13 of
                                                                               MAlonzo.Code.RawU.C_tmCon_206 v14 v15
                                                                                 -> case coe v14 of
                                                                                      MAlonzo.Code.Builtin.Signature.C_list_16 v17
                                                                                        -> coe
                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                             (coe
                                                                                                MAlonzo.Code.Untyped.C_con_28
                                                                                                (coe
                                                                                                   MAlonzo.Code.RawU.C_tmCon_206
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Builtin.Signature.C_list_16
                                                                                                      v17)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Utils.du_dropLIST_520
                                                                                                      (coe
                                                                                                         v10)
                                                                                                      (coe
                                                                                                         v15))))
                                                                                      _ -> coe v1
                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                        _ -> coe v1
                                                                 _ -> coe v1
                                                          _ -> coe v1
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> coe v1
                                     _ -> coe v1
                              _ -> coe v1
                       MAlonzo.Code.Untyped.C_builtin_44 v6
                         -> case coe v6 of
                              MAlonzo.Code.Builtin.C_addInteger_4
                                -> case coe v5 of
                                     MAlonzo.Code.Untyped.C_con_28 v7
                                       -> case coe v7 of
                                            MAlonzo.Code.RawU.C_tmCon_206 v8 v9
                                              -> case coe v8 of
                                                   MAlonzo.Code.Builtin.Signature.C_atomic_12 v11
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                            -> case coe v3 of
                                                                 MAlonzo.Code.Untyped.C_con_28 v12
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.RawU.C_tmCon_206 v13 v14
                                                                          -> case coe v13 of
                                                                               MAlonzo.Code.Builtin.Signature.C_atomic_12 v16
                                                                                 -> case coe v16 of
                                                                                      MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                                                        -> coe
                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                             (coe
                                                                                                MAlonzo.Code.Untyped.C_con_28
                                                                                                (coe
                                                                                                   MAlonzo.Code.RawU.C_tmCon_206
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                                      v16)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Data.Integer.Base.d__'43'__284
                                                                                                      (coe
                                                                                                         v9)
                                                                                                      (coe
                                                                                                         v14))))
                                                                                      _ -> coe v1
                                                                               _ -> coe v1
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> coe v1
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v1
                              MAlonzo.Code.Builtin.C_subtractInteger_6
                                -> case coe v5 of
                                     MAlonzo.Code.Untyped.C_con_28 v7
                                       -> case coe v7 of
                                            MAlonzo.Code.RawU.C_tmCon_206 v8 v9
                                              -> case coe v8 of
                                                   MAlonzo.Code.Builtin.Signature.C_atomic_12 v11
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                            -> case coe v3 of
                                                                 MAlonzo.Code.Untyped.C_con_28 v12
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.RawU.C_tmCon_206 v13 v14
                                                                          -> case coe v13 of
                                                                               MAlonzo.Code.Builtin.Signature.C_atomic_12 v16
                                                                                 -> case coe v16 of
                                                                                      MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                                                        -> coe
                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                             (coe
                                                                                                MAlonzo.Code.Untyped.C_con_28
                                                                                                (coe
                                                                                                   MAlonzo.Code.RawU.C_tmCon_206
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                                      v16)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Data.Integer.Base.d__'45'__302
                                                                                                      (coe
                                                                                                         v9)
                                                                                                      (coe
                                                                                                         v14))))
                                                                                      _ -> coe v1
                                                                               _ -> coe v1
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> coe v1
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v1
                              MAlonzo.Code.Builtin.C_multiplyInteger_8
                                -> case coe v5 of
                                     MAlonzo.Code.Untyped.C_con_28 v7
                                       -> case coe v7 of
                                            MAlonzo.Code.RawU.C_tmCon_206 v8 v9
                                              -> case coe v8 of
                                                   MAlonzo.Code.Builtin.Signature.C_atomic_12 v11
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                            -> case coe v3 of
                                                                 MAlonzo.Code.Untyped.C_con_28 v12
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.RawU.C_tmCon_206 v13 v14
                                                                          -> case coe v13 of
                                                                               MAlonzo.Code.Builtin.Signature.C_atomic_12 v16
                                                                                 -> case coe v16 of
                                                                                      MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                                                        -> coe
                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                             (coe
                                                                                                MAlonzo.Code.Untyped.C_con_28
                                                                                                (coe
                                                                                                   MAlonzo.Code.RawU.C_tmCon_206
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                                      v16)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Data.Integer.Base.d__'42'__316
                                                                                                      (coe
                                                                                                         v9)
                                                                                                      (coe
                                                                                                         v14))))
                                                                                      _ -> coe v1
                                                                               _ -> coe v1
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> coe v1
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v1
                              MAlonzo.Code.Builtin.C_divideInteger_10
                                -> case coe v5 of
                                     MAlonzo.Code.Untyped.C_con_28 v7
                                       -> case coe v7 of
                                            MAlonzo.Code.RawU.C_tmCon_206 v8 v9
                                              -> case coe v8 of
                                                   MAlonzo.Code.Builtin.Signature.C_atomic_12 v11
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                            -> case coe v3 of
                                                                 MAlonzo.Code.Untyped.C_con_28 v12
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.RawU.C_tmCon_206 v13 v14
                                                                          -> case coe v13 of
                                                                               MAlonzo.Code.Builtin.Signature.C_atomic_12 v16
                                                                                 -> case coe v16 of
                                                                                      MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                                                        -> let v17
                                                                                                 = MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800
                                                                                                     (coe
                                                                                                        v14)
                                                                                                     (coe
                                                                                                        (0 ::
                                                                                                           Integer)) in
                                                                                           coe
                                                                                             (case coe
                                                                                                     v17 of
                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                                  -> if coe
                                                                                                          v18
                                                                                                       then coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v19)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                                                       else coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v19)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Untyped.C_con_28
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.RawU.C_tmCon_206
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                                                          v16)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Builtin.d_div_312
                                                                                                                          v9
                                                                                                                          v14))))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                      _ -> coe v1
                                                                               _ -> coe v1
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> coe v1
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v1
                              MAlonzo.Code.Builtin.C_quotientInteger_12
                                -> case coe v5 of
                                     MAlonzo.Code.Untyped.C_con_28 v7
                                       -> case coe v7 of
                                            MAlonzo.Code.RawU.C_tmCon_206 v8 v9
                                              -> case coe v8 of
                                                   MAlonzo.Code.Builtin.Signature.C_atomic_12 v11
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                            -> case coe v3 of
                                                                 MAlonzo.Code.Untyped.C_con_28 v12
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.RawU.C_tmCon_206 v13 v14
                                                                          -> case coe v13 of
                                                                               MAlonzo.Code.Builtin.Signature.C_atomic_12 v16
                                                                                 -> case coe v16 of
                                                                                      MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                                                        -> let v17
                                                                                                 = MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800
                                                                                                     (coe
                                                                                                        v14)
                                                                                                     (coe
                                                                                                        (0 ::
                                                                                                           Integer)) in
                                                                                           coe
                                                                                             (case coe
                                                                                                     v17 of
                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                                  -> if coe
                                                                                                          v18
                                                                                                       then coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v19)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                                                       else coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v19)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Untyped.C_con_28
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.RawU.C_tmCon_206
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                                                          v16)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Builtin.d_quot_314
                                                                                                                          v9
                                                                                                                          v14))))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                      _ -> coe v1
                                                                               _ -> coe v1
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> coe v1
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v1
                              MAlonzo.Code.Builtin.C_remainderInteger_14
                                -> case coe v5 of
                                     MAlonzo.Code.Untyped.C_con_28 v7
                                       -> case coe v7 of
                                            MAlonzo.Code.RawU.C_tmCon_206 v8 v9
                                              -> case coe v8 of
                                                   MAlonzo.Code.Builtin.Signature.C_atomic_12 v11
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                            -> case coe v3 of
                                                                 MAlonzo.Code.Untyped.C_con_28 v12
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.RawU.C_tmCon_206 v13 v14
                                                                          -> case coe v13 of
                                                                               MAlonzo.Code.Builtin.Signature.C_atomic_12 v16
                                                                                 -> case coe v16 of
                                                                                      MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                                                        -> let v17
                                                                                                 = MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800
                                                                                                     (coe
                                                                                                        v14)
                                                                                                     (coe
                                                                                                        (0 ::
                                                                                                           Integer)) in
                                                                                           coe
                                                                                             (case coe
                                                                                                     v17 of
                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                                  -> if coe
                                                                                                          v18
                                                                                                       then coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v19)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                                                       else coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v19)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Untyped.C_con_28
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.RawU.C_tmCon_206
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                                                          v16)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Builtin.d_rem_316
                                                                                                                          v9
                                                                                                                          v14))))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                      _ -> coe v1
                                                                               _ -> coe v1
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> coe v1
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v1
                              MAlonzo.Code.Builtin.C_modInteger_16
                                -> case coe v5 of
                                     MAlonzo.Code.Untyped.C_con_28 v7
                                       -> case coe v7 of
                                            MAlonzo.Code.RawU.C_tmCon_206 v8 v9
                                              -> case coe v8 of
                                                   MAlonzo.Code.Builtin.Signature.C_atomic_12 v11
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                            -> case coe v3 of
                                                                 MAlonzo.Code.Untyped.C_con_28 v12
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.RawU.C_tmCon_206 v13 v14
                                                                          -> case coe v13 of
                                                                               MAlonzo.Code.Builtin.Signature.C_atomic_12 v16
                                                                                 -> case coe v16 of
                                                                                      MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                                                        -> let v17
                                                                                                 = MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800
                                                                                                     (coe
                                                                                                        v14)
                                                                                                     (coe
                                                                                                        (0 ::
                                                                                                           Integer)) in
                                                                                           coe
                                                                                             (case coe
                                                                                                     v17 of
                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                                  -> if coe
                                                                                                          v18
                                                                                                       then coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v19)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                                                       else coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v19)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Untyped.C_con_28
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.RawU.C_tmCon_206
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                                                          v16)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Builtin.d_mod_318
                                                                                                                          v9
                                                                                                                          v14))))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                      _ -> coe v1
                                                                               _ -> coe v1
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> coe v1
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v1
                              MAlonzo.Code.Builtin.C_equalsInteger_18
                                -> case coe v5 of
                                     MAlonzo.Code.Untyped.C_con_28 v7
                                       -> case coe v7 of
                                            MAlonzo.Code.RawU.C_tmCon_206 v8 v9
                                              -> case coe v8 of
                                                   MAlonzo.Code.Builtin.Signature.C_atomic_12 v11
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                            -> case coe v3 of
                                                                 MAlonzo.Code.Untyped.C_con_28 v12
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.RawU.C_tmCon_206 v13 v14
                                                                          -> case coe v13 of
                                                                               MAlonzo.Code.Builtin.Signature.C_atomic_12 v16
                                                                                 -> case coe v16 of
                                                                                      MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                                                        -> coe
                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                             (coe
                                                                                                MAlonzo.Code.Untyped.C_con_28
                                                                                                (coe
                                                                                                   MAlonzo.Code.RawU.C_tmCon_206
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800
                                                                                                         (coe
                                                                                                            v9)
                                                                                                         (coe
                                                                                                            v14)))))
                                                                                      _ -> coe v1
                                                                               _ -> coe v1
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> coe v1
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v1
                              MAlonzo.Code.Builtin.C_lessThanInteger_20
                                -> case coe v5 of
                                     MAlonzo.Code.Untyped.C_con_28 v7
                                       -> case coe v7 of
                                            MAlonzo.Code.RawU.C_tmCon_206 v8 v9
                                              -> case coe v8 of
                                                   MAlonzo.Code.Builtin.Signature.C_atomic_12 v11
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                            -> case coe v3 of
                                                                 MAlonzo.Code.Untyped.C_con_28 v12
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.RawU.C_tmCon_206 v13 v14
                                                                          -> case coe v13 of
                                                                               MAlonzo.Code.Builtin.Signature.C_atomic_12 v16
                                                                                 -> case coe v16 of
                                                                                      MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                                                        -> coe
                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                             (coe
                                                                                                MAlonzo.Code.Untyped.C_con_28
                                                                                                (coe
                                                                                                   MAlonzo.Code.RawU.C_tmCon_206
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Data.Integer.Properties.d__'60''63'__3190
                                                                                                         (coe
                                                                                                            v9)
                                                                                                         (coe
                                                                                                            v14)))))
                                                                                      _ -> coe v1
                                                                               _ -> coe v1
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> coe v1
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v1
                              MAlonzo.Code.Builtin.C_lessThanEqualsInteger_22
                                -> case coe v5 of
                                     MAlonzo.Code.Untyped.C_con_28 v7
                                       -> case coe v7 of
                                            MAlonzo.Code.RawU.C_tmCon_206 v8 v9
                                              -> case coe v8 of
                                                   MAlonzo.Code.Builtin.Signature.C_atomic_12 v11
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                            -> case coe v3 of
                                                                 MAlonzo.Code.Untyped.C_con_28 v12
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.RawU.C_tmCon_206 v13 v14
                                                                          -> case coe v13 of
                                                                               MAlonzo.Code.Builtin.Signature.C_atomic_12 v16
                                                                                 -> case coe v16 of
                                                                                      MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                                                        -> coe
                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                             (coe
                                                                                                MAlonzo.Code.Untyped.C_con_28
                                                                                                (coe
                                                                                                   MAlonzo.Code.RawU.C_tmCon_206
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Data.Integer.Properties.d__'8804''63'__2880
                                                                                                         (coe
                                                                                                            v9)
                                                                                                         (coe
                                                                                                            v14)))))
                                                                                      _ -> coe v1
                                                                               _ -> coe v1
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> coe v1
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v1
                              MAlonzo.Code.Builtin.C_constrData_88
                                -> case coe v5 of
                                     MAlonzo.Code.Untyped.C_con_28 v7
                                       -> case coe v7 of
                                            MAlonzo.Code.RawU.C_tmCon_206 v8 v9
                                              -> case coe v8 of
                                                   MAlonzo.Code.Builtin.Signature.C_atomic_12 v11
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                            -> case coe v3 of
                                                                 MAlonzo.Code.Untyped.C_con_28 v12
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.RawU.C_tmCon_206 v13 v14
                                                                          -> case coe v13 of
                                                                               MAlonzo.Code.Builtin.Signature.C_list_16 v16
                                                                                 -> case coe v16 of
                                                                                      MAlonzo.Code.Builtin.Signature.C_atomic_12 v18
                                                                                        -> case coe
                                                                                                  v18 of
                                                                                             MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
                                                                                               -> coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Untyped.C_con_28
                                                                                                       (coe
                                                                                                          MAlonzo.Code.RawU.C_tmCon_206
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                                             v18)
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Utils.C_ConstrDATA_612
                                                                                                             (coe
                                                                                                                v9)
                                                                                                             (coe
                                                                                                                v14))))
                                                                                             _ -> coe
                                                                                                    v1
                                                                                      _ -> coe v1
                                                                               _ -> coe v1
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> coe v1
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v1
                              MAlonzo.Code.Builtin.C_equalsData_108
                                -> case coe v5 of
                                     MAlonzo.Code.Untyped.C_con_28 v7
                                       -> case coe v7 of
                                            MAlonzo.Code.RawU.C_tmCon_206 v8 v9
                                              -> case coe v8 of
                                                   MAlonzo.Code.Builtin.Signature.C_atomic_12 v11
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
                                                            -> case coe v3 of
                                                                 MAlonzo.Code.Untyped.C_con_28 v12
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.RawU.C_tmCon_206 v13 v14
                                                                          -> case coe v13 of
                                                                               MAlonzo.Code.Builtin.Signature.C_atomic_12 v16
                                                                                 -> case coe v16 of
                                                                                      MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
                                                                                        -> coe
                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                             (coe
                                                                                                MAlonzo.Code.Untyped.C_con_28
                                                                                                (coe
                                                                                                   MAlonzo.Code.RawU.C_tmCon_206
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Utils.d_eqDATA_622
                                                                                                      (coe
                                                                                                         v9)
                                                                                                      (coe
                                                                                                         v14))))
                                                                                      _ -> coe v1
                                                                               _ -> coe v1
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> coe v1
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v1
                              MAlonzo.Code.Builtin.C_mkPairData_112
                                -> case coe v5 of
                                     MAlonzo.Code.Untyped.C_con_28 v7
                                       -> case coe v7 of
                                            MAlonzo.Code.RawU.C_tmCon_206 v8 v9
                                              -> case coe v8 of
                                                   MAlonzo.Code.Builtin.Signature.C_atomic_12 v11
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
                                                            -> case coe v3 of
                                                                 MAlonzo.Code.Untyped.C_con_28 v12
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.RawU.C_tmCon_206 v13 v14
                                                                          -> case coe v13 of
                                                                               MAlonzo.Code.Builtin.Signature.C_atomic_12 v16
                                                                                 -> case coe v16 of
                                                                                      MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
                                                                                        -> coe
                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                             (coe
                                                                                                MAlonzo.Code.Untyped.C_con_28
                                                                                                (coe
                                                                                                   MAlonzo.Code.RawU.C_tmCon_206
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Builtin.Signature.C_pair_24
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                                         v16)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                                         v16))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Utils.C__'44'__442
                                                                                                      (coe
                                                                                                         v9)
                                                                                                      (coe
                                                                                                         v14))))
                                                                                      _ -> coe v1
                                                                               _ -> coe v1
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> coe v1
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v1
                              _ -> coe v1
                       _ -> coe v1
                MAlonzo.Code.Untyped.C_force_24 v4
                  -> case coe v4 of
                       MAlonzo.Code.Untyped.C_force_24 v5
                         -> case coe v5 of
                              MAlonzo.Code.Untyped.C_builtin_44 v6
                                -> case coe v6 of
                                     MAlonzo.Code.Builtin.C_fstPair_66
                                       -> case coe v3 of
                                            MAlonzo.Code.Untyped.C_con_28 v7
                                              -> case coe v7 of
                                                   MAlonzo.Code.RawU.C_tmCon_206 v8 v9
                                                     -> case coe v8 of
                                                          MAlonzo.Code.Builtin.Signature.C_pair_24 v11 v12
                                                            -> case coe v9 of
                                                                 MAlonzo.Code.Utils.C__'44'__442 v13 v14
                                                                   -> coe
                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                        (coe
                                                                           MAlonzo.Code.Untyped.C_con_28
                                                                           (coe
                                                                              MAlonzo.Code.RawU.C_tmCon_206
                                                                              (coe v11) (coe v13)))
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> coe v1
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> coe v1
                                     MAlonzo.Code.Builtin.C_sndPair_68
                                       -> case coe v3 of
                                            MAlonzo.Code.Untyped.C_con_28 v7
                                              -> case coe v7 of
                                                   MAlonzo.Code.RawU.C_tmCon_206 v8 v9
                                                     -> case coe v8 of
                                                          MAlonzo.Code.Builtin.Signature.C_pair_24 v11 v12
                                                            -> case coe v9 of
                                                                 MAlonzo.Code.Utils.C__'44'__442 v13 v14
                                                                   -> coe
                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                        (coe
                                                                           MAlonzo.Code.Untyped.C_con_28
                                                                           (coe
                                                                              MAlonzo.Code.RawU.C_tmCon_206
                                                                              (coe v12) (coe v14)))
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> coe v1
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> coe v1
                                     _ -> coe v1
                              _ -> coe v1
                       MAlonzo.Code.Untyped.C_builtin_44 v5
                         -> case coe v5 of
                              MAlonzo.Code.Builtin.C_headList_74
                                -> case coe v3 of
                                     MAlonzo.Code.Untyped.C_con_28 v6
                                       -> case coe v6 of
                                            MAlonzo.Code.RawU.C_tmCon_206 v7 v8
                                              -> case coe v7 of
                                                   MAlonzo.Code.Builtin.Signature.C_list_16 v10
                                                     -> case coe v8 of
                                                          MAlonzo.Code.Utils.C__'8759'__452 v11 v12
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                 (coe
                                                                    MAlonzo.Code.Untyped.C_con_28
                                                                    (coe
                                                                       MAlonzo.Code.RawU.C_tmCon_206
                                                                       (coe v10) (coe v11)))
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v1
                              MAlonzo.Code.Builtin.C_tailList_76
                                -> case coe v3 of
                                     MAlonzo.Code.Untyped.C_con_28 v6
                                       -> case coe v6 of
                                            MAlonzo.Code.RawU.C_tmCon_206 v7 v8
                                              -> case coe v7 of
                                                   MAlonzo.Code.Builtin.Signature.C_list_16 v10
                                                     -> case coe v8 of
                                                          MAlonzo.Code.Utils.C__'8759'__452 v11 v12
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                 (coe
                                                                    MAlonzo.Code.Untyped.C_con_28
                                                                    (coe
                                                                       MAlonzo.Code.RawU.C_tmCon_206
                                                                       (coe
                                                                          MAlonzo.Code.Builtin.Signature.C_list_16
                                                                          v10)
                                                                       (coe v12)))
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v1
                              MAlonzo.Code.Builtin.C_nullList_78
                                -> case coe v3 of
                                     MAlonzo.Code.Untyped.C_con_28 v6
                                       -> case coe v6 of
                                            MAlonzo.Code.RawU.C_tmCon_206 v7 v8
                                              -> case coe v7 of
                                                   MAlonzo.Code.Builtin.Signature.C_list_16 v10
                                                     -> case coe v8 of
                                                          MAlonzo.Code.Utils.C_'91''93'_450
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                 (coe
                                                                    MAlonzo.Code.Untyped.C_con_28
                                                                    (coe
                                                                       MAlonzo.Code.RawU.C_tmCon_206
                                                                       (coe
                                                                          MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                          (coe
                                                                             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Bool.C_true_10)))
                                                          MAlonzo.Code.Utils.C__'8759'__452 v11 v12
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                 (coe
                                                                    MAlonzo.Code.Untyped.C_con_28
                                                                    (coe
                                                                       MAlonzo.Code.RawU.C_tmCon_206
                                                                       (coe
                                                                          MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                          (coe
                                                                             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8)))
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> coe v1
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v1
                              _ -> coe v1
                       _ -> coe v1
                MAlonzo.Code.Untyped.C_builtin_44 v4
                  -> case coe v4 of
                       MAlonzo.Code.Builtin.C_mapData_90
                         -> case coe v3 of
                              MAlonzo.Code.Untyped.C_con_28 v5
                                -> case coe v5 of
                                     MAlonzo.Code.RawU.C_tmCon_206 v6 v7
                                       -> case coe v6 of
                                            MAlonzo.Code.Builtin.Signature.C_list_16 v9
                                              -> case coe v9 of
                                                   MAlonzo.Code.Builtin.Signature.C_pair_24 v11 v12
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Builtin.Signature.C_atomic_12 v14
                                                            -> case coe v14 of
                                                                 MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.Builtin.Signature.C_atomic_12 v16
                                                                          -> case coe v16 of
                                                                               MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
                                                                                 -> coe
                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                      (coe
                                                                                         MAlonzo.Code.Untyped.C_con_28
                                                                                         (coe
                                                                                            MAlonzo.Code.RawU.C_tmCon_206
                                                                                            (coe
                                                                                               MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                               v16)
                                                                                            (coe
                                                                                               MAlonzo.Code.Utils.C_MapDATA_614
                                                                                               (coe
                                                                                                  v7))))
                                                                               _ -> coe v1
                                                                        _ -> coe v1
                                                                 _ -> coe v1
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> coe v1
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v1
                       MAlonzo.Code.Builtin.C_listData_92
                         -> case coe v3 of
                              MAlonzo.Code.Untyped.C_con_28 v5
                                -> case coe v5 of
                                     MAlonzo.Code.RawU.C_tmCon_206 v6 v7
                                       -> case coe v6 of
                                            MAlonzo.Code.Builtin.Signature.C_list_16 v9
                                              -> case coe v9 of
                                                   MAlonzo.Code.Builtin.Signature.C_atomic_12 v11
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                 (coe
                                                                    MAlonzo.Code.Untyped.C_con_28
                                                                    (coe
                                                                       MAlonzo.Code.RawU.C_tmCon_206
                                                                       (coe
                                                                          MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                          v11)
                                                                       (coe
                                                                          MAlonzo.Code.Utils.C_ListDATA_616
                                                                          (coe v7))))
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> coe v1
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v1
                       MAlonzo.Code.Builtin.C_iData_94
                         -> case coe v3 of
                              MAlonzo.Code.Untyped.C_con_28 v5
                                -> case coe v5 of
                                     MAlonzo.Code.RawU.C_tmCon_206 v6 v7
                                       -> case coe v6 of
                                            MAlonzo.Code.Builtin.Signature.C_atomic_12 v9
                                              -> case coe v9 of
                                                   MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                          (coe
                                                             MAlonzo.Code.Untyped.C_con_28
                                                             (coe
                                                                MAlonzo.Code.RawU.C_tmCon_206
                                                                (coe
                                                                   MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                   (coe
                                                                      MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18))
                                                                (coe
                                                                   MAlonzo.Code.Utils.C_iDATA_618
                                                                   (coe v7))))
                                                   _ -> coe v1
                                            _ -> coe v1
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v1
                       MAlonzo.Code.Builtin.C_unConstrData_98
                         -> case coe v3 of
                              MAlonzo.Code.Untyped.C_con_28 v5
                                -> case coe v5 of
                                     MAlonzo.Code.RawU.C_tmCon_206 v6 v7
                                       -> case coe v6 of
                                            MAlonzo.Code.Builtin.Signature.C_atomic_12 v9
                                              -> case coe v9 of
                                                   MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
                                                     -> case coe v7 of
                                                          MAlonzo.Code.Utils.C_ConstrDATA_612 v10 v11
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                 (coe
                                                                    MAlonzo.Code.Untyped.C_con_28
                                                                    (coe
                                                                       MAlonzo.Code.RawU.C_tmCon_206
                                                                       (coe
                                                                          MAlonzo.Code.Builtin.Signature.C_pair_24
                                                                          (coe
                                                                             MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                             (coe
                                                                                MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8))
                                                                          (coe
                                                                             MAlonzo.Code.Builtin.Signature.C_list_16
                                                                             (coe
                                                                                MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                v9)))
                                                                       (coe
                                                                          MAlonzo.Code.Utils.C__'44'__442
                                                                          (coe v10) (coe v11))))
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> coe v1
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v1
                       MAlonzo.Code.Builtin.C_unMapData_100
                         -> case coe v3 of
                              MAlonzo.Code.Untyped.C_con_28 v5
                                -> case coe v5 of
                                     MAlonzo.Code.RawU.C_tmCon_206 v6 v7
                                       -> case coe v6 of
                                            MAlonzo.Code.Builtin.Signature.C_atomic_12 v9
                                              -> case coe v9 of
                                                   MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
                                                     -> case coe v7 of
                                                          MAlonzo.Code.Utils.C_MapDATA_614 v10
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                 (coe
                                                                    MAlonzo.Code.Untyped.C_con_28
                                                                    (coe
                                                                       MAlonzo.Code.RawU.C_tmCon_206
                                                                       (coe
                                                                          MAlonzo.Code.Builtin.Signature.C_list_16
                                                                          (coe
                                                                             MAlonzo.Code.Builtin.Signature.C_pair_24
                                                                             (coe
                                                                                MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                v9)
                                                                             (coe
                                                                                MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                                v9)))
                                                                       (coe v10)))
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> coe v1
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v1
                       MAlonzo.Code.Builtin.C_unListData_102
                         -> case coe v3 of
                              MAlonzo.Code.Untyped.C_con_28 v5
                                -> case coe v5 of
                                     MAlonzo.Code.RawU.C_tmCon_206 v6 v7
                                       -> case coe v6 of
                                            MAlonzo.Code.Builtin.Signature.C_atomic_12 v9
                                              -> case coe v9 of
                                                   MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
                                                     -> case coe v7 of
                                                          MAlonzo.Code.Utils.C_ListDATA_616 v10
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                 (coe
                                                                    MAlonzo.Code.Untyped.C_con_28
                                                                    (coe
                                                                       MAlonzo.Code.RawU.C_tmCon_206
                                                                       (coe
                                                                          MAlonzo.Code.Builtin.Signature.C_list_16
                                                                          (coe
                                                                             MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                             v9))
                                                                       (coe v10)))
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> coe v1
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v1
                       MAlonzo.Code.Builtin.C_unIData_104
                         -> case coe v3 of
                              MAlonzo.Code.Untyped.C_con_28 v5
                                -> case coe v5 of
                                     MAlonzo.Code.RawU.C_tmCon_206 v6 v7
                                       -> case coe v6 of
                                            MAlonzo.Code.Builtin.Signature.C_atomic_12 v9
                                              -> case coe v9 of
                                                   MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
                                                     -> case coe v7 of
                                                          MAlonzo.Code.Utils.C_iDATA_618 v10
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                 (coe
                                                                    MAlonzo.Code.Untyped.C_con_28
                                                                    (coe
                                                                       MAlonzo.Code.RawU.C_tmCon_206
                                                                       (coe
                                                                          MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                          (coe
                                                                             MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8))
                                                                       (coe v10)))
                                                          _ -> coe v1
                                                   _ -> coe v1
                                            _ -> coe v1
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v1
                       MAlonzo.Code.Builtin.C_mkNilData_114
                         -> case coe v3 of
                              MAlonzo.Code.Untyped.C_con_28 v5
                                -> case coe v5 of
                                     MAlonzo.Code.RawU.C_tmCon_206 v6 v7
                                       -> case coe v6 of
                                            MAlonzo.Code.Builtin.Signature.C_atomic_12 v9
                                              -> case coe v9 of
                                                   MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                          (coe
                                                             MAlonzo.Code.Untyped.C_con_28
                                                             (coe
                                                                MAlonzo.Code.RawU.C_tmCon_206
                                                                (coe
                                                                   MAlonzo.Code.Builtin.Signature.C_list_16
                                                                   (coe
                                                                      MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                      (coe
                                                                         MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18)))
                                                                (coe
                                                                   MAlonzo.Code.Utils.C_'91''93'_450)))
                                                   _ -> coe v1
                                            _ -> coe v1
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v1
                       MAlonzo.Code.Builtin.C_mkNilPairData_116
                         -> case coe v3 of
                              MAlonzo.Code.Untyped.C_con_28 v5
                                -> case coe v5 of
                                     MAlonzo.Code.RawU.C_tmCon_206 v6 v7
                                       -> case coe v6 of
                                            MAlonzo.Code.Builtin.Signature.C_atomic_12 v9
                                              -> case coe v9 of
                                                   MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                          (coe
                                                             MAlonzo.Code.Untyped.C_con_28
                                                             (coe
                                                                MAlonzo.Code.RawU.C_tmCon_206
                                                                (coe
                                                                   MAlonzo.Code.Builtin.Signature.C_list_16
                                                                   (coe
                                                                      MAlonzo.Code.Builtin.Signature.C_pair_24
                                                                      (coe
                                                                         MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                         (coe
                                                                            MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18))
                                                                      (coe
                                                                         MAlonzo.Code.Builtin.Signature.C_atomic_12
                                                                         (coe
                                                                            MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18))))
                                                                (coe
                                                                   MAlonzo.Code.Utils.C_'91''93'_450)))
                                                   _ -> coe v1
                                            _ -> coe v1
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v1
                       _ -> coe v1
                _ -> coe v1
         _ -> coe v1)
-- VerifiedCompilation.UConstantFold.ConstantFold
d_ConstantFold_196 a0 a1 a2 = ()
data T_ConstantFold_196 = C_constantFold_204
-- VerifiedCompilation.UConstantFold.isConstantFold?
d_isConstantFold'63'_208 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38
d_isConstantFold'63'_208 v0 v1 v2
  = let v3 = coe du_evalCF_6 (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> let v5
                    = MAlonzo.Code.Untyped.Equality.d_decEq'45''8866'_56
                        (coe v0) (coe v4) (coe v2) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                     -> if coe v6
                          then coe
                                 seq (coe v7)
                                 (coe
                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44
                                    (coe C_constantFold_204))
                          else coe
                                 seq (coe v7)
                                 (coe
                                    MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                                    MAlonzo.Code.VerifiedCompilation.Trace.d_ConstantFoldT_46 v1 v2)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                MAlonzo.Code.VerifiedCompilation.Trace.d_ConstantFoldT_46 v1 v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UConstantFold.UConstantFold
d_UConstantFold_258 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_UConstantFold_258 = erased
-- VerifiedCompilation.UConstantFold.isUConstantFold?
d_isUConstantFold'63'_262 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38
d_isUConstantFold'63'_262 v0
  = coe
      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.du_translation'63'_164
      (coe v0)
      (coe MAlonzo.Code.VerifiedCompilation.Trace.d_ConstantFoldT_46)
      (coe d_isConstantFold'63'_208)
