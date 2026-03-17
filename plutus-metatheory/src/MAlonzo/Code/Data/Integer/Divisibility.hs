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

module MAlonzo.Code.Data.Integer.Divisibility where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Divisibility
import qualified MAlonzo.Code.Data.Nat.Divisibility.Core
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Double
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax

-- Data.Integer.Divisibility._∣_
d__'8739'__6 :: Integer -> Integer -> ()
d__'8739'__6 = erased
-- Data.Integer.Divisibility.*-monoʳ-∣
d_'42''45'mono'691''45''8739'_18 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'42''45'mono'691''45''8739'_18 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
            (coe v4))
         (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v1)))
         (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v2)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v5 v6 v7 v8 v9 -> v9)
            (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
               (coe
                  MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v1)))
            (mulInt
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
            (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
               (coe
                  MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v2)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_332
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                  (coe
                     MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200))
               (mulInt
                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
               (mulInt
                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v2)))
               (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v2)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                  (\ v5 v6 v7 v8 v9 -> v9)
                  (mulInt
                     (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                     (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v2)))
                  (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v2)))
                  (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v2)))
                  (let v5
                         = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200 in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                           (coe v5))
                        (coe
                           MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                           (coe
                              MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v2)))))
                  erased)
               (coe
                  MAlonzo.Code.Data.Nat.Divisibility.du_'42''45'mono'691''45''8739'_426
                  v3))
            erased))
-- Data.Integer.Divisibility.*-monoˡ-∣
d_'42''45'mono'737''45''8739'_36 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'42''45'mono'737''45''8739'_36 v0 v1 v2
  = coe d_'42''45'mono'691''45''8739'_18 (coe v0) (coe v1) (coe v2)
-- Data.Integer.Divisibility.*-cancelˡ-∣
d_'42''45'cancel'737''45''8739'_60 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'42''45'cancel'737''45''8739'_60 v0 v1 v2 ~v3 v4
  = du_'42''45'cancel'737''45''8739'_60 v0 v1 v2 v4
du_'42''45'cancel'737''45''8739'_60 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'42''45'cancel'737''45''8739'_60 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Nat.Divisibility.du_'42''45'cancel'737''45''8739'_440
      (let v4
             = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
               (coe v4))
            (mulInt
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
            (mulInt
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
               (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v2)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
               (\ v5 v6 v7 v8 v9 -> v9)
               (mulInt
                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v1)))
               (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v1)))
               (mulInt
                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v2)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8739'_332
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                     (coe
                        MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200))
                  (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v1)))
                  (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v2)))
                  (mulInt
                     (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                     (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v2)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                     (\ v5 v6 v7 v8 v9 -> v9)
                     (MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                        (coe
                           MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0) (coe v2)))
                     (mulInt
                        (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                        (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v2)))
                     (mulInt
                        (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                        (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v2)))
                     (let v5
                            = MAlonzo.Code.Data.Nat.Divisibility.d_'8739''45'isPreorder_200 in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                              (coe v5))
                           (coe
                              mulInt
                              (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
                              (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v2)))))
                     erased)
                  v3)
               erased)))
-- Data.Integer.Divisibility.*-cancelʳ-∣
d_'42''45'cancel'691''45''8739'_82 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
d_'42''45'cancel'691''45''8739'_82 v0 v1 v2 ~v3
  = du_'42''45'cancel'691''45''8739'_82 v0 v1 v2
du_'42''45'cancel'691''45''8739'_82 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20 ->
  MAlonzo.Code.Data.Nat.Divisibility.Core.T__'8739'__20
du_'42''45'cancel'691''45''8739'_82 v0 v1 v2
  = coe
      du_'42''45'cancel'737''45''8739'_60 (coe v0) (coe v1) (coe v2)
