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

module MAlonzo.Code.Untyped.Relation.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Untyped

-- Untyped.Relation.Properties.Reflexive
d_Reflexive_6 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Reflexive_6 = erased
-- Untyped.Relation.Properties.Transitive
d_Transitive_14 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Transitive_14 = erased
-- Untyped.Relation.Properties.Symmetric
d_Symmetric_26 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Symmetric_26 = erased
-- Untyped.Relation.Properties.Idempotent
d_Idempotent_36 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Idempotent_36 = erased
-- Untyped.Relation.Properties._⊆_
d__'8838'__48 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d__'8838'__48 = erased
-- Untyped.Relation.Properties.⊆-trans
d_'8838''45'trans_66 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
d_'8838''45'trans_66 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_'8838''45'trans_66 v3 v4 v5 v6 v7 v8
du_'8838''45'trans_66 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
du_'8838''45'trans_66 v0 v1 v2 v3 v4 v5
  = coe v1 v2 v3 v4 (coe v0 v2 v3 v4 v5)
-- Untyped.Relation.Properties.Transform
d_Transform_74 :: ()
d_Transform_74 = erased
-- Untyped.Relation.Properties.Transform?
d_Transform'63'_78 :: ()
d_Transform'63'_78 = erased
-- Untyped.Relation.Properties.Transform₂
d_Transform'8322'_82 :: ()
d_Transform'8322'_82 = erased
-- Untyped.Relation.Properties.Deterministicᵣ
d_Deterministic'7523'_86 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Deterministic'7523'_86 = erased
-- Untyped.Relation.Properties.Deterministicₗ
d_Deterministic'8343'_98 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Deterministic'8343'_98 = erased
-- Untyped.Relation.Properties.Compatible
d_Compatible_110 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  ()
d_Compatible_110 = erased
-- Untyped.Relation.Properties.Compatible₂
d_Compatible'8322'_122 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  ()
d_Compatible'8322'_122 = erased
-- Untyped.Relation.Properties.Graph
d_Graph_138 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_Graph_138 = erased
-- Untyped.Relation.Properties.Refines
d_Refines_146 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Refines_146 = erased
-- Untyped.Relation.Properties.Graph?
d_Graph'63'_156 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_Graph'63'_156 = erased
-- Untyped.Relation.Properties.Refines?
d_Refines'63'_164 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Refines'63'_164 = erased
-- Untyped.Relation.Properties.Refines?-⊆
d_Refines'63''45''8838'_184 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_Refines'63''45''8838'_184 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_Refines'63''45''8838'_184 v3 v4 v5 v6 v7 v8
du_Refines'63''45''8838'_184 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_Refines'63''45''8838'_184 v0 v1 v2 v3 v4 v5
  = coe v0 v2 v3 v4 (coe v1 v2 v3 v4 v5)
