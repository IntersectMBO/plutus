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

module MAlonzo.Code.Algebra.Solver.Ring where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Definitions.RawSemiring
import qualified MAlonzo.Code.Algebra.Properties.Semiring.Exp
import qualified MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing
import qualified MAlonzo.Code.Algebra.Solver.Ring.Lemmas
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Reflection
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Solver.Ring.C.Carrier
d_Carrier_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) -> ()
d_Carrier_66 = erased
-- Algebra.Solver.Ring._._*_
d__'42'__74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'42'__74 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du__'42'__74 v5
du__'42'__74 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'42'__74 v0
  = coe
      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
      (coe v0)
-- Algebra.Solver.Ring._._+_
d__'43'__76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'43'__76 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du__'43'__76 v5
du__'43'__76 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'43'__76 v0
  = coe
      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
      (coe v0)
-- Algebra.Solver.Ring._._≈_
d__'8776'__78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) -> AgdaAny -> AgdaAny -> ()
d__'8776'__78 = erased
-- Algebra.Solver.Ring._.-_
d_'45'__162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) -> AgdaAny -> AgdaAny
d_'45'__162 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du_'45'__162 v5
du_'45'__162 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> AgdaAny
du_'45'__162 v0
  = coe
      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
      (coe v0)
-- Algebra.Solver.Ring._.0#
d_0'35'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) -> AgdaAny
d_0'35'_170 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du_0'35'_170 v5
du_0'35'_170 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny
du_0'35'_170 v0
  = coe
      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
      (coe v0)
-- Algebra.Solver.Ring._.1#
d_1'35'_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) -> AgdaAny
d_1'35'_172 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du_1'35'_172 v5
du_1'35'_172 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny
du_1'35'_172 v0
  = coe
      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
      (coe v0)
-- Algebra.Solver.Ring._.Carrier
d_Carrier_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) -> ()
d_Carrier_174 = erased
-- Algebra.Solver.Ring._.⟦_⟧
d_'10214'_'10215'_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) -> AgdaAny -> AgdaAny
d_'10214'_'10215'_358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_'10214'_'10215'_358 v6
du_'10214'_'10215'_358 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  AgdaAny -> AgdaAny
du_'10214'_'10215'_358 v0
  = coe
      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'10214'_'10215'_756
      (coe v0)
-- Algebra.Solver.Ring._._^_
d__'94'__362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  AgdaAny -> Integer -> AgdaAny
d__'94'__362 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du__'94'__362 v5
du__'94'__362 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  AgdaAny -> Integer -> AgdaAny
du__'94'__362 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Bundles.du_semiring_2600
              (coe
                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.du_commutativeSemiring_320
                 (coe v0)) in
    coe
      (coe
         MAlonzo.Code.Algebra.Definitions.RawSemiring.du__'94'__90
         (coe
            MAlonzo.Code.Algebra.Bundles.du_rawSemiring_2260
            (coe
               MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
               (coe v1))))
-- Algebra.Solver.Ring.Op
d_Op_418 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_Op_418 = C_'91''43''93'_420 | C_'91''42''93'_422
-- Algebra.Solver.Ring.Polynomial
d_Polynomial_426 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_Polynomial_426
  = C_op_436 T_Op_418 T_Polynomial_426 T_Polynomial_426 |
    C_con_440 AgdaAny | C_var_444 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C__'58''94'__450 T_Polynomial_426 Integer |
    C_'58''45'__454 T_Polynomial_426
-- Algebra.Solver.Ring._:+_
d__'58''43'__456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> T_Polynomial_426 -> T_Polynomial_426 -> T_Polynomial_426
d__'58''43'__456 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du__'58''43'__456
du__'58''43'__456 ::
  T_Polynomial_426 -> T_Polynomial_426 -> T_Polynomial_426
du__'58''43'__456 = coe C_op_436 (coe C_'91''43''93'_420)
-- Algebra.Solver.Ring._:*_
d__'58''42'__458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> T_Polynomial_426 -> T_Polynomial_426 -> T_Polynomial_426
d__'58''42'__458 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du__'58''42'__458
du__'58''42'__458 ::
  T_Polynomial_426 -> T_Polynomial_426 -> T_Polynomial_426
du__'58''42'__458 = coe C_op_436 (coe C_'91''42''93'_422)
-- Algebra.Solver.Ring._:-_
d__'58''45'__460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> T_Polynomial_426 -> T_Polynomial_426 -> T_Polynomial_426
d__'58''45'__460 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du__'58''45'__460 v9 v10
du__'58''45'__460 ::
  T_Polynomial_426 -> T_Polynomial_426 -> T_Polynomial_426
du__'58''45'__460 v0 v1
  = coe du__'58''43'__456 v0 (coe C_'58''45'__454 (coe v1))
-- Algebra.Solver.Ring._:×_
d__'58''215'__466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> Integer -> T_Polynomial_426 -> T_Polynomial_426
d__'58''215'__466 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du__'58''215'__466 v4 v9 v10
du__'58''215'__466 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  Integer -> T_Polynomial_426 -> T_Polynomial_426
du__'58''215'__466 v0 v1 v2
  = case coe v1 of
      0 -> coe
             C_con_440
             (coe MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0))
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                du__'58''43'__456 v2
                (coe du__'58''215'__466 (coe v0) (coe v3) (coe v2)))
-- Algebra.Solver.Ring.sem
d_sem_474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  T_Op_418 -> AgdaAny -> AgdaAny -> AgdaAny
d_sem_474 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 = du_sem_474 v5 v8
du_sem_474 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  T_Op_418 -> AgdaAny -> AgdaAny -> AgdaAny
du_sem_474 v0 v1
  = case coe v1 of
      C_'91''43''93'_420
        -> coe
             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
             (coe v0)
      C_'91''42''93'_422
        -> coe
             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
             (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.Env
d_Env_476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) -> Integer -> ()
d_Env_476 = erased
-- Algebra.Solver.Ring.⟦_⟧
d_'10214'_'10215'_478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_Polynomial_426 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'10214'_'10215'_478 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 v9 v10
  = du_'10214'_'10215'_478 v5 v6 v9 v10
du_'10214'_'10215'_478 ::
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  T_Polynomial_426 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
du_'10214'_'10215'_478 v0 v1 v2 v3
  = case coe v2 of
      C_op_436 v4 v5 v6
        -> coe
             MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
             (coe du_'10214'_'10215'_478 (coe v0) (coe v1) (coe v5) (coe v3))
             (coe du_sem_474 (coe v0) (coe v4))
             (coe du_'10214'_'10215'_478 (coe v0) (coe v1) (coe v6) (coe v3))
      C_con_440 v4
        -> coe
             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'10214'_'10215'_756
             v1 v4
      C_var_444 v4
        -> coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v3) (coe v4)
      C__'58''94'__450 v4 v5
        -> coe
             MAlonzo.Code.Algebra.Definitions.RawSemiring.du__'94'__90
             (coe
                MAlonzo.Code.Algebra.Bundles.du_rawSemiring_2260
                (coe
                   MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                   (coe
                      MAlonzo.Code.Algebra.Bundles.du_semiring_2600
                      (coe
                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.du_commutativeSemiring_320
                         (coe v0)))))
             (coe du_'10214'_'10215'_478 (coe v0) (coe v1) (coe v4) (coe v3))
             (coe v5)
      C_'58''45'__454 v4
        -> coe
             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
             v0 (coe du_'10214'_'10215'_478 (coe v0) (coe v1) (coe v4) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.HNF
d_HNF_506 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_HNF_506
  = C_'8709'_510 | C__'42'x'43'__512 T_HNF_506 T_Normal_508
-- Algebra.Solver.Ring.Normal
d_Normal_508 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_Normal_508 = C_con_514 AgdaAny | C_poly_516 T_HNF_506
-- Algebra.Solver.Ring.⟦_⟧H
d_'10214'_'10215'H_518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_HNF_506 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'10214'_'10215'H_518 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      C_'8709'_510
        -> coe
             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
             (coe v5)
      C__'42'x'43'__512 v12 v13
        -> case coe v10 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v15 v16
               -> coe
                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                    v5
                    (coe
                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                       v5
                       (d_'10214'_'10215'H_518
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v8) (coe v12)
                          (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v15 v16))
                       v15)
                    (d_'10214'_'10215'N_520
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8) (coe v13) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.⟦_⟧N
d_'10214'_'10215'N_520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_Normal_508 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'10214'_'10215'N_520 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      C_con_514 v11
        -> coe
             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'10214'_'10215'_756
             v6 v11
      C_poly_516 v12
        -> let v13 = subInt (coe v8) (coe (1 :: Integer)) in
           coe
             (coe
                d_'10214'_'10215'H_518 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v13) (coe v12) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring._≈H_
d__'8776'H__536 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T__'8776'H__536
  = C_'8709'_540 | C__'42'x'43'__552 T__'8776'H__536 T__'8776'N__538
-- Algebra.Solver.Ring._≈N_
d__'8776'N__538 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T__'8776'N__538
  = C_con_558 AgdaAny | C_poly_566 T__'8776'H__536
-- Algebra.Solver.Ring._≟H_
d__'8799'H__568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> T_HNF_506 -> T_HNF_506 -> Maybe T__'8776'H__536
d__'8799'H__568 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      C_'8709'_510
        -> case coe v10 of
             C_'8709'_510
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_'8709'_540)
             C__'42'x'43'__512 v13 v14
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'42'x'43'__512 v12 v13
        -> let v14 = subInt (coe v8) (coe (1 :: Integer)) in
           coe
             (case coe v10 of
                C_'8709'_510 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                C__'42'x'43'__512 v16 v17
                  -> let v18
                           = d__'8799'H__568
                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                               (coe v7) (coe v8) (coe v12) (coe v16) in
                     coe
                       (let v19
                              = d__'8799'N__570
                                  (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                  (coe v7) (coe v14) (coe v13) (coe v17) in
                        coe
                          (case coe v18 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                               -> case coe v19 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe C__'42'x'43'__552 v20 v21)
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v19
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> case coe v19 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v19
                                    _ -> coe v18
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring._≟N_
d__'8799'N__570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> T_Normal_508 -> T_Normal_508 -> Maybe T__'8776'N__538
d__'8799'N__570 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      C_con_514 v11
        -> case coe v10 of
             C_con_514 v12
               -> let v13 = coe v7 v11 v12 in
                  coe
                    (case coe v13 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_con_558 v14)
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v13
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poly_516 v12
        -> case coe v10 of
             C_poly_516 v14
               -> let v15
                        = d__'8799'H__568
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8) (coe v12) (coe v14) in
                  coe
                    (case coe v15 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_poly_566 v16)
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v15
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.⟦_⟧H-cong
d_'10214'_'10215'H'45'cong_654 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_HNF_506 ->
  T_HNF_506 ->
  T__'8776'H__536 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'10214'_'10215'H'45'cong_654 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                               v11 v12
  = case coe v11 of
      C_'8709'_540
        -> coe
             MAlonzo.Code.Relation.Binary.Structures.d_refl_34
             (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                (coe
                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                   (coe
                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                      (coe
                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                         (coe
                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                            (coe
                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                  (coe
                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                     (coe
                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                        (coe v5))))))))))
             (d_'10214'_'10215'H_518
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe C_'8709'_510) (coe v12))
      C__'42'x'43'__552 v18 v19
        -> case coe v9 of
             C__'42'x'43'__512 v21 v22
               -> case coe v10 of
                    C__'42'x'43'__512 v24 v25
                      -> case coe v12 of
                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v27 v28
                             -> coe
                                  MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                  (coe
                                     MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                     (coe
                                        d_'10214'_'10215'H'45'cong_654 (coe v0) (coe v1) (coe v2)
                                        (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                        (coe v21) (coe v24) (coe v18)
                                        (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v27 v28))
                                     (coe
                                        MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                                        (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                           (coe
                                              MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                              (coe
                                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                 (coe
                                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                    (coe v5)))))
                                        (d_'10214'_'10215'H_518
                                           (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                           (coe v6) (coe v7) (coe v8) (coe v21)
                                           (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v27 v28))
                                        (d_'10214'_'10215'H_518
                                           (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                           (coe v6) (coe v7) (coe v8) (coe v24)
                                           (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v27 v28))
                                        v27 v27)
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                        (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                           (coe
                                              MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                              (coe
                                                 MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                 (coe
                                                    MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                    (coe
                                                       MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                       (coe
                                                          MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                          (coe
                                                             MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                             (coe
                                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                                (coe
                                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                                   (coe v5))))))))))
                                        v27))
                                  (coe
                                     MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                     (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                        (coe
                                           MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                           (coe
                                              MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                              (coe
                                                 MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                 (coe
                                                    MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                    (coe
                                                       MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                       (coe
                                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                          (coe
                                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                             (coe v5)))))))))
                                     (coe
                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                        v5
                                        (d_'10214'_'10215'H_518
                                           (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                           (coe v6) (coe v7) (coe v8) (coe v21)
                                           (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v27 v28))
                                        v27)
                                     (coe
                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                        v5
                                        (d_'10214'_'10215'H_518
                                           (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                           (coe v6) (coe v7) (coe v8) (coe v24)
                                           (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v27 v28))
                                        v27)
                                     (d_'10214'_'10215'N_520
                                        (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                        (coe v6) (coe v7) (coe v8) (coe v22) (coe v28))
                                     (d_'10214'_'10215'N_520
                                        (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                        (coe v6) (coe v7) (coe v8) (coe v25) (coe v28)))
                                  (coe
                                     d_'10214'_'10215'N'45'cong_662 (coe v0) (coe v1) (coe v2)
                                     (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v22)
                                     (coe v25) (coe v19) (coe v28))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.⟦_⟧N-cong
d_'10214'_'10215'N'45'cong_662 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_Normal_508 ->
  T_Normal_508 ->
  T__'8776'N__538 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'10214'_'10215'N'45'cong_662 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                               v11 v12
  = case coe v11 of
      C_con_558 v15 -> coe v15
      C_poly_566 v16
        -> let v17 = subInt (coe v8) (coe (1 :: Integer)) in
           coe
             (case coe v9 of
                C_poly_516 v19
                  -> case coe v10 of
                       C_poly_516 v21
                         -> coe
                              d_'10214'_'10215'H'45'cong_654 (coe v0) (coe v1) (coe v2) (coe v3)
                              (coe v4) (coe v5) (coe v6) (coe v7) (coe v17) (coe v19) (coe v21)
                              (coe v16) (coe v12)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.0H
d_0H_678 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) -> Integer -> T_HNF_506
d_0H_678 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 = du_0H_678
du_0H_678 :: T_HNF_506
du_0H_678 = coe C_'8709'_510
-- Algebra.Solver.Ring.0N
d_0N_680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) -> Integer -> T_Normal_508
d_0N_680 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 v8 = du_0N_680 v4 v8
du_0N_680 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  Integer -> T_Normal_508
du_0N_680 v0 v1
  = case coe v1 of
      0 -> coe
             C_con_514
             (coe MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0))
      _ -> coe C_poly_516 (coe du_0H_678)
-- Algebra.Solver.Ring.1H
d_1H_684 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) -> Integer -> T_HNF_506
d_1H_684 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      C__'42'x'43'__512 (coe C_'8709'_510)
      (d_1N_686
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8))
-- Algebra.Solver.Ring.1N
d_1N_686 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) -> Integer -> T_Normal_508
d_1N_686 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      0 -> coe
             C_con_514
             (coe MAlonzo.Code.Algebra.Bundles.Raw.d_1'35'_308 (coe v4))
      _ -> let v9 = subInt (coe v8) (coe (1 :: Integer)) in
           coe
             (coe
                C_poly_516
                (d_1H_684
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                   (coe v7) (coe v9)))
-- Algebra.Solver.Ring._*x+HN_
d__'42'x'43'HN__692 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> T_HNF_506 -> T_Normal_508 -> T_HNF_506
d__'42'x'43'HN__692 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      C_'8709'_510
        -> let v12
                 = d__'8799'N__570
                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                     (coe v7) (coe v8) (coe v10) (coe du_0N_680 (coe v4) (coe v8)) in
           coe
             (case coe v12 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13 -> coe C_'8709'_510
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe C__'42'x'43'__512 (coe C_'8709'_510) v10
                _ -> MAlonzo.RTE.mazUnreachableError)
      C__'42'x'43'__512 v12 v13
        -> coe C__'42'x'43'__512 (coe C__'42'x'43'__512 v12 v13) v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring._+H_
d__'43'H__712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> T_HNF_506 -> T_HNF_506 -> T_HNF_506
d__'43'H__712 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      C_'8709'_510 -> coe v10
      C__'42'x'43'__512 v12 v13
        -> case coe v10 of
             C_'8709'_510 -> coe C__'42'x'43'__512 v12 v13
             C__'42'x'43'__512 v15 v16
               -> coe
                    d__'42'x'43'HN__692 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe
                       d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                       (coe v6) (coe v7) (coe v8) (coe v12) (coe v15))
                    (coe
                       d__'43'N__714 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                       (coe v6) (coe v7) (coe v8) (coe v13) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring._+N_
d__'43'N__714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> T_Normal_508 -> T_Normal_508 -> T_Normal_508
d__'43'N__714 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      C_con_514 v11
        -> case coe v10 of
             C_con_514 v12
               -> coe
                    C_con_514
                    (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v4 v11 v12)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poly_516 v12
        -> let v13 = subInt (coe v8) (coe (1 :: Integer)) in
           coe
             (case coe v10 of
                C_poly_516 v15
                  -> coe
                       C_poly_516
                       (d__'43'H__712
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v13) (coe v12) (coe v15))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring._*x+H_
d__'42'x'43'H__736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> T_HNF_506 -> T_HNF_506 -> T_HNF_506
d__'42'x'43'H__736 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      C_'8709'_510
        -> case coe v9 of
             C_'8709'_510 -> coe C_'8709'_510
             C__'42'x'43'__512 v13 v14
               -> coe
                    C__'42'x'43'__512 (coe C__'42'x'43'__512 v13 v14)
                    (coe du_0N_680 (coe v4) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'42'x'43'__512 v12 v13
        -> coe
             d__'42'x'43'HN__692 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8)
             (coe
                d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v7) (coe v8) (coe v9) (coe v12))
             (coe v13)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring._*NH_
d__'42'NH__748 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> T_Normal_508 -> T_HNF_506 -> T_HNF_506
d__'42'NH__748 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      C_'8709'_510 -> coe C_'8709'_510
      C__'42'x'43'__512 v12 v13
        -> let v14
                 = d__'8799'N__570
                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                     (coe v7) (coe v8) (coe v9) (coe du_0N_680 (coe v4) (coe v8)) in
           coe
             (case coe v14 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15 -> coe C_'8709'_510
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       C__'42'x'43'__512
                       (d__'42'NH__748
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v8) (coe v9) (coe v12))
                       (d__'42'N__754
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v8) (coe v9) (coe v13))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring._*HN_
d__'42'HN__750 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> T_HNF_506 -> T_Normal_508 -> T_HNF_506
d__'42'HN__750 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      C_'8709'_510 -> coe C_'8709'_510
      C__'42'x'43'__512 v12 v13
        -> let v14
                 = d__'8799'N__570
                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                     (coe v7) (coe v8) (coe v10) (coe du_0N_680 (coe v4) (coe v8)) in
           coe
             (case coe v14 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15 -> coe C_'8709'_510
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       C__'42'x'43'__512
                       (d__'42'HN__750
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v8) (coe v12) (coe v10))
                       (d__'42'N__754
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v8) (coe v13) (coe v10))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring._*H_
d__'42'H__752 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> T_HNF_506 -> T_HNF_506 -> T_HNF_506
d__'42'H__752 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      C_'8709'_510 -> coe C_'8709'_510
      C__'42'x'43'__512 v12 v13
        -> case coe v10 of
             C_'8709'_510 -> coe C_'8709'_510
             C__'42'x'43'__512 v15 v16
               -> coe
                    d__'42'x'43'HN__692 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v7) (coe v8)
                    (coe
                       d__'42'x'43'H__736 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v7) (coe v8)
                       (coe
                          d__'42'H__752 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                          (coe v6) (coe v7) (coe v8) (coe v12) (coe v15))
                       (coe
                          d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                          (coe v6) (coe v7) (coe v8)
                          (coe
                             d__'42'HN__750 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v5) (coe v6) (coe v7) (coe v8) (coe v12) (coe v16))
                          (coe
                             d__'42'NH__748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v5) (coe v6) (coe v7) (coe v8) (coe v13) (coe v15))))
                    (coe
                       d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                       (coe v6) (coe v7) (coe v8) (coe v13) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring._*N_
d__'42'N__754 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> T_Normal_508 -> T_Normal_508 -> T_Normal_508
d__'42'N__754 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      C_con_514 v11
        -> case coe v10 of
             C_con_514 v12
               -> coe
                    C_con_514
                    (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v4 v11 v12)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poly_516 v12
        -> let v13 = subInt (coe v8) (coe (1 :: Integer)) in
           coe
             (case coe v10 of
                C_poly_516 v15
                  -> coe
                       C_poly_516
                       (d__'42'H__752
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v13) (coe v12) (coe v15))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring._^N_
d__'94'N__824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> T_Normal_508 -> Integer -> T_Normal_508
d__'94'N__824 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      0 -> coe
             d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v8)
      _ -> let v11 = subInt (coe v10) (coe (1 :: Integer)) in
           coe
             (coe
                d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                (coe v6) (coe v7) (coe v8) (coe v9)
                (coe
                   d__'94'N__824 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8) (coe v9) (coe v11)))
-- Algebra.Solver.Ring.-H_
d_'45'H__832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> T_HNF_506 -> T_HNF_506
d_'45'H__832 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      d__'42'NH__748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8)
      (coe
         d_'45'N__834 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7) (coe v8)
         (coe
            d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
            (coe v6) (coe v7) (coe v8)))
      (coe v9)
-- Algebra.Solver.Ring.-N_
d_'45'N__834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> T_Normal_508 -> T_Normal_508
d_'45'N__834 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_con_514 v10
        -> coe
             C_con_514 (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v4 v10)
      C_poly_516 v11
        -> let v12 = subInt (coe v8) (coe (1 :: Integer)) in
           coe
             (coe
                C_poly_516
                (d_'45'H__832
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                   (coe v7) (coe v12) (coe v11)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.normalise-con
d_normalise'45'con_842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> AgdaAny -> T_Normal_508
d_normalise'45'con_842 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v8 of
      0 -> coe C_con_514 (coe v9)
      _ -> let v10 = subInt (coe v8) (coe (1 :: Integer)) in
           coe
             (coe
                C_poly_516
                (d__'42'x'43'HN__692
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                   (coe v7) (coe v10) (coe C_'8709'_510)
                   (coe
                      d_normalise'45'con_842 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                      (coe v5) (coe v6) (coe v7) (coe v10) (coe v9))))
-- Algebra.Solver.Ring.normalise-var
d_normalise'45'var_850 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Normal_508
d_normalise'45'var_850 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> let v11 = subInt (coe v8) (coe (1 :: Integer)) in
           coe
             (coe
                C_poly_516
                (coe
                   C__'42'x'43'__512
                   (coe
                      C__'42'x'43'__512 (coe C_'8709'_510)
                      (d_1N_686
                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                         (coe v7) (coe v11)))
                   (coe du_0N_680 (coe v4) (coe v11))))
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v11
        -> let v12 = subInt (coe v8) (coe (1 :: Integer)) in
           coe
             (coe
                C_poly_516
                (d__'42'x'43'HN__692
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                   (coe v7) (coe v12) (coe C_'8709'_510)
                   (coe
                      d_normalise'45'var_850 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                      (coe v5) (coe v6) (coe v7) (coe v12) (coe v11))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.normalise
d_normalise_854 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> T_Polynomial_426 -> T_Normal_508
d_normalise_854 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      C_op_436 v10 v11 v12
        -> case coe v10 of
             C_'91''43''93'_420
               -> coe
                    d__'43'N__714 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                    (coe v6) (coe v7) (coe v8)
                    (coe
                       d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v7) (coe v8) (coe v11))
                    (coe
                       d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v7) (coe v8) (coe v12))
             C_'91''42''93'_422
               -> coe
                    d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                    (coe v6) (coe v7) (coe v8)
                    (coe
                       d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v7) (coe v8) (coe v11))
                    (coe
                       d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v7) (coe v8) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_con_440 v10
        -> coe
             d_normalise'45'con_842 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
      C_var_444 v10
        -> coe
             d_normalise'45'var_850 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
      C__'58''94'__450 v10 v11
        -> coe
             d__'94'N__824 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v8)
             (coe
                d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v10))
             (coe v11)
      C_'58''45'__454 v10
        -> coe
             d_'45'N__834 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6) (coe v7) (coe v8)
             (coe
                d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v7) (coe v8) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.⟦_⟧↓
d_'10214'_'10215''8595'_874 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_Polynomial_426 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'10214'_'10215''8595'_874 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8)
      (coe
         d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9))
      (coe v10)
-- Algebra.Solver.Ring.0N-homo
d_0N'45'homo_884 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_0N'45'homo_884 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
        -> coe
             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'45'homo_764
             (coe v6)
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12
        -> coe
             MAlonzo.Code.Relation.Binary.Structures.d_refl_34
             (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                (coe
                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                   (coe
                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                      (coe
                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                         (coe
                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                            (coe
                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                  (coe
                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                     (coe
                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                        (coe v5))))))))))
             (d_'10214'_'10215'N_520
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8) (coe du_0N_680 (coe v4) (coe v8))
                (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.0≈⟦0⟧
d_0'8776''10214'0'10215'_896 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_Normal_508 ->
  T__'8776'N__538 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_0'8776''10214'0'10215'_896 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                 (coe v5))))))))))
      (d_'10214'_'10215'N_520
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
         (coe v7) (coe v8) (coe v9) (coe v11))
      (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
         (coe v5))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v12 v13 v14 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v14)
         (d_'10214'_'10215'N_520
            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
            (coe v7) (coe v8) (coe v9) (coe v11))
         (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
            (coe v5))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v12
                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                (coe v5) in
                      coe
                        (let v13
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                   (coe v12) in
                         coe
                           (let v14
                                  = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v13) in
                            coe
                              (let v15
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                         (coe v14) in
                               coe
                                 (let v16
                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe v15) in
                                  coe
                                    (let v17
                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe v16) in
                                     coe
                                       (let v18
                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                  (coe v17) in
                                        coe
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe v18)))))))))))))
            (d_'10214'_'10215'N_520
               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
               (coe v7) (coe v8) (coe v9) (coe v11))
            (d_'10214'_'10215'N_520
               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
               (coe v7) (coe v8) (coe du_0N_680 (coe v4) (coe v8)) (coe v11))
            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
               (coe v5))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v12
                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                   (coe v5) in
                         coe
                           (let v13
                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                      (coe v12) in
                            coe
                              (let v14
                                     = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                         (coe v13) in
                               coe
                                 (let v15
                                        = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                            (coe v14) in
                                  coe
                                    (let v16
                                           = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                               (coe v15) in
                                     coe
                                       (let v17
                                              = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                  (coe v16) in
                                        coe
                                          (let v18
                                                 = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                     (coe v17) in
                                           coe
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                   (coe v18)))))))))))))
               (d_'10214'_'10215'N_520
                  (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                  (coe v7) (coe v8) (coe du_0N_680 (coe v4) (coe v8)) (coe v11))
               (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                  (coe v5))
               (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                  (coe v5))
               (let v12
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v12
                                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                        (coe v5) in
                              coe
                                (let v13
                                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                           (coe v12) in
                                 coe
                                   (let v14
                                          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                              (coe v13) in
                                    coe
                                      (let v15
                                             = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                 (coe v14) in
                                       coe
                                         (let v16
                                                = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                    (coe v15) in
                                          coe
                                            (let v17
                                                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                       (coe v16) in
                                             coe
                                               (let v18
                                                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                          (coe v17) in
                                                coe
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                        (coe v18))))))))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v12))
                     (coe
                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                        (coe v5))))
               (d_0N'45'homo_884
                  (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                  (coe v7) (coe v8) (coe v11)))
            (d_'10214'_'10215'N'45'cong_662
               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
               (coe v7) (coe v8) (coe v9) (coe du_0N_680 (coe v4) (coe v8))
               (coe v10) (coe v11))))
-- Algebra.Solver.Ring.1N-homo
d_1N'45'homo_908 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_1N'45'homo_908 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
        -> coe
             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'45'homo_766
             (coe v6)
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12
        -> let v13 = subInt (coe v8) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                (\ v14 v15 v16 ->
                   coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v16)
                (coe
                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                   v5
                   (coe
                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                      v5
                      (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                         (coe v5))
                      v11)
                   (d_'10214'_'10215'N_520
                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                      (coe v7) (coe v13)
                      (coe
                         d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                         (coe v6) (coe v7) (coe v13))
                      (coe v12)))
                (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                   (coe v5))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                            (let v14
                                   = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                       (coe v5) in
                             coe
                               (let v15
                                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe v14) in
                                coe
                                  (let v16
                                         = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                             (coe v15) in
                                   coe
                                     (let v17
                                            = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                (coe v16) in
                                      coe
                                        (let v18
                                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                   (coe v17) in
                                         coe
                                           (let v19
                                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                      (coe v18) in
                                            coe
                                              (let v20
                                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                         (coe v19) in
                                               coe
                                                 (coe
                                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                    (coe
                                                       MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                       (coe v20)))))))))))))
                   (coe
                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                      v5
                      (coe
                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                         v5
                         (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                            (coe v5))
                         v11)
                      (d_'10214'_'10215'N_520
                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                         (coe v7) (coe v13)
                         (coe
                            d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                            (coe v6) (coe v7) (coe v13))
                         (coe v12)))
                   (coe
                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                      v5
                      (coe
                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                         v5
                         (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                            (coe v5))
                         v11)
                      (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                         (coe v5)))
                   (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                      (coe v5))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                               (let v14
                                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v5) in
                                coe
                                  (let v15
                                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                             (coe v14) in
                                   coe
                                     (let v16
                                            = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                (coe v15) in
                                      coe
                                        (let v17
                                               = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                   (coe v16) in
                                         coe
                                           (let v18
                                                  = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                      (coe v17) in
                                            coe
                                              (let v19
                                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                         (coe v18) in
                                               coe
                                                 (let v20
                                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                            (coe v19) in
                                                  coe
                                                    (coe
                                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                       (coe
                                                          MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                          (coe v20)))))))))))))
                      (coe
                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                         v5
                         (coe
                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                            v5
                            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                               (coe v5))
                            v11)
                         (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                            (coe v5)))
                      (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                         (coe v5))
                      (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                         (coe v5))
                      (let v14
                             = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (let v14
                                           = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                               (coe v5) in
                                     coe
                                       (let v15
                                              = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                  (coe v14) in
                                        coe
                                          (let v16
                                                 = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                     (coe v15) in
                                           coe
                                             (let v17
                                                    = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                        (coe v16) in
                                              coe
                                                (let v18
                                                       = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                           (coe v17) in
                                                 coe
                                                   (let v19
                                                          = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                              (coe v18) in
                                                    coe
                                                      (let v20
                                                             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                 (coe v19) in
                                                       coe
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                               (coe v20))))))))))) in
                       coe
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                               (coe v14))
                            (coe
                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                               (coe v5))))
                      (coe
                         MAlonzo.Code.Algebra.Solver.Ring.Lemmas.du_lemma'8326'_376 (coe v5)
                         (coe
                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                            (coe v5))
                         (coe v11)))
                   (coe
                      MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                            (coe
                               MAlonzo.Code.Algebra.Structures.d_isMagma_478
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                  (coe
                                     MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                     (coe
                                        MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                        (coe
                                           MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                           (coe
                                              MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                              (coe
                                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                 (coe
                                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                    (coe v5))))))))))
                         (coe
                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                            v5
                            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                               (coe v5))
                            v11))
                      (coe
                         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                         (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                            (coe
                               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                  (coe
                                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                     (coe
                                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                        (coe
                                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                           (coe
                                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                              (coe
                                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                 (coe v5)))))))))
                         (coe
                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                            v5
                            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                               (coe v5))
                            v11)
                         (coe
                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                            v5
                            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                               (coe v5))
                            v11)
                         (d_'10214'_'10215'N_520
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v13)
                            (coe
                               d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                               (coe v6) (coe v7) (coe v13))
                            (coe v12))
                         (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                            (coe v5)))
                      (coe
                         d_1N'45'homo_908 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                         (coe v5) (coe v6) (coe v7) (coe v13) (coe v12)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.*x+HN≈*x+
d_'42'x'43'HN'8776''42'x'43'_922 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_HNF_506 ->
  T_Normal_508 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'42'x'43'HN'8776''42'x'43'_922 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                 v11
  = case coe v9 of
      C_'8709'_510
        -> case coe v11 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v14 v15
               -> let v16
                        = d__'8799'N__570
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8) (coe v10) (coe du_0N_680 (coe v4) (coe v8)) in
                  coe
                    (case coe v16 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                         -> coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                              (\ v18 v19 v20 ->
                                 coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36
                                   v20)
                              (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                 (coe v5))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v5
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v5
                                    (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                       (coe v5))
                                    v14)
                                 (d_'10214'_'10215'N_520
                                    (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                    (coe v7) (coe v8) (coe v10) (coe v15)))
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (let v18
                                                 = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                     (coe v5) in
                                           coe
                                             (let v19
                                                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                        (coe v18) in
                                              coe
                                                (let v20
                                                       = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                           (coe v19) in
                                                 coe
                                                   (let v21
                                                          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                              (coe v20) in
                                                    coe
                                                      (let v22
                                                             = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                 (coe v21) in
                                                       coe
                                                         (let v23
                                                                = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                    (coe v22) in
                                                          coe
                                                            (let v24
                                                                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                       (coe v23) in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                     (coe v24)))))))))))))
                                 (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                    (coe v5))
                                 (d_'10214'_'10215'N_520
                                    (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                    (coe v7) (coe v8) (coe v10) (coe v15))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v5
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v5
                                       (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                          (coe v5))
                                       v14)
                                    (d_'10214'_'10215'N_520
                                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                       (coe v6) (coe v7) (coe v8) (coe v10) (coe v15)))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                             (let v18
                                                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                        (coe v5) in
                                              coe
                                                (let v19
                                                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                           (coe v18) in
                                                 coe
                                                   (let v20
                                                          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                              (coe v19) in
                                                    coe
                                                      (let v21
                                                             = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                                 (coe v20) in
                                                       coe
                                                         (let v22
                                                                = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                    (coe v21) in
                                                          coe
                                                            (let v23
                                                                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                       (coe v22) in
                                                             coe
                                                               (let v24
                                                                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                          (coe v23) in
                                                                coe
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                     (coe
                                                                        MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                        (coe v24)))))))))))))
                                    (d_'10214'_'10215'N_520
                                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                       (coe v6) (coe v7) (coe v8) (coe v10) (coe v15))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v5
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v5
                                          (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                             (coe v5))
                                          v14)
                                       (d_'10214'_'10215'N_520
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8) (coe v10) (coe v15)))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v5
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v5
                                          (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                             (coe v5))
                                          v14)
                                       (d_'10214'_'10215'N_520
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8) (coe v10) (coe v15)))
                                    (let v18
                                           = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                               (coe
                                                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                  (let v18
                                                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                             (coe v5) in
                                                   coe
                                                     (let v19
                                                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                                (coe v18) in
                                                      coe
                                                        (let v20
                                                               = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                                   (coe v19) in
                                                         coe
                                                           (let v21
                                                                  = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                                      (coe v20) in
                                                            coe
                                                              (let v22
                                                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                         (coe v21) in
                                                               coe
                                                                 (let v23
                                                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                            (coe v22) in
                                                                  coe
                                                                    (let v24
                                                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                               (coe v23) in
                                                                     coe
                                                                       (coe
                                                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                          (coe
                                                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                             (coe v24))))))))))) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                             (coe v18))
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                             v5
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v5
                                                (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                                   (coe v5))
                                                v14)
                                             (d_'10214'_'10215'N_520
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v10)
                                                (coe v15)))))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                       (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                            (coe
                                                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                                  (coe v5))))))))))
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v5
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                                (coe v5))
                                             v14)
                                          (d_'10214'_'10215'N_520
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v10) (coe v15)))
                                       (d_'10214'_'10215'N_520
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8) (coe v10) (coe v15))
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.Lemmas.du_lemma'8326'_376
                                          (coe v5)
                                          (coe
                                             d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2)
                                             (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                             (coe v10) (coe v15))
                                          (coe v14))))
                                 (d_0'8776''10214'0'10215'_896
                                    (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                    (coe v7) (coe v8) (coe v10) (coe v17) (coe v15)))
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                              (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                         (coe v5))))))))))
                              (d_'10214'_'10215'H_518
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                 (coe v7) (coe v8) (coe C__'42'x'43'__512 (coe C_'8709'_510) v10)
                                 (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v14 v15))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'42'x'43'__512 v13 v14
        -> coe
             MAlonzo.Code.Relation.Binary.Structures.d_refl_34
             (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                (coe
                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                   (coe
                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                      (coe
                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                         (coe
                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                            (coe
                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                  (coe
                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                     (coe
                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                        (coe v5))))))))))
             (d_'10214'_'10215'H_518
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8)
                (coe
                   d__'42'x'43'HN__692 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                   (coe v5) (coe v6) (coe v7) (coe v8) (coe C__'42'x'43'__512 v13 v14)
                   (coe v10))
                (coe v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.∅*x+HN-homo
d_'8709''42'x'43'HN'45'homo_964 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_Normal_508 ->
  AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'8709''42'x'43'HN'45'homo_964 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                v11
  = let v12
          = d__'8799'N__570
              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
              (coe v7) (coe v8) (coe v9) (coe du_0N_680 (coe v4) (coe v8)) in
    coe
      (case coe v12 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
           -> coe
                d_0'8776''10214'0'10215'_896 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v13)
                (coe v11)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Algebra.Solver.Ring.Lemmas.du_lemma'8326'_376 (coe v5)
                (coe
                   d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v11))
                (coe v10)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Solver.Ring.+H-homo
d_'43'H'45'homo_998 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_HNF_506 ->
  T_HNF_506 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'43'H'45'homo_998 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v9 of
      C_'8709'_510
        -> coe
             MAlonzo.Code.Relation.Binary.Structures.d_sym_36
             (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                (coe
                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                   (coe
                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                      (coe
                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                         (coe
                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                            (coe
                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                  (coe
                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                     (coe
                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                        (coe v5))))))))))
             (coe
                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                v5
                (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                   (coe v5))
                (d_'10214'_'10215'H_518
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                   (coe v7) (coe v8)
                   (coe
                      d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                      (coe v6) (coe v7) (coe v8) (coe C_'8709'_510) (coe v10))
                   (coe v11)))
             (d_'10214'_'10215'H_518
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8)
                (coe
                   d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8) (coe C_'8709'_510) (coe v10))
                (coe v11))
             (let v13
                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                        (coe v5) in
              coe
                (let v14
                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                           (coe v13) in
                 coe
                   (let v15
                          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v14) in
                    coe
                      (let v16
                             = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                 (coe v15) in
                       coe
                         (let v17
                                = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                    (coe v16) in
                          coe
                            (coe
                               MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                               (MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v17))
                               (d_'10214'_'10215'H_518
                                  (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                  (coe v7) (coe v8)
                                  (coe
                                     d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                     (coe v5) (coe v6) (coe v7) (coe v8) (coe C_'8709'_510)
                                     (coe v10))
                                  (coe v11))))))))
      C__'42'x'43'__512 v13 v14
        -> case coe v10 of
             C_'8709'_510
               -> coe
                    MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                    (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                       (coe
                          MAlonzo.Code.Algebra.Structures.d_isMagma_478
                          (coe
                             MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                             (coe
                                MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                            (coe
                                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                               (coe v5))))))))))
                    (coe
                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                       v5
                       (d_'10214'_'10215'H_518
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v8)
                          (coe
                             d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                             (coe v6) (coe v7) (coe v8) (coe C__'42'x'43'__512 v13 v14)
                             (coe C_'8709'_510))
                          (coe v11))
                       (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                          (coe v5)))
                    (d_'10214'_'10215'H_518
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8)
                       (coe
                          d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                          (coe v6) (coe v7) (coe v8) (coe C__'42'x'43'__512 v13 v14)
                          (coe C_'8709'_510))
                       (coe v11))
                    (let v16
                           = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                               (coe v5) in
                     coe
                       (let v17
                              = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                  (coe v16) in
                        coe
                          (let v18
                                 = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v17) in
                           coe
                             (let v19
                                    = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                        (coe v18) in
                              coe
                                (let v20
                                       = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                           (coe v19) in
                                 coe
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                                      (MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v20))
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8)
                                         (coe
                                            d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3)
                                            (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                            (coe C__'42'x'43'__512 v13 v14) (coe C_'8709'_510))
                                         (coe v11))))))))
             C__'42'x'43'__512 v16 v17
               -> case coe v11 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20
                      -> coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                           (\ v21 v22 v23 ->
                              coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v23)
                           (d_'10214'_'10215'H_518
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8)
                              (coe
                                 d__'42'x'43'HN__692 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                 (coe v5) (coe v6) (coe v7) (coe v8)
                                 (coe
                                    d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v13) (coe v16))
                                 (coe
                                    d__'43'N__714 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v17)))
                              (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                              v5
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v5
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v5
                                    (d_'10214'_'10215'H_518
                                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                       (coe v6) (coe v7) (coe v8) (coe v13)
                                       (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                    v19)
                                 (d_'10214'_'10215'N_520
                                    (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                    (coe v7) (coe v8) (coe v14) (coe v20)))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v5
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v5
                                    (d_'10214'_'10215'H_518
                                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                       (coe v6) (coe v7) (coe v8) (coe v16)
                                       (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                    v19)
                                 (d_'10214'_'10215'N_520
                                    (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                    (coe v7) (coe v8) (coe v17) (coe v20))))
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (let v21
                                              = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                  (coe v5) in
                                        coe
                                          (let v22
                                                 = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                     (coe v21) in
                                           coe
                                             (let v23
                                                    = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                        (coe v22) in
                                              coe
                                                (let v24
                                                       = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                           (coe v23) in
                                                 coe
                                                   (let v25
                                                          = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                              (coe v24) in
                                                    coe
                                                      (let v26
                                                             = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                 (coe v25) in
                                                       coe
                                                         (let v27
                                                                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                    (coe v26) in
                                                          coe
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                  (coe v27)))))))))))))
                              (d_'10214'_'10215'H_518
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                 (coe v7) (coe v8)
                                 (coe
                                    d__'42'x'43'HN__692 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                    (coe v5) (coe v6) (coe v7) (coe v8)
                                    (coe
                                       d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                       (coe v5) (coe v6) (coe v7) (coe v8) (coe v13) (coe v16))
                                    (coe
                                       d__'43'N__714 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                       (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v17)))
                                 (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v5
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v5
                                    (d_'10214'_'10215'H_518
                                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                       (coe v6) (coe v7) (coe v8)
                                       (coe
                                          d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                          (coe v5) (coe v6) (coe v7) (coe v8) (coe v13) (coe v16))
                                       (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                    v19)
                                 (d_'10214'_'10215'N_520
                                    (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                    (coe v7) (coe v8)
                                    (coe
                                       d__'43'N__714 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                       (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v17))
                                    (coe v20)))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v5
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v5
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v5
                                       (d_'10214'_'10215'H_518
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8) (coe v13)
                                          (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                       v19)
                                    (d_'10214'_'10215'N_520
                                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                       (coe v6) (coe v7) (coe v8) (coe v14) (coe v20)))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v5
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v5
                                       (d_'10214'_'10215'H_518
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8) (coe v16)
                                          (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                       v19)
                                    (d_'10214'_'10215'N_520
                                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                       (coe v6) (coe v7) (coe v8) (coe v17) (coe v20))))
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (let v21
                                                 = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                     (coe v5) in
                                           coe
                                             (let v22
                                                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                        (coe v21) in
                                              coe
                                                (let v23
                                                       = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                           (coe v22) in
                                                 coe
                                                   (let v24
                                                          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                              (coe v23) in
                                                    coe
                                                      (let v25
                                                             = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                 (coe v24) in
                                                       coe
                                                         (let v26
                                                                = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                    (coe v25) in
                                                          coe
                                                            (let v27
                                                                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                       (coe v26) in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                     (coe v27)))))))))))))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v5
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v5
                                       (d_'10214'_'10215'H_518
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8)
                                          (coe
                                             d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3)
                                             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                             (coe v16))
                                          (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                       v19)
                                    (d_'10214'_'10215'N_520
                                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                       (coe v6) (coe v7) (coe v8)
                                       (coe
                                          d__'43'N__714 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                          (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v17))
                                       (coe v20)))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v5
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v5
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v5
                                          (d_'10214'_'10215'H_518
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v13)
                                             (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                          (d_'10214'_'10215'H_518
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v16)
                                             (coe
                                                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20)))
                                       v19)
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v5
                                       (d_'10214'_'10215'N_520
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8) (coe v14) (coe v20))
                                       (d_'10214'_'10215'N_520
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8) (coe v17) (coe v20))))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v5
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v5
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v5
                                          (d_'10214'_'10215'H_518
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v13)
                                             (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                          v19)
                                       (d_'10214'_'10215'N_520
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8) (coe v14) (coe v20)))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v5
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v5
                                          (d_'10214'_'10215'H_518
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v16)
                                             (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                          v19)
                                       (d_'10214'_'10215'N_520
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8) (coe v17) (coe v20))))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                             (let v21
                                                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                        (coe v5) in
                                              coe
                                                (let v22
                                                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                           (coe v21) in
                                                 coe
                                                   (let v23
                                                          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                              (coe v22) in
                                                    coe
                                                      (let v24
                                                             = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                                 (coe v23) in
                                                       coe
                                                         (let v25
                                                                = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                    (coe v24) in
                                                          coe
                                                            (let v26
                                                                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                       (coe v25) in
                                                             coe
                                                               (let v27
                                                                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                          (coe v26) in
                                                                coe
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                     (coe
                                                                        MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                        (coe v27)))))))))))))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v5
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v5
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                             v5
                                             (d_'10214'_'10215'H_518
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20))
                                             (d_'10214'_'10215'H_518
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v16)
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20)))
                                          v19)
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v5
                                          (d_'10214'_'10215'N_520
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v14) (coe v20))
                                          (d_'10214'_'10215'N_520
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v17) (coe v20))))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v5
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v5
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (d_'10214'_'10215'H_518
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20))
                                             v19)
                                          (d_'10214'_'10215'N_520
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v14) (coe v20)))
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v5
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (d_'10214'_'10215'H_518
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v16)
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20))
                                             v19)
                                          (d_'10214'_'10215'N_520
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v17) (coe v20))))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v5
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v5
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (d_'10214'_'10215'H_518
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20))
                                             v19)
                                          (d_'10214'_'10215'N_520
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v14) (coe v20)))
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v5
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (d_'10214'_'10215'H_518
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v16)
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20))
                                             v19)
                                          (d_'10214'_'10215'N_520
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v17) (coe v20))))
                                    (let v21
                                           = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                               (coe
                                                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                  (let v21
                                                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                             (coe v5) in
                                                   coe
                                                     (let v22
                                                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                                (coe v21) in
                                                      coe
                                                        (let v23
                                                               = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                                   (coe v22) in
                                                         coe
                                                           (let v24
                                                                  = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                                      (coe v23) in
                                                            coe
                                                              (let v25
                                                                     = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                         (coe v24) in
                                                               coe
                                                                 (let v26
                                                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                            (coe v25) in
                                                                  coe
                                                                    (let v27
                                                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                               (coe v26) in
                                                                     coe
                                                                       (coe
                                                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                          (coe
                                                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                             (coe v27))))))))))) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                             (coe v21))
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                             v5
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                v5
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                   v5
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))
                                                   v19)
                                                (d_'10214'_'10215'N_520
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                                   (coe v20)))
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                v5
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                   v5
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8) (coe v16)
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))
                                                   v19)
                                                (d_'10214'_'10215'N_520
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v17)
                                                   (coe v20))))))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.Lemmas.du_lemma'8321'_280
                                       (coe v5)
                                       (coe
                                          d_'10214'_'10215'H_518 (coe v0) (coe v1) (coe v2) (coe v3)
                                          (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                          (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                       (coe
                                          d_'10214'_'10215'H_518 (coe v0) (coe v1) (coe v2) (coe v3)
                                          (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v16)
                                          (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                       (coe
                                          d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2) (coe v3)
                                          (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                          (coe v20))
                                       (coe
                                          d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2) (coe v3)
                                          (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v17)
                                          (coe v20))
                                       (coe v19)))
                                 (coe
                                    MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                    (coe
                                       MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                       (coe
                                          d_'43'H'45'homo_998 (coe v0) (coe v1) (coe v2) (coe v3)
                                          (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                          (coe v16)
                                          (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                                          (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                      (coe v5)))))
                                          (d_'10214'_'10215'H_518
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8)
                                             (coe
                                                d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3)
                                                (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                (coe v13) (coe v16))
                                             (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                             v5
                                             (d_'10214'_'10215'H_518
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20))
                                             (d_'10214'_'10215'H_518
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v16)
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20)))
                                          v19 v19)
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                          (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                                     (coe v5))))))))))
                                          v19))
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                       (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                         (coe
                                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                            (coe
                                                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                               (coe v5)))))))))
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v5
                                          (d_'10214'_'10215'H_518
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8)
                                             (coe
                                                d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3)
                                                (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                (coe v13) (coe v16))
                                             (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                          v19)
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v5
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                             v5
                                             (d_'10214'_'10215'H_518
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20))
                                             (d_'10214'_'10215'H_518
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v16)
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20)))
                                          v19)
                                       (d_'10214'_'10215'N_520
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8)
                                          (coe
                                             d__'43'N__714 (coe v0) (coe v1) (coe v2) (coe v3)
                                             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                             (coe v17))
                                          (coe v20))
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v5
                                          (d_'10214'_'10215'N_520
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v14) (coe v20))
                                          (d_'10214'_'10215'N_520
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v17) (coe v20))))
                                    (coe
                                       d_'43'N'45'homo_1008 (coe v0) (coe v1) (coe v2) (coe v3)
                                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                       (coe v17) (coe v20))))
                              (d_'42'x'43'HN'8776''42'x'43'_922
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                 (coe v7) (coe v8)
                                 (coe
                                    d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v13) (coe v16))
                                 (coe
                                    d__'43'N__714 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v17))
                                 (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.+N-homo
d_'43'N'45'homo_1008 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_Normal_508 ->
  T_Normal_508 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'43'N'45'homo_1008 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v9 of
      C_con_514 v12
        -> case coe v10 of
             C_con_514 v13
               -> coe
                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'43''45'homo_758
                    v6 v12 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poly_516 v13
        -> let v14 = subInt (coe v8) (coe (1 :: Integer)) in
           coe
             (case coe v10 of
                C_poly_516 v16
                  -> coe
                       d_'43'H'45'homo_998 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v7) (coe v14) (coe v13) (coe v16) (coe v11)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.*x+H-homo
d_'42'x'43'H'45'homo_1052 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_HNF_506 ->
  T_HNF_506 ->
  AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'42'x'43'H'45'homo_1052 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v9 of
      C_'8709'_510
        -> case coe v10 of
             C_'8709'_510
               -> coe
                    MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                    (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                       (coe
                          MAlonzo.Code.Algebra.Structures.d_isMagma_478
                          (coe
                             MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                             (coe
                                MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                            (coe
                                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                               (coe v5))))))))))
                    (coe
                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                       v5
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                          v5
                          (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                             (coe v5))
                          v11)
                       (d_'10214'_'10215'H_518
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v8)
                          (coe
                             d__'42'x'43'H__736 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v5) (coe v6) (coe v7) (coe v8) (coe C_'8709'_510)
                             (coe C_'8709'_510))
                          (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12)))
                    (d_'10214'_'10215'H_518
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8)
                       (coe
                          d__'42'x'43'H__736 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                          (coe v5) (coe v6) (coe v7) (coe v8) (coe C_'8709'_510)
                          (coe C_'8709'_510))
                       (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                    (coe
                       MAlonzo.Code.Algebra.Solver.Ring.Lemmas.du_lemma'8326'_376 (coe v5)
                       (coe
                          d_'10214'_'10215'H_518 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                          (coe v5) (coe v6) (coe v7) (coe v8)
                          (coe
                             d__'42'x'43'H__736 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v5) (coe v6) (coe v7) (coe v8) (coe C_'8709'_510)
                             (coe C_'8709'_510))
                          (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                       (coe v11))
             C__'42'x'43'__512 v15 v16
               -> coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                    (\ v17 v18 v19 ->
                       coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v19)
                    (d_'10214'_'10215'H_518
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8)
                       (coe
                          d__'42'x'43'HN__692 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                          (coe v5) (coe v6) (coe v7) (coe v8)
                          (coe
                             d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                             (coe v6) (coe v7) (coe v8) (coe C_'8709'_510) (coe v15))
                          (coe v16))
                       (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                    (coe
                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                       v5
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                          v5
                          (d_'10214'_'10215'H_518
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8) (coe C_'8709'_510)
                             (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                          v11)
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                          v5
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (d_'10214'_'10215'H_518
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v15)
                                (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                             v11)
                          (d_'10214'_'10215'N_520
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8) (coe v16) (coe v12))))
                    (coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                          (coe
                             MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v17
                                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                           (coe v5) in
                                 coe
                                   (let v18
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                              (coe v17) in
                                    coe
                                      (let v19
                                             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                 (coe v18) in
                                       coe
                                         (let v20
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                    (coe v19) in
                                          coe
                                            (let v21
                                                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                       (coe v20) in
                                             coe
                                               (let v22
                                                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                          (coe v21) in
                                                coe
                                                  (let v23
                                                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                             (coe v22) in
                                                   coe
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                           (coe v23)))))))))))))
                       (d_'10214'_'10215'H_518
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v8)
                          (coe
                             d__'42'x'43'HN__692 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v5) (coe v6) (coe v7) (coe v8)
                             (coe
                                d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                (coe v6) (coe v7) (coe v8) (coe C_'8709'_510) (coe v15))
                             (coe v16))
                          (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                          v5
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (d_'10214'_'10215'H_518
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8)
                                (coe
                                   d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe C_'8709'_510) (coe v15))
                                (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                             v11)
                          (d_'10214'_'10215'N_520
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8) (coe v16) (coe v12)))
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                          v5
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (d_'10214'_'10215'H_518
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe C_'8709'_510)
                                (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                             v11)
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'H_518
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v15)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                v11)
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v16) (coe v12))))
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v17
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                              (coe v5) in
                                    coe
                                      (let v18
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                 (coe v17) in
                                       coe
                                         (let v19
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                    (coe v18) in
                                          coe
                                            (let v20
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                       (coe v19) in
                                             coe
                                               (let v21
                                                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                          (coe v20) in
                                                coe
                                                  (let v22
                                                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                             (coe v21) in
                                                   coe
                                                     (let v23
                                                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                (coe v22) in
                                                      coe
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                              (coe v23)))))))))))))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'H_518
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8)
                                   (coe
                                      d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                      (coe v5) (coe v6) (coe v7) (coe v8) (coe C_'8709'_510)
                                      (coe v15))
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                v11)
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v16) (coe v12)))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe C_'8709'_510)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12)))
                                v11)
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v16) (coe v12)))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'H_518
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe C_'8709'_510)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                v11)
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   v11)
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v16) (coe v12))))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                      (let v17
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                 (coe v5) in
                                       coe
                                         (let v18
                                                = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                    (coe v17) in
                                          coe
                                            (let v19
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                       (coe v18) in
                                             coe
                                               (let v20
                                                      = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                          (coe v19) in
                                                coe
                                                  (let v21
                                                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                             (coe v20) in
                                                   coe
                                                     (let v22
                                                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                (coe v21) in
                                                      coe
                                                        (let v23
                                                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                   (coe v22) in
                                                         coe
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                              (coe
                                                                 MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                 (coe v23)))))))))))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe C_'8709'_510)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v15)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12)))
                                   v11)
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v16) (coe v12)))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe C_'8709'_510)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   v11)
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v15)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      v11)
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v16) (coe v12))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe C_'8709'_510)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   v11)
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v15)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      v11)
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v16) (coe v12))))
                             (let v17
                                    = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                           (let v17
                                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                      (coe v5) in
                                            coe
                                              (let v18
                                                     = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                         (coe v17) in
                                               coe
                                                 (let v19
                                                        = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                            (coe v18) in
                                                  coe
                                                    (let v20
                                                           = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                               (coe v19) in
                                                     coe
                                                       (let v21
                                                              = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                  (coe v20) in
                                                        coe
                                                          (let v22
                                                                 = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                     (coe v21) in
                                                           coe
                                                             (let v23
                                                                    = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                        (coe v22) in
                                                              coe
                                                                (coe
                                                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                   (coe
                                                                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                      (coe v23))))))))))) in
                              coe
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                      (coe v17))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                         v5
                                         (d_'10214'_'10215'H_518
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe C_'8709'_510)
                                            (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                         v11)
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                         v5
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                            v5
                                            (d_'10214'_'10215'H_518
                                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                               (coe v6) (coe v7) (coe v8) (coe v15)
                                               (coe
                                                  MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                            v11)
                                         (d_'10214'_'10215'N_520
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v16) (coe v12))))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.Lemmas.du_lemma'8320'_260 (coe v5)
                                (coe
                                   d_'10214'_'10215'H_518 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe C_'8709'_510)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                (coe
                                   d_'10214'_'10215'H_518 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v15)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                (coe
                                   d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v16) (coe v12))
                                (coe v11)))
                          (coe
                             MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                             (coe
                                MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                (coe
                                   d_'43'H'45'homo_998 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe C_'8709'_510) (coe v15)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                                   (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                            (coe
                                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                               (coe v5)))))
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8)
                                      (coe
                                         d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                         (coe v5) (coe v6) (coe v7) (coe v8) (coe C_'8709'_510)
                                         (coe v15))
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe C_'8709'_510)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v15)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12)))
                                   v11 v11)
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                        (coe
                                                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                           (coe
                                                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                              (coe v5))))))))))
                                   v11))
                             (coe
                                MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                  (coe
                                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                     (coe
                                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                        (coe v5)))))))))
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8)
                                      (coe
                                         d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                         (coe v5) (coe v6) (coe v7) (coe v8) (coe C_'8709'_510)
                                         (coe v15))
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   v11)
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe C_'8709'_510)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v15)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12)))
                                   v11)
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v16) (coe v12))
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v16) (coe v12)))
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                     (coe
                                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                        (coe
                                                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                           (coe v5))))))))))
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v16) (coe v12)))))
                       (d_'42'x'43'HN'8776''42'x'43'_922
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v8)
                          (coe
                             d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                             (coe v6) (coe v7) (coe v8) (coe C_'8709'_510) (coe v15))
                          (coe v16) (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'42'x'43'__512 v14 v15
        -> case coe v10 of
             C_'8709'_510
               -> coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                    (\ v17 v18 v19 ->
                       coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v19)
                    (coe
                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                       v5
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                          v5
                          (d_'10214'_'10215'H_518
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                             (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                          v11)
                       (d_'10214'_'10215'N_520
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v8) (coe du_0N_680 (coe v4) (coe v8)) (coe v12)))
                    (coe
                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                       v5
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                          v5
                          (d_'10214'_'10215'H_518
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                             (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                          v11)
                       (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                          (coe v5)))
                    (coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                          (coe
                             MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v17
                                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                           (coe v5) in
                                 coe
                                   (let v18
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                              (coe v17) in
                                    coe
                                      (let v19
                                             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                 (coe v18) in
                                       coe
                                         (let v20
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                    (coe v19) in
                                          coe
                                            (let v21
                                                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                       (coe v20) in
                                             coe
                                               (let v22
                                                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                          (coe v21) in
                                                coe
                                                  (let v23
                                                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                             (coe v22) in
                                                   coe
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                           (coe v23)))))))))))))
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                          v5
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (d_'10214'_'10215'H_518
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                                (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                             v11)
                          (d_'10214'_'10215'N_520
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8) (coe du_0N_680 (coe v4) (coe v8)) (coe v12)))
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                          v5
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (d_'10214'_'10215'H_518
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                                (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                             v11)
                          (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                             (coe v5)))
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                          v5
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (d_'10214'_'10215'H_518
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                                (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                             v11)
                          (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                             (coe v5)))
                       (let v17
                              = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                     (let v17
                                            = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                (coe v5) in
                                      coe
                                        (let v18
                                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                   (coe v17) in
                                         coe
                                           (let v19
                                                  = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                      (coe v18) in
                                            coe
                                              (let v20
                                                     = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                         (coe v19) in
                                               coe
                                                 (let v21
                                                        = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                            (coe v20) in
                                                  coe
                                                    (let v22
                                                           = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                               (coe v21) in
                                                     coe
                                                       (let v23
                                                              = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                  (coe v22) in
                                                        coe
                                                          (coe
                                                             MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                             (coe
                                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                (coe v23))))))))))) in
                        coe
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                (coe v17))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   v11)
                                (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                   (coe v5)))))
                       (coe
                          MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                          (coe
                             MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                  (coe
                                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                     (coe
                                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                        (coe v5))))))))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'H_518
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                v11))
                          (coe
                             MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                             (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                               (coe
                                                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                  (coe
                                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                     (coe v5)))))))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'H_518
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                v11)
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'H_518
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                v11)
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe du_0N_680 (coe v4) (coe v8)) (coe v12))
                             (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                (coe v5)))
                          (coe
                             d_0N'45'homo_884 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v5) (coe v6) (coe v7) (coe v8) (coe v12))))
             C__'42'x'43'__512 v17 v18
               -> coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                    (\ v19 v20 v21 ->
                       coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v21)
                    (d_'10214'_'10215'H_518
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8)
                       (coe
                          d__'42'x'43'HN__692 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                          (coe v5) (coe v6) (coe v7) (coe v8)
                          (coe
                             d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                             (coe v6) (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                             (coe v17))
                          (coe v18))
                       (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                    (coe
                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                       v5
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                          v5
                          (d_'10214'_'10215'H_518
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                             (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                          v11)
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                          v5
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (d_'10214'_'10215'H_518
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v17)
                                (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                             v11)
                          (d_'10214'_'10215'N_520
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8) (coe v18) (coe v12))))
                    (coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                          (coe
                             MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v19
                                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                           (coe v5) in
                                 coe
                                   (let v20
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                              (coe v19) in
                                    coe
                                      (let v21
                                             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                 (coe v20) in
                                       coe
                                         (let v22
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                    (coe v21) in
                                          coe
                                            (let v23
                                                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                       (coe v22) in
                                             coe
                                               (let v24
                                                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                          (coe v23) in
                                                coe
                                                  (let v25
                                                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                             (coe v24) in
                                                   coe
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                           (coe v25)))))))))))))
                       (d_'10214'_'10215'H_518
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v8)
                          (coe
                             d__'42'x'43'HN__692 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v5) (coe v6) (coe v7) (coe v8)
                             (coe
                                d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                (coe v6) (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                                (coe v17))
                             (coe v18))
                          (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                          v5
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (d_'10214'_'10215'H_518
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8)
                                (coe
                                   d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                   (coe v5) (coe v6) (coe v7) (coe v8)
                                   (coe C__'42'x'43'__512 v14 v15) (coe v17))
                                (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                             v11)
                          (d_'10214'_'10215'N_520
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8) (coe v18) (coe v12)))
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                          v5
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (d_'10214'_'10215'H_518
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                                (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                             v11)
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'H_518
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v17)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                v11)
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v18) (coe v12))))
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v19
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                              (coe v5) in
                                    coe
                                      (let v20
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                 (coe v19) in
                                       coe
                                         (let v21
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                    (coe v20) in
                                          coe
                                            (let v22
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                       (coe v21) in
                                             coe
                                               (let v23
                                                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                          (coe v22) in
                                                coe
                                                  (let v24
                                                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                             (coe v23) in
                                                   coe
                                                     (let v25
                                                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                (coe v24) in
                                                      coe
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                              (coe v25)))))))))))))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'H_518
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8)
                                   (coe
                                      d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                      (coe v5) (coe v6) (coe v7) (coe v8)
                                      (coe C__'42'x'43'__512 v14 v15) (coe v17))
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                v11)
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v18) (coe v12)))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v17)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12)))
                                v11)
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v18) (coe v12)))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'H_518
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                v11)
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v17)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   v11)
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v18) (coe v12))))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                      (let v19
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                 (coe v5) in
                                       coe
                                         (let v20
                                                = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                    (coe v19) in
                                          coe
                                            (let v21
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                       (coe v20) in
                                             coe
                                               (let v22
                                                      = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                          (coe v21) in
                                                coe
                                                  (let v23
                                                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                             (coe v22) in
                                                   coe
                                                     (let v24
                                                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                (coe v23) in
                                                      coe
                                                        (let v25
                                                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                   (coe v24) in
                                                         coe
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                              (coe
                                                                 MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                 (coe v25)))))))))))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v17)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12)))
                                   v11)
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v18) (coe v12)))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   v11)
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v17)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      v11)
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v18) (coe v12))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   v11)
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v17)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      v11)
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v18) (coe v12))))
                             (let v19
                                    = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                           (let v19
                                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                      (coe v5) in
                                            coe
                                              (let v20
                                                     = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                         (coe v19) in
                                               coe
                                                 (let v21
                                                        = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                            (coe v20) in
                                                  coe
                                                    (let v22
                                                           = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                               (coe v21) in
                                                     coe
                                                       (let v23
                                                              = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                  (coe v22) in
                                                        coe
                                                          (let v24
                                                                 = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                     (coe v23) in
                                                           coe
                                                             (let v25
                                                                    = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                        (coe v24) in
                                                              coe
                                                                (coe
                                                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                   (coe
                                                                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                      (coe v25))))))))))) in
                              coe
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                      (coe v19))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                         v5
                                         (d_'10214'_'10215'H_518
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8)
                                            (coe C__'42'x'43'__512 v14 v15)
                                            (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                         v11)
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                         v5
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                            v5
                                            (d_'10214'_'10215'H_518
                                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                               (coe v6) (coe v7) (coe v8) (coe v17)
                                               (coe
                                                  MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                            v11)
                                         (d_'10214'_'10215'N_520
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v18) (coe v12))))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.Lemmas.du_lemma'8320'_260 (coe v5)
                                (coe
                                   d_'10214'_'10215'H_518 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                   (coe C__'42'x'43'__512 v14 v15)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                (coe
                                   d_'10214'_'10215'H_518 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v17)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                (coe
                                   d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v18) (coe v12))
                                (coe v11)))
                          (coe
                             MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                             (coe
                                MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                (coe
                                   d_'43'H'45'homo_998 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                   (coe v5) (coe v6) (coe v7) (coe v8)
                                   (coe C__'42'x'43'__512 v14 v15) (coe v17)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                                   (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                            (coe
                                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                               (coe v5)))))
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8)
                                      (coe
                                         d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                         (coe v5) (coe v6) (coe v7) (coe v8)
                                         (coe C__'42'x'43'__512 v14 v15) (coe v17))
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v17)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12)))
                                   v11 v11)
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                        (coe
                                                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                           (coe
                                                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                              (coe v5))))))))))
                                   v11))
                             (coe
                                MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                  (coe
                                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                     (coe
                                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                        (coe v5)))))))))
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8)
                                      (coe
                                         d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                         (coe v5) (coe v6) (coe v7) (coe v8)
                                         (coe C__'42'x'43'__512 v14 v15) (coe v17))
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   v11)
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v17)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12)))
                                   v11)
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v18) (coe v12))
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v18) (coe v12)))
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                     (coe
                                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                        (coe
                                                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                           (coe v5))))))))))
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v18) (coe v12)))))
                       (d_'42'x'43'HN'8776''42'x'43'_922
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v8)
                          (coe
                             d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                             (coe v6) (coe v7) (coe v8) (coe C__'42'x'43'__512 v14 v15)
                             (coe v17))
                          (coe v18) (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.*NH-homo
d_'42'NH'45'homo_1082 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_Normal_508 ->
  T_HNF_506 ->
  AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'42'NH'45'homo_1082 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v10 of
      C_'8709'_510
        -> coe
             MAlonzo.Code.Relation.Binary.Structures.d_sym_36
             (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                (coe
                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                   (coe
                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                      (coe
                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                         (coe
                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                            (coe
                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                  (coe
                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                     (coe
                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                        (coe v5))))))))))
             (coe
                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                v5
                (d_'10214'_'10215'N_520
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                   (coe v7) (coe v8) (coe v9) (coe v12))
                (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                   (coe v5)))
             (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                (coe v5))
             (let v14
                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                        (coe v5) in
              coe
                (let v15
                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                           (coe v14) in
                 coe
                   (let v16
                          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v15) in
                    coe
                      (coe
                         MAlonzo.Code.Algebra.Structures.du_zero'691'_1380
                         (coe
                            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                            (coe v16))
                         (d_'10214'_'10215'N_520
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8) (coe v9) (coe v12))))))
      C__'42'x'43'__512 v14 v15
        -> let v16
                 = d__'8799'N__570
                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                     (coe v7) (coe v8) (coe v9) (coe du_0N_680 (coe v4) (coe v8)) in
           coe
             (case coe v16 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                  -> coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                       (\ v18 v19 v20 ->
                          coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v20)
                       (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                          (coe v5))
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                          v5
                          (d_'10214'_'10215'N_520
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8) (coe v9) (coe v12))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'H_518
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v14)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                v11)
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v15) (coe v12))))
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v18
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                              (coe v5) in
                                    coe
                                      (let v19
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                 (coe v18) in
                                       coe
                                         (let v20
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                    (coe v19) in
                                          coe
                                            (let v21
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                       (coe v20) in
                                             coe
                                               (let v22
                                                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                          (coe v21) in
                                                coe
                                                  (let v23
                                                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                             (coe v22) in
                                                   coe
                                                     (let v24
                                                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                (coe v23) in
                                                      coe
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                              (coe v24)))))))))))))
                          (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                             (coe v5))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                (coe v5))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v14)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   v11)
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v15) (coe v12))))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v9) (coe v12))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v14)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   v11)
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v15) (coe v12))))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                      (let v18
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                 (coe v5) in
                                       coe
                                         (let v19
                                                = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                    (coe v18) in
                                          coe
                                            (let v20
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                       (coe v19) in
                                             coe
                                               (let v21
                                                      = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                          (coe v20) in
                                                coe
                                                  (let v22
                                                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                             (coe v21) in
                                                   coe
                                                     (let v23
                                                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                (coe v22) in
                                                      coe
                                                        (let v24
                                                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                   (coe v23) in
                                                         coe
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                              (coe
                                                                 MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                 (coe v24)))))))))))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                   (coe v5))
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      v11)
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15) (coe v12))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v9) (coe v12))
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      v11)
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15) (coe v12))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v9) (coe v12))
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      v11)
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15) (coe v12))))
                             (let v18
                                    = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                           (let v18
                                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                      (coe v5) in
                                            coe
                                              (let v19
                                                     = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                         (coe v18) in
                                               coe
                                                 (let v20
                                                        = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                            (coe v19) in
                                                  coe
                                                    (let v21
                                                           = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                               (coe v20) in
                                                     coe
                                                       (let v22
                                                              = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                  (coe v21) in
                                                        coe
                                                          (let v23
                                                                 = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                     (coe v22) in
                                                           coe
                                                             (let v24
                                                                    = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                        (coe v23) in
                                                              coe
                                                                (coe
                                                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                   (coe
                                                                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                      (coe v24))))))))))) in
                              coe
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                      (coe v18))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v9) (coe v12))
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                         v5
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                            v5
                                            (d_'10214'_'10215'H_518
                                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                               (coe v6) (coe v7) (coe v8) (coe v14)
                                               (coe
                                                  MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                            v11)
                                         (d_'10214'_'10215'N_520
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v15) (coe v12))))))
                             (coe
                                MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                (coe
                                   d_0'8776''10214'0'10215'_896 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v17)
                                   (coe v12))
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                                   (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                            (coe
                                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                               (coe v5)))))
                                   (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                      (coe v5))
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v9) (coe v12))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                         v5
                                         (d_'10214'_'10215'H_518
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v14)
                                            (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                         v11)
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v15) (coe v12)))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                         v5
                                         (d_'10214'_'10215'H_518
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v14)
                                            (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                         v11)
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v15) (coe v12))))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                        (coe
                                                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                           (coe
                                                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                              (coe v5))))))))))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                         v5
                                         (d_'10214'_'10215'H_518
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v14)
                                            (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                         v11)
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v15) (coe v12))))))
                          (coe
                             MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                             (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                  (coe
                                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                     (coe
                                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                        (coe v5))))))))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                   (coe v5))
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      v11)
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15) (coe v12))))
                             (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                (coe v5))
                             (let v18
                                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                        (coe v5) in
                              coe
                                (let v19
                                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                           (coe v18) in
                                 coe
                                   (let v20
                                          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                              (coe v19) in
                                    coe
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.du_zero'737'_1378
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                                            (coe v20))
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                            v5
                                            (coe
                                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                               v5
                                               (d_'10214'_'10215'H_518
                                                  (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                  (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                                  (coe
                                                     MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11
                                                     v12))
                                               v11)
                                            (d_'10214'_'10215'N_520
                                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                               (coe v6) (coe v7) (coe v8) (coe v15)
                                               (coe v12)))))))))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                       (\ v17 v18 v19 ->
                          coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v19)
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                          v5
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (d_'10214'_'10215'H_518
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8)
                                (coe
                                   d__'42'NH__748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v14))
                                (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                             v11)
                          (d_'10214'_'10215'N_520
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8)
                             (coe
                                d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                (coe v6) (coe v7) (coe v8) (coe v9) (coe v15))
                             (coe v12)))
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                          v5
                          (d_'10214'_'10215'N_520
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8) (coe v9) (coe v12))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'H_518
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v14)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                v11)
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v15) (coe v12))))
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v17
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                              (coe v5) in
                                    coe
                                      (let v18
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                 (coe v17) in
                                       coe
                                         (let v19
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                    (coe v18) in
                                          coe
                                            (let v20
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                       (coe v19) in
                                             coe
                                               (let v21
                                                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                          (coe v20) in
                                                coe
                                                  (let v22
                                                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                             (coe v21) in
                                                   coe
                                                     (let v23
                                                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                (coe v22) in
                                                      coe
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                              (coe v23)))))))))))))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'H_518
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8)
                                   (coe
                                      d__'42'NH__748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v14))
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                v11)
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8)
                                (coe
                                   d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v15))
                                (coe v12)))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v9) (coe v12))
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v14)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12)))
                                v11)
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v9) (coe v12))
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v15) (coe v12))))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v9) (coe v12))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v14)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   v11)
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v15) (coe v12))))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                      (let v17
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                 (coe v5) in
                                       coe
                                         (let v18
                                                = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                    (coe v17) in
                                          coe
                                            (let v19
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                       (coe v18) in
                                             coe
                                               (let v20
                                                      = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                          (coe v19) in
                                                coe
                                                  (let v21
                                                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                             (coe v20) in
                                                   coe
                                                     (let v22
                                                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                (coe v21) in
                                                      coe
                                                        (let v23
                                                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                   (coe v22) in
                                                         coe
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                              (coe
                                                                 MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                 (coe v23)))))))))))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v9) (coe v12))
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12)))
                                   v11)
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v9) (coe v12))
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15) (coe v12))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v9) (coe v12))
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      v11)
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15) (coe v12))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v9) (coe v12))
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      v11)
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15) (coe v12))))
                             (let v17
                                    = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                           (let v17
                                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                      (coe v5) in
                                            coe
                                              (let v18
                                                     = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                         (coe v17) in
                                               coe
                                                 (let v19
                                                        = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                            (coe v18) in
                                                  coe
                                                    (let v20
                                                           = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                               (coe v19) in
                                                     coe
                                                       (let v21
                                                              = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                  (coe v20) in
                                                        coe
                                                          (let v22
                                                                 = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                     (coe v21) in
                                                           coe
                                                             (let v23
                                                                    = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                        (coe v22) in
                                                              coe
                                                                (coe
                                                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                   (coe
                                                                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                      (coe v23))))))))))) in
                              coe
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                      (coe v17))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v9) (coe v12))
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                         v5
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                            v5
                                            (d_'10214'_'10215'H_518
                                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                               (coe v6) (coe v7) (coe v8) (coe v14)
                                               (coe
                                                  MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                            v11)
                                         (d_'10214'_'10215'N_520
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v15) (coe v12))))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.Lemmas.du_lemma'8323'_324 (coe v5)
                                (coe
                                   d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v12))
                                (coe
                                   d_'10214'_'10215'H_518 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                (coe
                                   d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v15) (coe v12))
                                (coe v11)))
                          (coe
                             MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                             (coe
                                MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                (coe
                                   d_'42'NH'45'homo_1082 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v14)
                                   (coe v11) (coe v12))
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                                   (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                            (coe
                                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                               (coe v5)))))
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8)
                                      (coe
                                         d__'42'NH__748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v14))
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v9) (coe v12))
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12)))
                                   v11 v11)
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                        (coe
                                                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                           (coe
                                                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                              (coe v5))))))))))
                                   v11))
                             (coe
                                MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                  (coe
                                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                     (coe
                                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                        (coe v5)))))))))
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8)
                                      (coe
                                         d__'42'NH__748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v14))
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   v11)
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v9) (coe v12))
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12)))
                                   v11)
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8)
                                   (coe
                                      d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v15))
                                   (coe v12))
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v9) (coe v12))
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15) (coe v12))))
                             (coe
                                d_'42'N'45'homo_1114 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v15) (coe v12))))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.*HN-homo
d_'42'HN'45'homo_1094 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_HNF_506 ->
  T_Normal_508 ->
  AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'42'HN'45'homo_1094 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = case coe v9 of
      C_'8709'_510
        -> coe
             MAlonzo.Code.Relation.Binary.Structures.d_sym_36
             (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                (coe
                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                   (coe
                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                      (coe
                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                         (coe
                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                            (coe
                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                  (coe
                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                     (coe
                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                        (coe v5))))))))))
             (coe
                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                v5
                (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                   (coe v5))
                (d_'10214'_'10215'N_520
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                   (coe v7) (coe v8) (coe v10) (coe v12)))
             (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                (coe v5))
             (let v14
                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                        (coe v5) in
              coe
                (let v15
                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                           (coe v14) in
                 coe
                   (let v16
                          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v15) in
                    coe
                      (coe
                         MAlonzo.Code.Algebra.Structures.du_zero'737'_1378
                         (coe
                            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                            (coe v16))
                         (d_'10214'_'10215'N_520
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8) (coe v10) (coe v12))))))
      C__'42'x'43'__512 v14 v15
        -> let v16
                 = d__'8799'N__570
                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                     (coe v7) (coe v8) (coe v10) (coe du_0N_680 (coe v4) (coe v8)) in
           coe
             (case coe v16 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                  -> coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                       (\ v18 v19 v20 ->
                          coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v20)
                       (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                          (coe v5))
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                          v5
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'H_518
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v14)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                v11)
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v15) (coe v12)))
                          (d_'10214'_'10215'N_520
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8) (coe v10) (coe v12)))
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v18
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                              (coe v5) in
                                    coe
                                      (let v19
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                 (coe v18) in
                                       coe
                                         (let v20
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                    (coe v19) in
                                          coe
                                            (let v21
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                       (coe v20) in
                                             coe
                                               (let v22
                                                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                          (coe v21) in
                                                coe
                                                  (let v23
                                                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                             (coe v22) in
                                                   coe
                                                     (let v24
                                                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                (coe v23) in
                                                      coe
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                              (coe v24)))))))))))))
                          (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                             (coe v5))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v14)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   v11)
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v15) (coe v12)))
                             (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                (coe v5)))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v14)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   v11)
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v15) (coe v12)))
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v10) (coe v12)))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                      (let v18
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                 (coe v5) in
                                       coe
                                         (let v19
                                                = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                    (coe v18) in
                                          coe
                                            (let v20
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                       (coe v19) in
                                             coe
                                               (let v21
                                                      = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                          (coe v20) in
                                                coe
                                                  (let v22
                                                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                             (coe v21) in
                                                   coe
                                                     (let v23
                                                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                (coe v22) in
                                                      coe
                                                        (let v24
                                                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                   (coe v23) in
                                                         coe
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                              (coe
                                                                 MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                 (coe v24)))))))))))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      v11)
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15) (coe v12)))
                                (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                   (coe v5)))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      v11)
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15) (coe v12)))
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v10) (coe v12)))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      v11)
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15) (coe v12)))
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v10) (coe v12)))
                             (let v18
                                    = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                           (let v18
                                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                      (coe v5) in
                                            coe
                                              (let v19
                                                     = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                         (coe v18) in
                                               coe
                                                 (let v20
                                                        = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                            (coe v19) in
                                                  coe
                                                    (let v21
                                                           = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                               (coe v20) in
                                                     coe
                                                       (let v22
                                                              = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                  (coe v21) in
                                                        coe
                                                          (let v23
                                                                 = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                     (coe v22) in
                                                           coe
                                                             (let v24
                                                                    = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                        (coe v23) in
                                                              coe
                                                                (coe
                                                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                   (coe
                                                                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                      (coe v24))))))))))) in
                              coe
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                      (coe v18))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                         v5
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                            v5
                                            (d_'10214'_'10215'H_518
                                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                               (coe v6) (coe v7) (coe v8) (coe v14)
                                               (coe
                                                  MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                            v11)
                                         (d_'10214'_'10215'N_520
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v15) (coe v12)))
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v10) (coe v12)))))
                             (coe
                                MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                        (coe
                                                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                           (coe
                                                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                              (coe v5))))))))))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                         v5
                                         (d_'10214'_'10215'H_518
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v14)
                                            (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                         v11)
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v15) (coe v12))))
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                                   (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                            (coe
                                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                               (coe v5)))))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                         v5
                                         (d_'10214'_'10215'H_518
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v14)
                                            (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                         v11)
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v15) (coe v12)))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                         v5
                                         (d_'10214'_'10215'H_518
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v14)
                                            (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                         v11)
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v15) (coe v12)))
                                   (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                      (coe v5))
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v10) (coe v12)))
                                (coe
                                   d_0'8776''10214'0'10215'_896 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10) (coe v17)
                                   (coe v12))))
                          (coe
                             MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                             (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                  (coe
                                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                     (coe
                                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                        (coe v5))))))))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      v11)
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15) (coe v12)))
                                (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                   (coe v5)))
                             (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                (coe v5))
                             (let v18
                                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                        (coe v5) in
                              coe
                                (let v19
                                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                           (coe v18) in
                                 coe
                                   (let v20
                                          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                              (coe v19) in
                                    coe
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.du_zero'691'_1380
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                                            (coe v20))
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                            v5
                                            (coe
                                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                               v5
                                               (d_'10214'_'10215'H_518
                                                  (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                  (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                                  (coe
                                                     MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11
                                                     v12))
                                               v11)
                                            (d_'10214'_'10215'N_520
                                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                               (coe v6) (coe v7) (coe v8) (coe v15)
                                               (coe v12)))))))))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                       (\ v17 v18 v19 ->
                          coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v19)
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                          v5
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (d_'10214'_'10215'H_518
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8)
                                (coe
                                   d__'42'HN__750 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v10))
                                (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                             v11)
                          (d_'10214'_'10215'N_520
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8)
                             (coe
                                d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                (coe v6) (coe v7) (coe v8) (coe v15) (coe v10))
                             (coe v12)))
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                          v5
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'H_518
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v14)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                v11)
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v15) (coe v12)))
                          (d_'10214'_'10215'N_520
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8) (coe v10) (coe v12)))
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v17
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                              (coe v5) in
                                    coe
                                      (let v18
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                 (coe v17) in
                                       coe
                                         (let v19
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                    (coe v18) in
                                          coe
                                            (let v20
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                       (coe v19) in
                                             coe
                                               (let v21
                                                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                          (coe v20) in
                                                coe
                                                  (let v22
                                                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                             (coe v21) in
                                                   coe
                                                     (let v23
                                                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                (coe v22) in
                                                      coe
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                              (coe v23)))))))))))))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'H_518
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8)
                                   (coe
                                      d__'42'HN__750 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                      (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v10))
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                v11)
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8)
                                (coe
                                   d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v15) (coe v10))
                                (coe v12)))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v14)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v10) (coe v12)))
                                v11)
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v15) (coe v12))
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v10) (coe v12))))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v14)
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   v11)
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v15) (coe v12)))
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v10) (coe v12)))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                      (let v17
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                 (coe v5) in
                                       coe
                                         (let v18
                                                = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                    (coe v17) in
                                          coe
                                            (let v19
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                       (coe v18) in
                                             coe
                                               (let v20
                                                      = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                          (coe v19) in
                                                coe
                                                  (let v21
                                                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                             (coe v20) in
                                                   coe
                                                     (let v22
                                                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                (coe v21) in
                                                      coe
                                                        (let v23
                                                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                   (coe v22) in
                                                         coe
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                              (coe
                                                                 MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                 (coe v23)))))))))))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v10) (coe v12)))
                                   v11)
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15) (coe v12))
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v10) (coe v12))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      v11)
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15) (coe v12)))
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v10) (coe v12)))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      v11)
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15) (coe v12)))
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v10) (coe v12)))
                             (let v17
                                    = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                           (let v17
                                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                      (coe v5) in
                                            coe
                                              (let v18
                                                     = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                         (coe v17) in
                                               coe
                                                 (let v19
                                                        = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                            (coe v18) in
                                                  coe
                                                    (let v20
                                                           = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                               (coe v19) in
                                                     coe
                                                       (let v21
                                                              = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                  (coe v20) in
                                                        coe
                                                          (let v22
                                                                 = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                     (coe v21) in
                                                           coe
                                                             (let v23
                                                                    = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                        (coe v22) in
                                                              coe
                                                                (coe
                                                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                   (coe
                                                                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                      (coe v23))))))))))) in
                              coe
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                      (coe v17))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                         v5
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                            v5
                                            (d_'10214'_'10215'H_518
                                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                               (coe v6) (coe v7) (coe v8) (coe v14)
                                               (coe
                                                  MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                            v11)
                                         (d_'10214'_'10215'N_520
                                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                            (coe v6) (coe v7) (coe v8) (coe v15) (coe v12)))
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v10) (coe v12)))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.Lemmas.du_lemma'8322'_300 (coe v5)
                                (coe
                                   d_'10214'_'10215'H_518 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                (coe
                                   d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v15) (coe v12))
                                (coe
                                   d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v10) (coe v12))
                                (coe v11)))
                          (coe
                             MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                             (coe
                                MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                (coe
                                   d_'42'HN'45'homo_1094 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v10)
                                   (coe v11) (coe v12))
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                                   (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                            (coe
                                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                               (coe v5)))))
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8)
                                      (coe
                                         d__'42'HN__750 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                         (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v10))
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v10) (coe v12)))
                                   v11 v11)
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                        (coe
                                                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                           (coe
                                                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                              (coe v5))))))))))
                                   v11))
                             (coe
                                MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                  (coe
                                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                     (coe
                                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                        (coe v5)))))))))
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'H_518
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8)
                                      (coe
                                         d__'42'HN__750 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                         (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v10))
                                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                   v11)
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (d_'10214'_'10215'H_518
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v14)
                                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12))
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v8) (coe v10) (coe v12)))
                                   v11)
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8)
                                   (coe
                                      d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                      (coe v5) (coe v6) (coe v7) (coe v8) (coe v15) (coe v10))
                                   (coe v12))
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v15) (coe v12))
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v8) (coe v10) (coe v12))))
                             (coe
                                d_'42'N'45'homo_1114 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v15) (coe v10)
                                (coe v12))))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.*H-homo
d_'42'H'45'homo_1104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_HNF_506 ->
  T_HNF_506 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'42'H'45'homo_1104 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v9 of
      C_'8709'_510
        -> coe
             MAlonzo.Code.Relation.Binary.Structures.d_sym_36
             (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                (coe
                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                   (coe
                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                      (coe
                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                         (coe
                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                            (coe
                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                  (coe
                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                     (coe
                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                        (coe v5))))))))))
             (coe
                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                v5
                (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                   (coe v5))
                (d_'10214'_'10215'H_518
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                   (coe v7) (coe v8) (coe v10) (coe v11)))
             (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                (coe v5))
             (let v13
                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                        (coe v5) in
              coe
                (let v14
                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                           (coe v13) in
                 coe
                   (let v15
                          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v14) in
                    coe
                      (coe
                         MAlonzo.Code.Algebra.Structures.du_zero'737'_1378
                         (coe
                            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                            (coe v15))
                         (d_'10214'_'10215'H_518
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8) (coe v10) (coe v11))))))
      C__'42'x'43'__512 v13 v14
        -> case coe v10 of
             C_'8709'_510
               -> coe
                    MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                    (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                       (coe
                          MAlonzo.Code.Algebra.Structures.d_isMagma_478
                          (coe
                             MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                             (coe
                                MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                            (coe
                                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                               (coe v5))))))))))
                    (coe
                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                       v5
                       (d_'10214'_'10215'H_518
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v8) (coe C__'42'x'43'__512 v13 v14) (coe v11))
                       (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                          (coe v5)))
                    (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                       (coe v5))
                    (let v16
                           = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                               (coe v5) in
                     coe
                       (let v17
                              = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                  (coe v16) in
                        coe
                          (let v18
                                 = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v17) in
                           coe
                             (coe
                                MAlonzo.Code.Algebra.Structures.du_zero'691'_1380
                                (coe
                                   MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
                                   (coe v18))
                                (d_'10214'_'10215'H_518
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe C__'42'x'43'__512 v13 v14) (coe v11))))))
             C__'42'x'43'__512 v16 v17
               -> case coe v11 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20
                      -> coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                           (\ v21 v22 v23 ->
                              coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v23)
                           (d_'10214'_'10215'H_518
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                              (coe v7) (coe v8)
                              (coe
                                 d__'42'x'43'HN__692 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                 (coe v5) (coe v6) (coe v7) (coe v8)
                                 (coe
                                    d__'42'x'43'H__736 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                    (coe v5) (coe v6) (coe v7) (coe v8)
                                    (coe
                                       d__'42'H__752 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                       (coe v5) (coe v6) (coe v7) (coe v8) (coe v13) (coe v16))
                                    (coe
                                       d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                       (coe v5) (coe v6) (coe v7) (coe v8)
                                       (coe
                                          d__'42'HN__750 (coe v0) (coe v1) (coe v2) (coe v3)
                                          (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                          (coe v17))
                                       (coe
                                          d__'42'NH__748 (coe v0) (coe v1) (coe v2) (coe v3)
                                          (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                          (coe v16))))
                                 (coe
                                    d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v17)))
                              (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                           (coe
                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                              v5
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v5
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v5
                                    (d_'10214'_'10215'H_518
                                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                       (coe v6) (coe v7) (coe v8) (coe v13)
                                       (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                    v19)
                                 (d_'10214'_'10215'N_520
                                    (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                    (coe v7) (coe v8) (coe v14) (coe v20)))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v5
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v5
                                    (d_'10214'_'10215'H_518
                                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                       (coe v6) (coe v7) (coe v8) (coe v16)
                                       (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                    v19)
                                 (d_'10214'_'10215'N_520
                                    (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                    (coe v7) (coe v8) (coe v17) (coe v20))))
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (let v21
                                              = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                  (coe v5) in
                                        coe
                                          (let v22
                                                 = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                     (coe v21) in
                                           coe
                                             (let v23
                                                    = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                        (coe v22) in
                                              coe
                                                (let v24
                                                       = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                           (coe v23) in
                                                 coe
                                                   (let v25
                                                          = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                              (coe v24) in
                                                    coe
                                                      (let v26
                                                             = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                 (coe v25) in
                                                       coe
                                                         (let v27
                                                                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                    (coe v26) in
                                                          coe
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                  (coe v27)))))))))))))
                              (d_'10214'_'10215'H_518
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                 (coe v7) (coe v8)
                                 (coe
                                    d__'42'x'43'HN__692 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                    (coe v5) (coe v6) (coe v7) (coe v8)
                                    (coe
                                       d__'42'x'43'H__736 (coe v0) (coe v1) (coe v2) (coe v3)
                                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                       (coe
                                          d__'42'H__752 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                          (coe v5) (coe v6) (coe v7) (coe v8) (coe v13) (coe v16))
                                       (coe
                                          d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                          (coe v5) (coe v6) (coe v7) (coe v8)
                                          (coe
                                             d__'42'HN__750 (coe v0) (coe v1) (coe v2) (coe v3)
                                             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                             (coe v17))
                                          (coe
                                             d__'42'NH__748 (coe v0) (coe v1) (coe v2) (coe v3)
                                             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                             (coe v16))))
                                    (coe
                                       d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                       (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v17)))
                                 (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                 v5
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v5
                                    (d_'10214'_'10215'H_518
                                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                       (coe v6) (coe v7) (coe v8)
                                       (coe
                                          d__'42'x'43'H__736 (coe v0) (coe v1) (coe v2) (coe v3)
                                          (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                          (coe
                                             d__'42'H__752 (coe v0) (coe v1) (coe v2) (coe v3)
                                             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                             (coe v16))
                                          (coe
                                             d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3)
                                             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                             (coe
                                                d__'42'HN__750 (coe v0) (coe v1) (coe v2) (coe v3)
                                                (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                (coe v13) (coe v17))
                                             (coe
                                                d__'42'NH__748 (coe v0) (coe v1) (coe v2) (coe v3)
                                                (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                (coe v14) (coe v16))))
                                       (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                    v19)
                                 (d_'10214'_'10215'N_520
                                    (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                    (coe v7) (coe v8)
                                    (coe
                                       d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                       (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v17))
                                    (coe v20)))
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                 v5
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v5
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v5
                                       (d_'10214'_'10215'H_518
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8) (coe v13)
                                          (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                       v19)
                                    (d_'10214'_'10215'N_520
                                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                       (coe v6) (coe v7) (coe v8) (coe v14) (coe v20)))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v5
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v5
                                       (d_'10214'_'10215'H_518
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8) (coe v16)
                                          (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                       v19)
                                    (d_'10214'_'10215'N_520
                                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                       (coe v6) (coe v7) (coe v8) (coe v17) (coe v20))))
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (let v21
                                                 = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                     (coe v5) in
                                           coe
                                             (let v22
                                                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                        (coe v21) in
                                              coe
                                                (let v23
                                                       = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                           (coe v22) in
                                                 coe
                                                   (let v24
                                                          = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                              (coe v23) in
                                                    coe
                                                      (let v25
                                                             = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                 (coe v24) in
                                                       coe
                                                         (let v26
                                                                = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                    (coe v25) in
                                                          coe
                                                            (let v27
                                                                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                       (coe v26) in
                                                             coe
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                     (coe v27)))))))))))))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v5
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v5
                                       (d_'10214'_'10215'H_518
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8)
                                          (coe
                                             d__'42'x'43'H__736 (coe v0) (coe v1) (coe v2) (coe v3)
                                             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                             (coe
                                                d__'42'H__752 (coe v0) (coe v1) (coe v2) (coe v3)
                                                (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                (coe v13) (coe v16))
                                             (coe
                                                d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3)
                                                (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                (coe
                                                   d__'42'HN__750 (coe v0) (coe v1) (coe v2)
                                                   (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                   (coe v8) (coe v13) (coe v17))
                                                (coe
                                                   d__'42'NH__748 (coe v0) (coe v1) (coe v2)
                                                   (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                   (coe v8) (coe v14) (coe v16))))
                                          (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                       v19)
                                    (d_'10214'_'10215'N_520
                                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                       (coe v6) (coe v7) (coe v8)
                                       (coe
                                          d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                          (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v17))
                                       (coe v20)))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                    v5
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v5
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v5
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (d_'10214'_'10215'H_518
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8)
                                                (coe
                                                   d__'42'H__752 (coe v0) (coe v1) (coe v2) (coe v3)
                                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                   (coe v13) (coe v16))
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20))
                                             v19)
                                          (d_'10214'_'10215'H_518
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8)
                                             (coe
                                                d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3)
                                                (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                (coe
                                                   d__'42'HN__750 (coe v0) (coe v1) (coe v2)
                                                   (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                   (coe v8) (coe v13) (coe v17))
                                                (coe
                                                   d__'42'NH__748 (coe v0) (coe v1) (coe v2)
                                                   (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                   (coe v8) (coe v14) (coe v16)))
                                             (coe
                                                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20)))
                                       v19)
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v5
                                       (d_'10214'_'10215'N_520
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8) (coe v14) (coe v20))
                                       (d_'10214'_'10215'N_520
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8) (coe v17) (coe v20))))
                                 (coe
                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                    v5
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v5
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v5
                                          (d_'10214'_'10215'H_518
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v13)
                                             (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                          v19)
                                       (d_'10214'_'10215'N_520
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8) (coe v14) (coe v20)))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v5
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v5
                                          (d_'10214'_'10215'H_518
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v16)
                                             (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                          v19)
                                       (d_'10214'_'10215'N_520
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8) (coe v17) (coe v20))))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                             (let v21
                                                    = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                        (coe v5) in
                                              coe
                                                (let v22
                                                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                           (coe v21) in
                                                 coe
                                                   (let v23
                                                          = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                              (coe v22) in
                                                    coe
                                                      (let v24
                                                             = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                                 (coe v23) in
                                                       coe
                                                         (let v25
                                                                = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                    (coe v24) in
                                                          coe
                                                            (let v26
                                                                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                       (coe v25) in
                                                             coe
                                                               (let v27
                                                                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                          (coe v26) in
                                                                coe
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                     (coe
                                                                        MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                        (coe v27)))))))))))))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v5
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v5
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                             v5
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v5
                                                (d_'10214'_'10215'H_518
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8)
                                                   (coe
                                                      d__'42'H__752 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8) (coe v13) (coe v16))
                                                   (coe
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                      v20))
                                                v19)
                                             (d_'10214'_'10215'H_518
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8)
                                                (coe
                                                   d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3)
                                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                   (coe
                                                      d__'42'HN__750 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8) (coe v13) (coe v17))
                                                   (coe
                                                      d__'42'NH__748 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8) (coe v14) (coe v16)))
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20)))
                                          v19)
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v5
                                          (d_'10214'_'10215'N_520
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v14) (coe v20))
                                          (d_'10214'_'10215'N_520
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v17) (coe v20))))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                       v5
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v5
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                             v5
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v5
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                   v5
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8) (coe v16)
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20)))
                                                v19)
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                v5
                                                (d_'10214'_'10215'H_518
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8)
                                                   (coe
                                                      d__'42'HN__750 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8) (coe v13) (coe v17))
                                                   (coe
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                      v20))
                                                (d_'10214'_'10215'H_518
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8)
                                                   (coe
                                                      d__'42'NH__748 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8) (coe v14) (coe v16))
                                                   (coe
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                      v20))))
                                          v19)
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v5
                                          (d_'10214'_'10215'N_520
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v14) (coe v20))
                                          (d_'10214'_'10215'N_520
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v17) (coe v20))))
                                    (coe
                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                       v5
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v5
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (d_'10214'_'10215'H_518
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20))
                                             v19)
                                          (d_'10214'_'10215'N_520
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v14) (coe v20)))
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v5
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (d_'10214'_'10215'H_518
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v16)
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20))
                                             v19)
                                          (d_'10214'_'10215'N_520
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v17) (coe v20))))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                (let v21
                                                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                           (coe v5) in
                                                 coe
                                                   (let v22
                                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                              (coe v21) in
                                                    coe
                                                      (let v23
                                                             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                                 (coe v22) in
                                                       coe
                                                         (let v24
                                                                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                                    (coe v23) in
                                                          coe
                                                            (let v25
                                                                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                       (coe v24) in
                                                             coe
                                                               (let v26
                                                                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                          (coe v25) in
                                                                coe
                                                                  (let v27
                                                                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                             (coe v26) in
                                                                   coe
                                                                     (coe
                                                                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                        (coe
                                                                           MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                           (coe v27)))))))))))))
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v5
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                v5
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                      v5
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v13)
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20))
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v16)
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20)))
                                                   v19)
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                   v5
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8)
                                                      (coe
                                                         d__'42'HN__750 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v13) (coe v17))
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8)
                                                      (coe
                                                         d__'42'NH__748 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v14) (coe v16))
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))))
                                             v19)
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (d_'10214'_'10215'N_520
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                                (coe v20))
                                             (d_'10214'_'10215'N_520
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v17)
                                                (coe v20))))
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                          v5
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                v5
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                      v5
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v13)
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20))
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v16)
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20)))
                                                   v19)
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                      v5
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v13)
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20))
                                                      (d_'10214'_'10215'N_520
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v17) (coe v20)))
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                      v5
                                                      (d_'10214'_'10215'N_520
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v14) (coe v20))
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v16)
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20)))))
                                             v19)
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (d_'10214'_'10215'N_520
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                                (coe v20))
                                             (d_'10214'_'10215'N_520
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v17)
                                                (coe v20))))
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v5
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                             v5
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v5
                                                (d_'10214'_'10215'H_518
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                                   (coe
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                      v20))
                                                v19)
                                             (d_'10214'_'10215'N_520
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                                (coe v20)))
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                             v5
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v5
                                                (d_'10214'_'10215'H_518
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v16)
                                                   (coe
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                      v20))
                                                v19)
                                             (d_'10214'_'10215'N_520
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v17)
                                                (coe v20))))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                   (let v21
                                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                              (coe v5) in
                                                    coe
                                                      (let v22
                                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                                 (coe v21) in
                                                       coe
                                                         (let v23
                                                                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                                    (coe v22) in
                                                          coe
                                                            (let v24
                                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                                       (coe v23) in
                                                             coe
                                                               (let v25
                                                                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                          (coe v24) in
                                                                coe
                                                                  (let v26
                                                                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                             (coe v25) in
                                                                   coe
                                                                     (let v27
                                                                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                                (coe v26) in
                                                                      coe
                                                                        (coe
                                                                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                           (coe
                                                                              MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                              (coe v27)))))))))))))
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                             v5
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v5
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                      v5
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v13)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20))
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v16)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20)))
                                                      v19)
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                      v5
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v13)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20))
                                                         (d_'10214'_'10215'N_520
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v17) (coe v20)))
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'N_520
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v14) (coe v20))
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v16)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20)))))
                                                v19)
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v5
                                                (d_'10214'_'10215'N_520
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                                   (coe v20))
                                                (d_'10214'_'10215'N_520
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v17)
                                                   (coe v20))))
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                v5
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                   v5
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))
                                                   v19)
                                                (d_'10214'_'10215'N_520
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                                   (coe v20)))
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                v5
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                   v5
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8) (coe v16)
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))
                                                   v19)
                                                (d_'10214'_'10215'N_520
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v17)
                                                   (coe v20))))
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                v5
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                   v5
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))
                                                   v19)
                                                (d_'10214'_'10215'N_520
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                                   (coe v20)))
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                v5
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                   v5
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8) (coe v16)
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))
                                                   v19)
                                                (d_'10214'_'10215'N_520
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v17)
                                                   (coe v20))))
                                          (let v21
                                                 = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                     (coe
                                                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                        (let v21
                                                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                                   (coe v5) in
                                                         coe
                                                           (let v22
                                                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                                      (coe v21) in
                                                            coe
                                                              (let v23
                                                                     = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                                         (coe v22) in
                                                               coe
                                                                 (let v24
                                                                        = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                                            (coe v23) in
                                                                  coe
                                                                    (let v25
                                                                           = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                               (coe v24) in
                                                                     coe
                                                                       (let v26
                                                                              = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                                  (coe v25) in
                                                                        coe
                                                                          (let v27
                                                                                 = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                                     (coe v26) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                                (coe
                                                                                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                                   (coe
                                                                                      v27))))))))))) in
                                           coe
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                                   (coe v21))
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                      v5
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v13)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20))
                                                         v19)
                                                      (d_'10214'_'10215'N_520
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v14) (coe v20)))
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                      v5
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v16)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20))
                                                         v19)
                                                      (d_'10214'_'10215'N_520
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v17) (coe v20))))))
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.Lemmas.du_lemma'8324'_344
                                             (coe v5)
                                             (coe
                                                d_'10214'_'10215'H_518 (coe v0) (coe v1) (coe v2)
                                                (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                (coe v8) (coe v13)
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20))
                                             (coe
                                                d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2)
                                                (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                (coe v8) (coe v14) (coe v20))
                                             (coe
                                                d_'10214'_'10215'H_518 (coe v0) (coe v1) (coe v2)
                                                (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                (coe v8) (coe v16)
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20))
                                             (coe
                                                d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2)
                                                (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                (coe v8) (coe v17) (coe v20))
                                             (coe v19)))
                                       (coe
                                          MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                          (coe
                                             MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                             (coe
                                                MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                   (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                                     (coe
                                                                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                                        (coe
                                                                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                                           (coe
                                                                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                                              (coe v5))))))))))
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                      v5
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v13)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20))
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v16)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20)))
                                                      v19))
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                                   (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                                     (coe
                                                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                                        (coe
                                                                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                                           (coe v5)))))))))
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                      v5
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v13)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20))
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v16)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20)))
                                                      v19)
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                      v5
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v13)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20))
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v16)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20)))
                                                      v19)
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                      v5
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8)
                                                         (coe
                                                            d__'42'HN__750 (coe v0) (coe v1)
                                                            (coe v2) (coe v3) (coe v4) (coe v5)
                                                            (coe v6) (coe v7) (coe v8) (coe v13)
                                                            (coe v17))
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20))
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8)
                                                         (coe
                                                            d__'42'NH__748 (coe v0) (coe v1)
                                                            (coe v2) (coe v3) (coe v4) (coe v5)
                                                            (coe v6) (coe v7) (coe v8) (coe v14)
                                                            (coe v16))
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20)))
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                      v5
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v13)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20))
                                                         (d_'10214'_'10215'N_520
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v17) (coe v20)))
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'N_520
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v14) (coe v20))
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v16)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20)))))
                                                (coe
                                                   MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                                   (coe
                                                      d_'42'HN'45'homo_1094 (coe v0) (coe v1)
                                                      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                                      (coe v7) (coe v8) (coe v13) (coe v17)
                                                      (coe v19) (coe v20))
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                                      (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                                     (coe
                                                                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                                        (coe
                                                                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                                           (coe
                                                                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                                              (coe v5)))))))))
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8)
                                                         (coe
                                                            d__'42'HN__750 (coe v0) (coe v1)
                                                            (coe v2) (coe v3) (coe v4) (coe v5)
                                                            (coe v6) (coe v7) (coe v8) (coe v13)
                                                            (coe v17))
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20))
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v13)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20))
                                                         (d_'10214'_'10215'N_520
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v17) (coe v20)))
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8)
                                                         (coe
                                                            d__'42'NH__748 (coe v0) (coe v1)
                                                            (coe v2) (coe v3) (coe v4) (coe v5)
                                                            (coe v6) (coe v7) (coe v8) (coe v14)
                                                            (coe v16))
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20))
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'N_520
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v14) (coe v20))
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v16)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20))))
                                                   (coe
                                                      d_'42'NH'45'homo_1082 (coe v0) (coe v1)
                                                      (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                                      (coe v7) (coe v8) (coe v14) (coe v16)
                                                      (coe v19) (coe v20))))
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                                                (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                         (coe
                                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                            (coe v5)))))
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                      v5
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v13)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20))
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v16)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20)))
                                                      v19)
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                      v5
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8)
                                                         (coe
                                                            d__'42'HN__750 (coe v0) (coe v1)
                                                            (coe v2) (coe v3) (coe v4) (coe v5)
                                                            (coe v6) (coe v7) (coe v8) (coe v13)
                                                            (coe v17))
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20))
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8)
                                                         (coe
                                                            d__'42'NH__748 (coe v0) (coe v1)
                                                            (coe v2) (coe v3) (coe v4) (coe v5)
                                                            (coe v6) (coe v7) (coe v8) (coe v14)
                                                            (coe v16))
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20))))
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                      v5
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v13)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20))
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v16)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20)))
                                                      v19)
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                      v5
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v13)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20))
                                                         (d_'10214'_'10215'N_520
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v17) (coe v20)))
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'N_520
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v14) (coe v20))
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v16)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20)))))
                                                v19 v19)
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                                     (coe
                                                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                                        (coe
                                                                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                                           (coe v5))))))))))
                                                v19))
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                             (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                                     (coe v5)))))))))
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v5
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                      v5
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v13)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20))
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v16)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20)))
                                                      v19)
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                      v5
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8)
                                                         (coe
                                                            d__'42'HN__750 (coe v0) (coe v1)
                                                            (coe v2) (coe v3) (coe v4) (coe v5)
                                                            (coe v6) (coe v7) (coe v8) (coe v13)
                                                            (coe v17))
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20))
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8)
                                                         (coe
                                                            d__'42'NH__748 (coe v0) (coe v1)
                                                            (coe v2) (coe v3) (coe v4) (coe v5)
                                                            (coe v6) (coe v7) (coe v8) (coe v14)
                                                            (coe v16))
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20))))
                                                v19)
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v5
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                      v5
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v13)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20))
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v16)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20)))
                                                      v19)
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                      v5
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v13)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20))
                                                         (d_'10214'_'10215'N_520
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v17) (coe v20)))
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                         v5
                                                         (d_'10214'_'10215'N_520
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v14) (coe v20))
                                                         (d_'10214'_'10215'H_518
                                                            (coe v0) (coe v1) (coe v2) (coe v3)
                                                            (coe v4) (coe v5) (coe v6) (coe v7)
                                                            (coe v8) (coe v16)
                                                            (coe
                                                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                               v19 v20)))))
                                                v19)
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v5
                                                (d_'10214'_'10215'N_520
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                                   (coe v20))
                                                (d_'10214'_'10215'N_520
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v17)
                                                   (coe v20)))
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v5
                                                (d_'10214'_'10215'N_520
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                                   (coe v20))
                                                (d_'10214'_'10215'N_520
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v17)
                                                   (coe v20))))
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                             (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                                     (coe
                                                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                                        (coe v5))))))))))
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v5
                                                (d_'10214'_'10215'N_520
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                                   (coe v20))
                                                (d_'10214'_'10215'N_520
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8) (coe v17)
                                                   (coe v20))))))
                                    (coe
                                       MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                       (coe
                                          MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                          (coe
                                             MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                             (coe
                                                MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                                (coe
                                                   d_'42'H'45'homo_1104 (coe v0) (coe v1) (coe v2)
                                                   (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                   (coe v8) (coe v13) (coe v16)
                                                   (coe
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                      v20))
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                                                   (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                         (coe
                                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                            (coe
                                                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                               (coe v5)))))
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8)
                                                      (coe
                                                         d__'42'H__752 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v13) (coe v16))
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                      v5
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v13)
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20))
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v16)
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20)))
                                                   v19 v19)
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                   (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                                     (coe
                                                                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                                        (coe
                                                                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                                           (coe
                                                                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                                              (coe v5))))))))))
                                                   v19))
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                                (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                                     (coe
                                                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                                        (coe v5)))))))))
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                   v5
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8)
                                                      (coe
                                                         d__'42'H__752 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v13) (coe v16))
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))
                                                   v19)
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                      v5
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v13)
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20))
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v16)
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20)))
                                                   v19)
                                                (d_'10214'_'10215'H_518
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8)
                                                   (coe
                                                      d__'43'H__712 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8)
                                                      (coe
                                                         d__'42'HN__750 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v13) (coe v17))
                                                      (coe
                                                         d__'42'NH__748 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v14) (coe v16)))
                                                   (coe
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                      v20))
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                   v5
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8)
                                                      (coe
                                                         d__'42'HN__750 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v13) (coe v17))
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8)
                                                      (coe
                                                         d__'42'NH__748 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v14) (coe v16))
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))))
                                             (coe
                                                d_'43'H'45'homo_998 (coe v0) (coe v1) (coe v2)
                                                (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                (coe v8)
                                                (coe
                                                   d__'42'HN__750 (coe v0) (coe v1) (coe v2)
                                                   (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                   (coe v8) (coe v13) (coe v17))
                                                (coe
                                                   d__'42'NH__748 (coe v0) (coe v1) (coe v2)
                                                   (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                   (coe v8) (coe v14) (coe v16))
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20)))
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                                             (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                      (coe
                                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                         (coe v5)))))
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                v5
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                   v5
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8)
                                                      (coe
                                                         d__'42'H__752 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v13) (coe v16))
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))
                                                   v19)
                                                (d_'10214'_'10215'H_518
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8)
                                                   (coe
                                                      d__'43'H__712 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8)
                                                      (coe
                                                         d__'42'HN__750 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v13) (coe v17))
                                                      (coe
                                                         d__'42'NH__748 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v14) (coe v16)))
                                                   (coe
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                      v20)))
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                v5
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                      v5
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v13)
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20))
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v16)
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20)))
                                                   v19)
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                   v5
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8)
                                                      (coe
                                                         d__'42'HN__750 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v13) (coe v17))
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8)
                                                      (coe
                                                         d__'42'NH__748 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v14) (coe v16))
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))))
                                             v19 v19)
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                             (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                                     (coe
                                                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                                        (coe v5))))))))))
                                             v19))
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                          (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                            (coe
                                                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                                  (coe v5)))))))))
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                v5
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                   v5
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8)
                                                      (coe
                                                         d__'42'H__752 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v13) (coe v16))
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))
                                                   v19)
                                                (d_'10214'_'10215'H_518
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8)
                                                   (coe
                                                      d__'43'H__712 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8)
                                                      (coe
                                                         d__'42'HN__750 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v13) (coe v17))
                                                      (coe
                                                         d__'42'NH__748 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v14) (coe v16)))
                                                   (coe
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                      v20)))
                                             v19)
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                v5
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                      v5
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v13)
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20))
                                                      (d_'10214'_'10215'H_518
                                                         (coe v0) (coe v1) (coe v2) (coe v3)
                                                         (coe v4) (coe v5) (coe v6) (coe v7)
                                                         (coe v8) (coe v16)
                                                         (coe
                                                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                            v19 v20)))
                                                   v19)
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                                   v5
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8)
                                                      (coe
                                                         d__'42'HN__750 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v13) (coe v17))
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))
                                                   (d_'10214'_'10215'H_518
                                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                      (coe v5) (coe v6) (coe v7) (coe v8)
                                                      (coe
                                                         d__'42'NH__748 (coe v0) (coe v1) (coe v2)
                                                         (coe v3) (coe v4) (coe v5) (coe v6)
                                                         (coe v7) (coe v8) (coe v14) (coe v16))
                                                      (coe
                                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                                         v19 v20))))
                                             v19)
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (d_'10214'_'10215'N_520
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                                (coe v20))
                                             (d_'10214'_'10215'N_520
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v17)
                                                (coe v20)))
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (d_'10214'_'10215'N_520
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                                (coe v20))
                                             (d_'10214'_'10215'N_520
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v17)
                                                (coe v20))))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                          (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                                     (coe v5))))))))))
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                             v5
                                             (d_'10214'_'10215'N_520
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                                (coe v20))
                                             (d_'10214'_'10215'N_520
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v17)
                                                (coe v20))))))
                                 (coe
                                    MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                    (coe
                                       MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                       (coe
                                          d_'42'x'43'H'45'homo_1052 (coe v0) (coe v1) (coe v2)
                                          (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                          (coe
                                             d__'42'H__752 (coe v0) (coe v1) (coe v2) (coe v3)
                                             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                             (coe v16))
                                          (coe
                                             d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3)
                                             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                             (coe
                                                d__'42'HN__750 (coe v0) (coe v1) (coe v2) (coe v3)
                                                (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                (coe v13) (coe v17))
                                             (coe
                                                d__'42'NH__748 (coe v0) (coe v1) (coe v2) (coe v3)
                                                (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                (coe v14) (coe v16)))
                                          (coe v19) (coe v20))
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                                          (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                (coe
                                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                   (coe
                                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                      (coe v5)))))
                                          (d_'10214'_'10215'H_518
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8)
                                             (coe
                                                d__'42'x'43'H__736 (coe v0) (coe v1) (coe v2)
                                                (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                (coe v8)
                                                (coe
                                                   d__'42'H__752 (coe v0) (coe v1) (coe v2) (coe v3)
                                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                   (coe v13) (coe v16))
                                                (coe
                                                   d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3)
                                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                   (coe
                                                      d__'42'HN__750 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8) (coe v13) (coe v17))
                                                   (coe
                                                      d__'42'NH__748 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8) (coe v14) (coe v16))))
                                             (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                             v5
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v5
                                                (d_'10214'_'10215'H_518
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8)
                                                   (coe
                                                      d__'42'H__752 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8) (coe v13) (coe v16))
                                                   (coe
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                      v20))
                                                v19)
                                             (d_'10214'_'10215'H_518
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8)
                                                (coe
                                                   d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3)
                                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                   (coe
                                                      d__'42'HN__750 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8) (coe v13) (coe v17))
                                                   (coe
                                                      d__'42'NH__748 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8) (coe v14) (coe v16)))
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20)))
                                          v19 v19)
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                          (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                               (coe
                                                                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                                  (coe
                                                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                                     (coe v5))))))))))
                                          v19))
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                       (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                             (coe
                                                MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                (coe
                                                   MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                   (coe
                                                      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                         (coe
                                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                            (coe
                                                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                               (coe v5)))))))))
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v5
                                          (d_'10214'_'10215'H_518
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8)
                                             (coe
                                                d__'42'x'43'H__736 (coe v0) (coe v1) (coe v2)
                                                (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                (coe v8)
                                                (coe
                                                   d__'42'H__752 (coe v0) (coe v1) (coe v2) (coe v3)
                                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                   (coe v13) (coe v16))
                                                (coe
                                                   d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3)
                                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                   (coe
                                                      d__'42'HN__750 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8) (coe v13) (coe v17))
                                                   (coe
                                                      d__'42'NH__748 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8) (coe v14) (coe v16))))
                                             (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20))
                                          v19)
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v5
                                          (coe
                                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                             v5
                                             (coe
                                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                                v5
                                                (d_'10214'_'10215'H_518
                                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                   (coe v5) (coe v6) (coe v7) (coe v8)
                                                   (coe
                                                      d__'42'H__752 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8) (coe v13) (coe v16))
                                                   (coe
                                                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                      v20))
                                                v19)
                                             (d_'10214'_'10215'H_518
                                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                                (coe v5) (coe v6) (coe v7) (coe v8)
                                                (coe
                                                   d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3)
                                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                   (coe
                                                      d__'42'HN__750 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8) (coe v13) (coe v17))
                                                   (coe
                                                      d__'42'NH__748 (coe v0) (coe v1) (coe v2)
                                                      (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                                      (coe v8) (coe v14) (coe v16)))
                                                (coe
                                                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19
                                                   v20)))
                                          v19)
                                       (d_'10214'_'10215'N_520
                                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                          (coe v6) (coe v7) (coe v8)
                                          (coe
                                             d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3)
                                             (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                             (coe v17))
                                          (coe v20))
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                          v5
                                          (d_'10214'_'10215'N_520
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v14) (coe v20))
                                          (d_'10214'_'10215'N_520
                                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                             (coe v6) (coe v7) (coe v8) (coe v17) (coe v20))))
                                    (coe
                                       d_'42'N'45'homo_1114 (coe v0) (coe v1) (coe v2) (coe v3)
                                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                       (coe v17) (coe v20))))
                              (d_'42'x'43'HN'8776''42'x'43'_922
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                 (coe v7) (coe v8)
                                 (coe
                                    d__'42'x'43'H__736 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                    (coe v5) (coe v6) (coe v7) (coe v8)
                                    (coe
                                       d__'42'H__752 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                       (coe v5) (coe v6) (coe v7) (coe v8) (coe v13) (coe v16))
                                    (coe
                                       d__'43'H__712 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                       (coe v5) (coe v6) (coe v7) (coe v8)
                                       (coe
                                          d__'42'HN__750 (coe v0) (coe v1) (coe v2) (coe v3)
                                          (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)
                                          (coe v17))
                                       (coe
                                          d__'42'NH__748 (coe v0) (coe v1) (coe v2) (coe v3)
                                          (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v14)
                                          (coe v16))))
                                 (coe
                                    d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                    (coe v5) (coe v6) (coe v7) (coe v8) (coe v14) (coe v17))
                                 (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v19 v20)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.*N-homo
d_'42'N'45'homo_1114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_Normal_508 ->
  T_Normal_508 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'42'N'45'homo_1114 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v9 of
      C_con_514 v12
        -> case coe v10 of
             C_con_514 v13
               -> coe
                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'42''45'homo_760
                    v6 v12 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      C_poly_516 v13
        -> let v14 = subInt (coe v8) (coe (1 :: Integer)) in
           coe
             (case coe v10 of
                C_poly_516 v16
                  -> coe
                       d_'42'H'45'homo_1104 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v7) (coe v14) (coe v13) (coe v16) (coe v11)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.^N-homo
d_'94'N'45'homo_1240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_Normal_508 ->
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'94'N'45'homo_1240 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v10 of
      0 -> coe
             d_1N'45'homo_908 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v11)
      _ -> let v12 = subInt (coe v10) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                (\ v13 v14 v15 ->
                   coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v15)
                (d_'10214'_'10215'N_520
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                   (coe v7) (coe v8)
                   (coe
                      d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                      (coe v6) (coe v7) (coe v8) (coe v9)
                      (coe
                         d__'94'N__824 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                         (coe v6) (coe v7) (coe v8) (coe v9) (coe v12)))
                   (coe v11))
                (coe
                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                   v5
                   (d_'10214'_'10215'N_520
                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                      (coe v7) (coe v8) (coe v9) (coe v11))
                   (coe
                      MAlonzo.Code.Algebra.Definitions.RawSemiring.du__'94'__90
                      (coe
                         MAlonzo.Code.Algebra.Bundles.du_rawSemiring_2260
                         (coe
                            MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                            (coe
                               MAlonzo.Code.Algebra.Bundles.du_semiring_2600
                               (coe
                                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.du_commutativeSemiring_320
                                  (coe v5)))))
                      (coe
                         d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                         (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v11))
                      (coe v12)))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                            (let v13
                                   = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                       (coe v5) in
                             coe
                               (let v14
                                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe v13) in
                                coe
                                  (let v15
                                         = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                             (coe v14) in
                                   coe
                                     (let v16
                                            = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                (coe v15) in
                                      coe
                                        (let v17
                                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                   (coe v16) in
                                         coe
                                           (let v18
                                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                      (coe v17) in
                                            coe
                                              (let v19
                                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                         (coe v18) in
                                               coe
                                                 (coe
                                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                    (coe
                                                       MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                       (coe v19)))))))))))))
                   (d_'10214'_'10215'N_520
                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                      (coe v7) (coe v8)
                      (coe
                         d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                         (coe v6) (coe v7) (coe v8) (coe v9)
                         (coe
                            d__'94'N__824 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                            (coe v6) (coe v7) (coe v8) (coe v9) (coe v12)))
                      (coe v11))
                   (coe
                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                      v5
                      (d_'10214'_'10215'N_520
                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                         (coe v7) (coe v8) (coe v9) (coe v11))
                      (d_'10214'_'10215'N_520
                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                         (coe v7) (coe v8)
                         (coe
                            d__'94'N__824 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                            (coe v6) (coe v7) (coe v8) (coe v9) (coe v12))
                         (coe v11)))
                   (coe
                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                      v5
                      (d_'10214'_'10215'N_520
                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                         (coe v7) (coe v8) (coe v9) (coe v11))
                      (coe
                         MAlonzo.Code.Algebra.Definitions.RawSemiring.du__'94'__90
                         (coe
                            MAlonzo.Code.Algebra.Bundles.du_rawSemiring_2260
                            (coe
                               MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                               (coe
                                  MAlonzo.Code.Algebra.Bundles.du_semiring_2600
                                  (coe
                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.du_commutativeSemiring_320
                                     (coe v5)))))
                         (coe
                            d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                            (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v11))
                         (coe v12)))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                               (let v13
                                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v5) in
                                coe
                                  (let v14
                                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                             (coe v13) in
                                   coe
                                     (let v15
                                            = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                (coe v14) in
                                      coe
                                        (let v16
                                               = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                   (coe v15) in
                                         coe
                                           (let v17
                                                  = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                      (coe v16) in
                                            coe
                                              (let v18
                                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                         (coe v17) in
                                               coe
                                                 (let v19
                                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                            (coe v18) in
                                                  coe
                                                    (coe
                                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                       (coe
                                                          MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                          (coe v19)))))))))))))
                      (coe
                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                         v5
                         (d_'10214'_'10215'N_520
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8) (coe v9) (coe v11))
                         (d_'10214'_'10215'N_520
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8)
                            (coe
                               d__'94'N__824 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                               (coe v6) (coe v7) (coe v8) (coe v9) (coe v12))
                            (coe v11)))
                      (coe
                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                         v5
                         (d_'10214'_'10215'N_520
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8) (coe v9) (coe v11))
                         (coe
                            MAlonzo.Code.Algebra.Definitions.RawSemiring.du__'94'__90
                            (coe
                               MAlonzo.Code.Algebra.Bundles.du_rawSemiring_2260
                               (coe
                                  MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                                  (coe
                                     MAlonzo.Code.Algebra.Bundles.du_semiring_2600
                                     (coe
                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.du_commutativeSemiring_320
                                        (coe v5)))))
                            (coe
                               d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                               (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v11))
                            (coe v12)))
                      (coe
                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                         v5
                         (d_'10214'_'10215'N_520
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8) (coe v9) (coe v11))
                         (coe
                            MAlonzo.Code.Algebra.Definitions.RawSemiring.du__'94'__90
                            (coe
                               MAlonzo.Code.Algebra.Bundles.du_rawSemiring_2260
                               (coe
                                  MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                                  (coe
                                     MAlonzo.Code.Algebra.Bundles.du_semiring_2600
                                     (coe
                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.du_commutativeSemiring_320
                                        (coe v5)))))
                            (coe
                               d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                               (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v11))
                            (coe v12)))
                      (let v13
                             = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (let v13
                                           = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                               (coe v5) in
                                     coe
                                       (let v14
                                              = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                  (coe v13) in
                                        coe
                                          (let v15
                                                 = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                     (coe v14) in
                                           coe
                                             (let v16
                                                    = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                        (coe v15) in
                                              coe
                                                (let v17
                                                       = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                           (coe v16) in
                                                 coe
                                                   (let v18
                                                          = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                              (coe v17) in
                                                    coe
                                                      (let v19
                                                             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                 (coe v18) in
                                                       coe
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                               (coe v19))))))))))) in
                       coe
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                               (coe v13))
                            (coe
                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                               v5
                               (d_'10214'_'10215'N_520
                                  (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                  (coe v7) (coe v8) (coe v9) (coe v11))
                               (coe
                                  MAlonzo.Code.Algebra.Definitions.RawSemiring.du__'94'__90
                                  (coe
                                     MAlonzo.Code.Algebra.Bundles.du_rawSemiring_2260
                                     (coe
                                        MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                                        (coe
                                           MAlonzo.Code.Algebra.Bundles.du_semiring_2600
                                           (coe
                                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.du_commutativeSemiring_320
                                              (coe v5)))))
                                  (coe
                                     d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                                     (coe v11))
                                  (coe v12)))))
                      (coe
                         MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                            (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                  (coe
                                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                     (coe
                                        MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                        (coe
                                           MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                           (coe
                                              MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                              (coe
                                                 MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                 (coe
                                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                    (coe
                                                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                       (coe v5))))))))))
                            (d_'10214'_'10215'N_520
                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                               (coe v7) (coe v8) (coe v9) (coe v11)))
                         (coe
                            MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                            (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                  (coe
                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                     (coe
                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                        (coe v5)))))
                            (d_'10214'_'10215'N_520
                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                               (coe v7) (coe v8) (coe v9) (coe v11))
                            (d_'10214'_'10215'N_520
                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                               (coe v7) (coe v8) (coe v9) (coe v11))
                            (d_'10214'_'10215'N_520
                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                               (coe v7) (coe v8)
                               (coe
                                  d__'94'N__824 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                  (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v12))
                               (coe v11))
                            (let v13
                                   = coe
                                       MAlonzo.Code.Algebra.Bundles.du_semiring_2600
                                       (coe
                                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.du_commutativeSemiring_320
                                          (coe v5)) in
                             coe
                               (coe
                                  MAlonzo.Code.Algebra.Definitions.RawSemiring.du__'94'__90
                                  (coe
                                     MAlonzo.Code.Algebra.Bundles.du_rawSemiring_2260
                                     (coe
                                        MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                                        (coe v13)))
                                  (coe
                                     d_'10214'_'10215'N_520 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                                     (coe v11))
                                  (coe v12))))
                         (coe
                            d_'94'N'45'homo_1240 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                            (coe v5) (coe v6) (coe v7) (coe v8) (coe v9) (coe v12) (coe v11))))
                   (d_'42'N'45'homo_1114
                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                      (coe v7) (coe v8) (coe v9)
                      (coe
                         d__'94'N__824 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                         (coe v6) (coe v7) (coe v8) (coe v9) (coe v12))
                      (coe v11))))
-- Algebra.Solver.Ring.-H‿-homo
d_'45'H'8255''45'homo_1258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_HNF_506 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'45'H'8255''45'homo_1258 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13
        -> coe
             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
             (\ v14 v15 v16 ->
                coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v16)
             (d_'10214'_'10215'H_518
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8)
                (coe
                   d__'42'NH__748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                   (coe v5) (coe v6) (coe v7) (coe v8)
                   (coe
                      d_'45'N__834 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                      (coe v6) (coe v7) (coe v8)
                      (coe
                         d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                         (coe v6) (coe v7) (coe v8)))
                   (coe v9))
                (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13))
             (coe
                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                v5
                (d_'10214'_'10215'H_518
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                   (coe v7) (coe v8) (coe v9)
                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13)))
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                   (coe
                      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                      (coe
                         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                         (let v14
                                = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                    (coe v5) in
                          coe
                            (let v15
                                   = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                       (coe v14) in
                             coe
                               (let v16
                                      = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                          (coe v15) in
                                coe
                                  (let v17
                                         = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                             (coe v16) in
                                   coe
                                     (let v18
                                            = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                (coe v17) in
                                      coe
                                        (let v19
                                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                   (coe v18) in
                                         coe
                                           (let v20
                                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                      (coe v19) in
                                            coe
                                              (coe
                                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                 (coe
                                                    MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                    (coe v20)))))))))))))
                (d_'10214'_'10215'H_518
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                   (coe v7) (coe v8)
                   (coe
                      d__'42'NH__748 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                      (coe v5) (coe v6) (coe v7) (coe v8)
                      (coe
                         d_'45'N__834 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                         (coe v6) (coe v7) (coe v8)
                         (coe
                            d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                            (coe v6) (coe v7) (coe v8)))
                      (coe v9))
                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13))
                (coe
                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                   v5
                   (d_'10214'_'10215'N_520
                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                      (coe v7) (coe v8)
                      (coe
                         d_'45'N__834 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                         (coe v6) (coe v7) (coe v8)
                         (coe
                            d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                            (coe v6) (coe v7) (coe v8)))
                      (coe v13))
                   (d_'10214'_'10215'H_518
                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                      (coe v7) (coe v8) (coe v9)
                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13)))
                (coe
                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                   v5
                   (d_'10214'_'10215'H_518
                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                      (coe v7) (coe v8) (coe v9)
                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13)))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                            (let v14
                                   = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                       (coe v5) in
                             coe
                               (let v15
                                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe v14) in
                                coe
                                  (let v16
                                         = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                             (coe v15) in
                                   coe
                                     (let v17
                                            = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                (coe v16) in
                                      coe
                                        (let v18
                                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                   (coe v17) in
                                         coe
                                           (let v19
                                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                      (coe v18) in
                                            coe
                                              (let v20
                                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                         (coe v19) in
                                               coe
                                                 (coe
                                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                    (coe
                                                       MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                       (coe v20)))))))))))))
                   (coe
                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                      v5
                      (d_'10214'_'10215'N_520
                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                         (coe v7) (coe v8)
                         (coe
                            d_'45'N__834 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                            (coe v6) (coe v7) (coe v8)
                            (coe
                               d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                               (coe v6) (coe v7) (coe v8)))
                         (coe v13))
                      (d_'10214'_'10215'H_518
                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                         (coe v7) (coe v8) (coe v9)
                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13)))
                   (coe
                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                      v5
                      (coe
                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                         v5
                         (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                            (coe v5)))
                      (d_'10214'_'10215'H_518
                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                         (coe v7) (coe v8) (coe v9)
                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13)))
                   (coe
                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                      v5
                      (d_'10214'_'10215'H_518
                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                         (coe v7) (coe v8) (coe v9)
                         (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13)))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                               (let v14
                                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v5) in
                                coe
                                  (let v15
                                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                             (coe v14) in
                                   coe
                                     (let v16
                                            = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                (coe v15) in
                                      coe
                                        (let v17
                                               = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                   (coe v16) in
                                         coe
                                           (let v18
                                                  = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                      (coe v17) in
                                            coe
                                              (let v19
                                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                         (coe v18) in
                                               coe
                                                 (let v20
                                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                            (coe v19) in
                                                  coe
                                                    (coe
                                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                       (coe
                                                          MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                          (coe v20)))))))))))))
                      (coe
                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                         v5
                         (coe
                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                            v5
                            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                               (coe v5)))
                         (d_'10214'_'10215'H_518
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8) (coe v9)
                            (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13)))
                      (coe
                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                         v5
                         (d_'10214'_'10215'H_518
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8) (coe v9)
                            (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13)))
                      (coe
                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                         v5
                         (d_'10214'_'10215'H_518
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8) (coe v9)
                            (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13)))
                      (let v14
                             = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (let v14
                                           = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                               (coe v5) in
                                     coe
                                       (let v15
                                              = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                  (coe v14) in
                                        coe
                                          (let v16
                                                 = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                     (coe v15) in
                                           coe
                                             (let v17
                                                    = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                        (coe v16) in
                                              coe
                                                (let v18
                                                       = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                           (coe v17) in
                                                 coe
                                                   (let v19
                                                          = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                              (coe v18) in
                                                    coe
                                                      (let v20
                                                             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                 (coe v19) in
                                                       coe
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                               (coe v20))))))))))) in
                       coe
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                               (coe v14))
                            (coe
                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                               v5
                               (d_'10214'_'10215'H_518
                                  (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                  (coe v7) (coe v8) (coe v9)
                                  (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13)))))
                      (coe
                         MAlonzo.Code.Algebra.Solver.Ring.Lemmas.du_lemma'8327'_384 (coe v5)
                         (coe
                            d_'10214'_'10215'H_518 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                            (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                            (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13))))
                   (coe
                      MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                            (coe
                               MAlonzo.Code.Algebra.Structures.d_isMagma_478
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                  (coe
                                     MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                     (coe
                                        MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                        (coe
                                           MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                           (coe
                                              MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                              (coe
                                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                 (coe
                                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                    (coe v5))))))))))
                         (d_'10214'_'10215'N_520
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8)
                            (coe
                               d_'45'N__834 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                               (coe v6) (coe v7) (coe v8)
                               (coe
                                  d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                  (coe v6) (coe v7) (coe v8)))
                            (coe v13))
                         (coe
                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                            v5
                            (d_'10214'_'10215'N_520
                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                               (coe v7) (coe v8)
                               (coe
                                  d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                  (coe v6) (coe v7) (coe v8))
                               (coe v13)))
                         (coe
                            MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                            (\ v14 v15 -> v15)
                            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                               (coe v5))
                            (d_'10214'_'10215'N_520
                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                               (coe v7) (coe v8)
                               (coe
                                  d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                  (coe v6) (coe v7) (coe v8))
                               (coe v13))
                            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                               (coe v5)))
                         (d_'45'N'8255''45'homo_1266
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8)
                            (coe
                               d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                               (coe v6) (coe v7) (coe v8))
                            (coe v13))
                         (coe
                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45''8255'cong_64
                            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                               (coe v5))
                            (d_'10214'_'10215'N_520
                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                               (coe v7) (coe v8)
                               (coe
                                  d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                  (coe v6) (coe v7) (coe v8))
                               (coe v13))
                            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                               (coe v5))
                            (d_1N'45'homo_908
                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                               (coe v7) (coe v8) (coe v13))))
                      (coe
                         MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                         (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                            (coe
                               MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                               (coe
                                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                  (coe
                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                     (coe v5)))))
                         (d_'10214'_'10215'N_520
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8)
                            (coe
                               d_'45'N__834 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                               (coe v6) (coe v7) (coe v8)
                               (coe
                                  d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                  (coe v6) (coe v7) (coe v8)))
                            (coe v13))
                         (coe
                            MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                            (\ v14 v15 -> v15)
                            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                               (coe v5))
                            (d_'10214'_'10215'N_520
                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                               (coe v7) (coe v8)
                               (coe
                                  d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                  (coe v6) (coe v7) (coe v8))
                               (coe v13))
                            (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                               (coe v5)))
                         (d_'10214'_'10215'H_518
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8) (coe v9)
                            (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13))
                         (d_'10214'_'10215'H_518
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8) (coe v9)
                            (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13)))
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                            (coe
                               MAlonzo.Code.Algebra.Structures.d_isMagma_478
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                  (coe
                                     MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                     (coe
                                        MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                        (coe
                                           MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                           (coe
                                              MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                              (coe
                                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                 (coe
                                                    MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                    (coe v5))))))))))
                         (d_'10214'_'10215'H_518
                            (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                            (coe v7) (coe v8) (coe v9)
                            (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13)))))
                (d_'42'NH'45'homo_1082
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                   (coe v7) (coe v8)
                   (coe
                      d_'45'N__834 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                      (coe v6) (coe v7) (coe v8)
                      (coe
                         d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                         (coe v6) (coe v7) (coe v8)))
                   (coe v9) (coe v12) (coe v13)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.-N‿-homo
d_'45'N'8255''45'homo_1266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_Normal_508 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_'45'N'8255''45'homo_1266 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      C_con_514 v11
        -> coe
             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45''8255'homo_762
             v6 v11
      C_poly_516 v12
        -> let v13 = subInt (coe v8) (coe (1 :: Integer)) in
           coe
             (coe
                d_'45'H'8255''45'homo_1258 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v5) (coe v6) (coe v7) (coe v13) (coe v12) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.correct-con
d_correct'45'con_1286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_correct'45'con_1286 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
        -> coe
             MAlonzo.Code.Relation.Binary.Structures.d_refl_34
             (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                (coe
                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                   (coe
                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                      (coe
                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                         (coe
                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                            (coe
                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                  (coe
                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                     (coe
                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                        (coe v5))))))))))
             (d_'10214'_'10215'N_520
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe (0 :: Integer))
                (coe
                   d_normalise'45'con_842 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                   (coe v5) (coe v6) (coe v7) (coe (0 :: Integer)) (coe v9))
                (coe v10))
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13
        -> let v14 = subInt (coe v8) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                (\ v15 v16 v17 ->
                   coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v17)
                (d_'10214'_'10215'H_518
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                   (coe v7) (coe v14)
                   (coe
                      d__'42'x'43'HN__692 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                      (coe v5) (coe v6) (coe v7) (coe v14) (coe C_'8709'_510)
                      (coe
                         d_normalise'45'con_842 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                         (coe v5) (coe v6) (coe v7) (coe v14) (coe v9)))
                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13))
                (coe
                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'10214'_'10215'_756
                   v6 v9)
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                            (let v15
                                   = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                       (coe v5) in
                             coe
                               (let v16
                                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe v15) in
                                coe
                                  (let v17
                                         = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                             (coe v16) in
                                   coe
                                     (let v18
                                            = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                (coe v17) in
                                      coe
                                        (let v19
                                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                   (coe v18) in
                                         coe
                                           (let v20
                                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                      (coe v19) in
                                            coe
                                              (let v21
                                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                         (coe v20) in
                                               coe
                                                 (coe
                                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                    (coe
                                                       MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                       (coe v21)))))))))))))
                   (d_'10214'_'10215'H_518
                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                      (coe v7) (coe v14)
                      (coe
                         d__'42'x'43'HN__692 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                         (coe v5) (coe v6) (coe v7) (coe v14) (coe C_'8709'_510)
                         (coe
                            d_normalise'45'con_842 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                            (coe v5) (coe v6) (coe v7) (coe v14) (coe v9)))
                      (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13))
                   (d_'10214'_'10215'N_520
                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                      (coe v7) (coe v14)
                      (coe
                         d_normalise'45'con_842 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                         (coe v5) (coe v6) (coe v7) (coe v14) (coe v9))
                      (coe v13))
                   (coe
                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'10214'_'10215'_756
                      v6 v9)
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                               (let v15
                                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                          (coe v5) in
                                coe
                                  (let v16
                                         = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                             (coe v15) in
                                   coe
                                     (let v17
                                            = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                (coe v16) in
                                      coe
                                        (let v18
                                               = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                   (coe v17) in
                                         coe
                                           (let v19
                                                  = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                      (coe v18) in
                                            coe
                                              (let v20
                                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                         (coe v19) in
                                               coe
                                                 (let v21
                                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                            (coe v20) in
                                                  coe
                                                    (coe
                                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                       (coe
                                                          MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                          (coe v21)))))))))))))
                      (d_'10214'_'10215'N_520
                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                         (coe v7) (coe v14)
                         (coe
                            d_normalise'45'con_842 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                            (coe v5) (coe v6) (coe v7) (coe v14) (coe v9))
                         (coe v13))
                      (coe
                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'10214'_'10215'_756
                         v6 v9)
                      (coe
                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'10214'_'10215'_756
                         v6 v9)
                      (let v15
                             = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (let v15
                                           = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                               (coe v5) in
                                     coe
                                       (let v16
                                              = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                  (coe v15) in
                                        coe
                                          (let v17
                                                 = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                     (coe v16) in
                                           coe
                                             (let v18
                                                    = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                        (coe v17) in
                                              coe
                                                (let v19
                                                       = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                           (coe v18) in
                                                 coe
                                                   (let v20
                                                          = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                              (coe v19) in
                                                    coe
                                                      (let v21
                                                             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                 (coe v20) in
                                                       coe
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                            (coe
                                                               MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                               (coe v21))))))))))) in
                       coe
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                               (coe v15))
                            (coe
                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'10214'_'10215'_756
                               v6 v9)))
                      (d_correct'45'con_1286
                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                         (coe v7) (coe v14) (coe v9) (coe v13)))
                   (d_'8709''42'x'43'HN'45'homo_964
                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                      (coe v7) (coe v14)
                      (coe
                         d_normalise'45'con_842 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                         (coe v5) (coe v6) (coe v7) (coe v14) (coe v9))
                      (coe v12) (coe v13))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.correct-var
d_correct'45'var_1302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_correct'45'var_1302 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> let v12 = subInt (coe v8) (coe (1 :: Integer)) in
           coe
             (case coe v10 of
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v14 v15
                  -> coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                       (\ v16 v17 v18 ->
                          coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v18)
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                          v5
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                      (coe v5))
                                   v14)
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v12)
                                   (coe
                                      d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                      (coe v6) (coe v7) (coe v12))
                                   (coe v15)))
                             v14)
                          (d_'10214'_'10215'N_520
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v12) (coe du_0N_680 (coe v4) (coe v12)) (coe v15)))
                       v14
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v16
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                              (coe v5) in
                                    coe
                                      (let v17
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                 (coe v16) in
                                       coe
                                         (let v18
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                    (coe v17) in
                                          coe
                                            (let v19
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                       (coe v18) in
                                             coe
                                               (let v20
                                                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                          (coe v19) in
                                                coe
                                                  (let v21
                                                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                             (coe v20) in
                                                   coe
                                                     (let v22
                                                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                (coe v21) in
                                                      coe
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                              (coe v22)))))))))))))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                         (coe v5))
                                      v14)
                                   (d_'10214'_'10215'N_520
                                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                      (coe v7) (coe v12)
                                      (coe
                                         d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                         (coe v5) (coe v6) (coe v7) (coe v12))
                                      (coe v15)))
                                v14)
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v12) (coe du_0N_680 (coe v4) (coe v12)) (coe v15)))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                      v5
                                      (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                         (coe v5))
                                      v14)
                                   (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                                      (coe v5)))
                                v14)
                             (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                (coe v5)))
                          v14
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                      (let v16
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                 (coe v5) in
                                       coe
                                         (let v17
                                                = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                    (coe v16) in
                                          coe
                                            (let v18
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                       (coe v17) in
                                             coe
                                               (let v19
                                                      = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                          (coe v18) in
                                                coe
                                                  (let v20
                                                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                             (coe v19) in
                                                   coe
                                                     (let v21
                                                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                (coe v20) in
                                                      coe
                                                        (let v22
                                                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                   (coe v21) in
                                                         coe
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                              (coe
                                                                 MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                 (coe v22)))))))))))))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                v5
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                         v5
                                         (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                            (coe v5))
                                         v14)
                                      (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                                         (coe v5)))
                                   v14)
                                (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                   (coe v5)))
                             v14 v14
                             (let v16
                                    = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                           (let v16
                                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                      (coe v5) in
                                            coe
                                              (let v17
                                                     = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                         (coe v16) in
                                               coe
                                                 (let v18
                                                        = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                            (coe v17) in
                                                  coe
                                                    (let v19
                                                           = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                               (coe v18) in
                                                     coe
                                                       (let v20
                                                              = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                  (coe v19) in
                                                        coe
                                                          (let v21
                                                                 = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                     (coe v20) in
                                                           coe
                                                             (let v22
                                                                    = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                        (coe v21) in
                                                              coe
                                                                (coe
                                                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                   (coe
                                                                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                      (coe v22))))))))))) in
                              coe
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                      (coe v16))
                                   (coe v14)))
                             (coe
                                MAlonzo.Code.Algebra.Solver.Ring.Lemmas.du_lemma'8325'_368 (coe v5)
                                (coe v14)))
                          (coe
                             MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                             (coe
                                MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                (coe
                                   MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                           (coe
                                                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                              (coe
                                                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                                 (coe v5))))))))))
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                         v5
                                         (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                            (coe v5))
                                         v14))
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                      (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                        (coe
                                                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                           (coe
                                                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                              (coe v5)))))))))
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                         v5
                                         (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                            (coe v5))
                                         v14)
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                         v5
                                         (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                            (coe v5))
                                         v14)
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v12)
                                         (coe
                                            d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                            (coe v5) (coe v6) (coe v7) (coe v12))
                                         (coe v15))
                                      (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                                         (coe v5)))
                                   (coe
                                      d_1N'45'homo_908 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                      (coe v5) (coe v6) (coe v7) (coe v12) (coe v15)))
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                                   (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                            (coe
                                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                               (coe v5)))))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                         v5
                                         (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                            (coe v5))
                                         v14)
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v12)
                                         (coe
                                            d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                            (coe v5) (coe v6) (coe v7) (coe v12))
                                         (coe v15)))
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                         v5
                                         (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                            (coe v5))
                                         v14)
                                      (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                                         (coe v5)))
                                   v14 v14)
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                        (coe
                                                           MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                           (coe
                                                              MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                              (coe v5))))))))))
                                   v14))
                             (coe
                                MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                  (coe
                                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                     (coe
                                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                        (coe v5)))))))))
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                         v5
                                         (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                            (coe v5))
                                         v14)
                                      (d_'10214'_'10215'N_520
                                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                         (coe v6) (coe v7) (coe v12)
                                         (coe
                                            d_1N_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                            (coe v5) (coe v6) (coe v7) (coe v12))
                                         (coe v15)))
                                   v14)
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (coe
                                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                      v5
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                         v5
                                         (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                            (coe v5))
                                         v14)
                                      (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_1'35'_212
                                         (coe v5)))
                                   v14)
                                (d_'10214'_'10215'N_520
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v12) (coe du_0N_680 (coe v4) (coe v12)) (coe v15))
                                (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_0'35'_210
                                   (coe v5)))
                             (coe
                                d_0N'45'homo_884 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v5) (coe v6) (coe v7) (coe v12) (coe v15))))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v12
        -> let v13 = subInt (coe v8) (coe (1 :: Integer)) in
           coe
             (case coe v10 of
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v15 v16
                  -> coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                       (\ v17 v18 v19 ->
                          coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v19)
                       (d_'10214'_'10215'H_518
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v13)
                          (coe
                             d__'42'x'43'HN__692 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v5) (coe v6) (coe v7) (coe v13) (coe C_'8709'_510)
                             (coe
                                d_normalise'45'var_850 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v5) (coe v6) (coe v7) (coe v13) (coe v12)))
                          (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v15 v16))
                       (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v16) (coe v12))
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v17
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                              (coe v5) in
                                    coe
                                      (let v18
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                 (coe v17) in
                                       coe
                                         (let v19
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                    (coe v18) in
                                          coe
                                            (let v20
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                       (coe v19) in
                                             coe
                                               (let v21
                                                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                          (coe v20) in
                                                coe
                                                  (let v22
                                                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                             (coe v21) in
                                                   coe
                                                     (let v23
                                                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                (coe v22) in
                                                      coe
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                              (coe v23)))))))))))))
                          (d_'10214'_'10215'H_518
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v13)
                             (coe
                                d__'42'x'43'HN__692 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v5) (coe v6) (coe v7) (coe v13) (coe C_'8709'_510)
                                (coe
                                   d_normalise'45'var_850 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v13) (coe v12)))
                             (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v15 v16))
                          (d_'10214'_'10215'N_520
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v13)
                             (coe
                                d_normalise'45'var_850 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v5) (coe v6) (coe v7) (coe v13) (coe v12))
                             (coe v16))
                          (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v16) (coe v12))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                      (let v17
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                 (coe v5) in
                                       coe
                                         (let v18
                                                = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                    (coe v17) in
                                          coe
                                            (let v19
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                       (coe v18) in
                                             coe
                                               (let v20
                                                      = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                          (coe v19) in
                                                coe
                                                  (let v21
                                                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                             (coe v20) in
                                                   coe
                                                     (let v22
                                                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                (coe v21) in
                                                      coe
                                                        (let v23
                                                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                   (coe v22) in
                                                         coe
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                              (coe
                                                                 MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                 (coe v23)))))))))))))
                             (d_'10214'_'10215'N_520
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v13)
                                (coe
                                   d_normalise'45'var_850 (coe v0) (coe v1) (coe v2) (coe v3)
                                   (coe v4) (coe v5) (coe v6) (coe v7) (coe v13) (coe v12))
                                (coe v16))
                             (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v16) (coe v12))
                             (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v16) (coe v12))
                             (let v17
                                    = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                           (let v17
                                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                      (coe v5) in
                                            coe
                                              (let v18
                                                     = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                         (coe v17) in
                                               coe
                                                 (let v19
                                                        = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                            (coe v18) in
                                                  coe
                                                    (let v20
                                                           = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                               (coe v19) in
                                                     coe
                                                       (let v21
                                                              = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                                  (coe v20) in
                                                        coe
                                                          (let v22
                                                                 = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                     (coe v21) in
                                                           coe
                                                             (let v23
                                                                    = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                        (coe v22) in
                                                              coe
                                                                (coe
                                                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                   (coe
                                                                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                      (coe v23))))))))))) in
                              coe
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                      (coe v17))
                                   (coe
                                      MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v16) (coe v12))))
                             (d_correct'45'var_1302
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v13) (coe v12) (coe v16)))
                          (d_'8709''42'x'43'HN'45'homo_964
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v13)
                             (coe
                                d_normalise'45'var_850 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v5) (coe v6) (coe v7) (coe v13) (coe v12))
                             (coe v15) (coe v16)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring.correct
d_correct_1320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_Polynomial_426 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny
d_correct_1320 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v9 of
      C_op_436 v11 v12 v13
        -> case coe v11 of
             C_'91''43''93'_420
               -> coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                    (\ v14 v15 v16 ->
                       coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v16)
                    (d_'10214'_'10215'N_520
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8)
                       (coe
                          d__'43'N__714 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                          (coe v6) (coe v7) (coe v8)
                          (coe
                             d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v5) (coe v6) (coe v7) (coe v8) (coe v12))
                          (coe
                             d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)))
                       (coe v10))
                    (coe
                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                       v5
                       (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v12) (coe v10))
                       (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v13) (coe v10)))
                    (coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                          (coe
                             MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v14
                                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                           (coe v5) in
                                 coe
                                   (let v15
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                              (coe v14) in
                                    coe
                                      (let v16
                                             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                 (coe v15) in
                                       coe
                                         (let v17
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                    (coe v16) in
                                          coe
                                            (let v18
                                                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                       (coe v17) in
                                             coe
                                               (let v19
                                                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                          (coe v18) in
                                                coe
                                                  (let v20
                                                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                             (coe v19) in
                                                   coe
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                           (coe v20)))))))))))))
                       (d_'10214'_'10215'N_520
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v8)
                          (coe
                             d__'43'N__714 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                             (coe v6) (coe v7) (coe v8)
                             (coe
                                d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v12))
                             (coe
                                d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)))
                          (coe v10))
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                          v5
                          (d_'10214'_'10215''8595'_874
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8) (coe v12) (coe v10))
                          (d_'10214'_'10215''8595'_874
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8) (coe v13) (coe v10)))
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                          v5
                          (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v12) (coe v10))
                          (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v13) (coe v10)))
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v14
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                              (coe v5) in
                                    coe
                                      (let v15
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                 (coe v14) in
                                       coe
                                         (let v16
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                    (coe v15) in
                                          coe
                                            (let v17
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                       (coe v16) in
                                             coe
                                               (let v18
                                                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                          (coe v17) in
                                                coe
                                                  (let v19
                                                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                             (coe v18) in
                                                   coe
                                                     (let v20
                                                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                (coe v19) in
                                                      coe
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                              (coe v20)))))))))))))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (d_'10214'_'10215''8595'_874
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v12) (coe v10))
                             (d_'10214'_'10215''8595'_874
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v13) (coe v10)))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v12) (coe v10))
                             (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v13) (coe v10)))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                             v5
                             (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v12) (coe v10))
                             (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v13) (coe v10)))
                          (let v14
                                 = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                        (let v14
                                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                   (coe v5) in
                                         coe
                                           (let v15
                                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                      (coe v14) in
                                            coe
                                              (let v16
                                                     = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                         (coe v15) in
                                               coe
                                                 (let v17
                                                        = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                            (coe v16) in
                                                  coe
                                                    (let v18
                                                           = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                               (coe v17) in
                                                     coe
                                                       (let v19
                                                              = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                  (coe v18) in
                                                        coe
                                                          (let v20
                                                                 = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                     (coe v19) in
                                                           coe
                                                             (coe
                                                                MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                (coe
                                                                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                   (coe v20))))))))))) in
                           coe
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                   (coe v14))
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'43'__204
                                   v5
                                   (coe
                                      du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v12) (coe v10))
                                   (coe
                                      du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v13)
                                      (coe v10)))))
                          (coe
                             MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                             (coe
                                d_correct_1320 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v12) (coe v10))
                             (coe
                                MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                  (coe
                                                     MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                     (coe
                                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                        (coe v5)))))))))
                                (d_'10214'_'10215''8595'_874
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v12) (coe v10))
                                (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v12) (coe v10))
                                (d_'10214'_'10215''8595'_874
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v13) (coe v10))
                                (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v13) (coe v10)))
                             (coe
                                d_correct_1320 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v13) (coe v10))))
                       (d_'43'N'45'homo_1008
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v8)
                          (coe
                             d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v5) (coe v6) (coe v7) (coe v8) (coe v12))
                          (coe
                             d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v5) (coe v6) (coe v7) (coe v8) (coe v13))
                          (coe v10)))
             C_'91''42''93'_422
               -> coe
                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                    (\ v14 v15 v16 ->
                       coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v16)
                    (d_'10214'_'10215'N_520
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                       (coe v7) (coe v8)
                       (coe
                          d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                          (coe v6) (coe v7) (coe v8)
                          (coe
                             d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v5) (coe v6) (coe v7) (coe v8) (coe v12))
                          (coe
                             d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)))
                       (coe v10))
                    (coe
                       MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                       v5
                       (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v12) (coe v10))
                       (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v13) (coe v10)))
                    (coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                          (coe
                             MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v14
                                       = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                           (coe v5) in
                                 coe
                                   (let v15
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                              (coe v14) in
                                    coe
                                      (let v16
                                             = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                 (coe v15) in
                                       coe
                                         (let v17
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                    (coe v16) in
                                          coe
                                            (let v18
                                                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                       (coe v17) in
                                             coe
                                               (let v19
                                                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                          (coe v18) in
                                                coe
                                                  (let v20
                                                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                             (coe v19) in
                                                   coe
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                           (coe v20)))))))))))))
                       (d_'10214'_'10215'N_520
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v8)
                          (coe
                             d__'42'N__754 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                             (coe v6) (coe v7) (coe v8)
                             (coe
                                d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v12))
                             (coe
                                d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v13)))
                          (coe v10))
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                          v5
                          (d_'10214'_'10215''8595'_874
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8) (coe v12) (coe v10))
                          (d_'10214'_'10215''8595'_874
                             (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                             (coe v7) (coe v8) (coe v13) (coe v10)))
                       (coe
                          MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                          v5
                          (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v12) (coe v10))
                          (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v13) (coe v10)))
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                             (coe
                                MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                (coe
                                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                   (let v14
                                          = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                              (coe v5) in
                                    coe
                                      (let v15
                                             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                 (coe v14) in
                                       coe
                                         (let v16
                                                = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                    (coe v15) in
                                          coe
                                            (let v17
                                                   = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                       (coe v16) in
                                             coe
                                               (let v18
                                                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                          (coe v17) in
                                                coe
                                                  (let v19
                                                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                             (coe v18) in
                                                   coe
                                                     (let v20
                                                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                (coe v19) in
                                                      coe
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                              (coe v20)))))))))))))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (d_'10214'_'10215''8595'_874
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v12) (coe v10))
                             (d_'10214'_'10215''8595'_874
                                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                (coe v7) (coe v8) (coe v13) (coe v10)))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v12) (coe v10))
                             (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v13) (coe v10)))
                          (coe
                             MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                             v5
                             (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v12) (coe v10))
                             (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v13) (coe v10)))
                          (let v14
                                 = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                        (let v14
                                               = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                                   (coe v5) in
                                         coe
                                           (let v15
                                                  = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                                      (coe v14) in
                                            coe
                                              (let v16
                                                     = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                         (coe v15) in
                                               coe
                                                 (let v17
                                                        = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                            (coe v16) in
                                                  coe
                                                    (let v18
                                                           = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                               (coe v17) in
                                                     coe
                                                       (let v19
                                                              = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                  (coe v18) in
                                                        coe
                                                          (let v20
                                                                 = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                     (coe v19) in
                                                           coe
                                                             (coe
                                                                MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                (coe
                                                                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                   (coe v20))))))))))) in
                           coe
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                   (coe v14))
                                (coe
                                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d__'42'__206
                                   v5
                                   (coe
                                      du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v12) (coe v10))
                                   (coe
                                      du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v13)
                                      (coe v10)))))
                          (coe
                             MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                             (coe
                                d_correct_1320 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v12) (coe v10))
                             (coe
                                MAlonzo.Code.Algebra.Structures.d_'42''45'cong_1508
                                (MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                      (coe
                                         MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                         (coe
                                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                            (coe v5)))))
                                (d_'10214'_'10215''8595'_874
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v12) (coe v10))
                                (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v12) (coe v10))
                                (d_'10214'_'10215''8595'_874
                                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                                   (coe v7) (coe v8) (coe v13) (coe v10))
                                (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v13) (coe v10)))
                             (coe
                                d_correct_1320 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                (coe v5) (coe v6) (coe v7) (coe v8) (coe v13) (coe v10))))
                       (d_'42'N'45'homo_1114
                          (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                          (coe v7) (coe v8)
                          (coe
                             d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v5) (coe v6) (coe v7) (coe v8) (coe v12))
                          (coe
                             d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                             (coe v5) (coe v6) (coe v7) (coe v8) (coe v13))
                          (coe v10)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_con_440 v11
        -> coe
             d_correct'45'con_1286 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v11) (coe v10)
      C_var_444 v11
        -> coe
             d_correct'45'var_1302 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7) (coe v8) (coe v11) (coe v10)
      C__'58''94'__450 v11 v12
        -> coe
             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
             (\ v13 v14 v15 ->
                coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v15)
             (d_'10214'_'10215'N_520
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8)
                (coe
                   d__'94'N__824 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8)
                   (coe
                      d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                      (coe v5) (coe v6) (coe v7) (coe v8) (coe v11))
                   (coe v12))
                (coe v10))
             (coe
                MAlonzo.Code.Algebra.Definitions.RawSemiring.du__'94'__90
                (coe
                   MAlonzo.Code.Algebra.Bundles.du_rawSemiring_2260
                   (coe
                      MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                      (coe
                         MAlonzo.Code.Algebra.Bundles.du_semiring_2600
                         (coe
                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.du_commutativeSemiring_320
                            (coe v5)))))
                (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v11) (coe v10))
                (coe v12))
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                   (coe
                      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                      (coe
                         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                         (let v13
                                = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                    (coe v5) in
                          coe
                            (let v14
                                   = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                       (coe v13) in
                             coe
                               (let v15
                                      = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                          (coe v14) in
                                coe
                                  (let v16
                                         = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                             (coe v15) in
                                   coe
                                     (let v17
                                            = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                (coe v16) in
                                      coe
                                        (let v18
                                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                   (coe v17) in
                                         coe
                                           (let v19
                                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                      (coe v18) in
                                            coe
                                              (coe
                                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                 (coe
                                                    MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                    (coe v19)))))))))))))
                (d_'10214'_'10215'N_520
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                   (coe v7) (coe v8)
                   (coe
                      d__'94'N__824 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                      (coe v6) (coe v7) (coe v8)
                      (coe
                         d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                         (coe v5) (coe v6) (coe v7) (coe v8) (coe v11))
                      (coe v12))
                   (coe v10))
                (coe
                   MAlonzo.Code.Algebra.Definitions.RawSemiring.du__'94'__90
                   (coe
                      MAlonzo.Code.Algebra.Bundles.du_rawSemiring_2260
                      (coe
                         MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                         (coe
                            MAlonzo.Code.Algebra.Bundles.du_semiring_2600
                            (coe
                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.du_commutativeSemiring_320
                               (coe v5)))))
                   (coe
                      d_'10214'_'10215''8595'_874 (coe v0) (coe v1) (coe v2) (coe v3)
                      (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v11) (coe v10))
                   (coe v12))
                (coe
                   MAlonzo.Code.Algebra.Definitions.RawSemiring.du__'94'__90
                   (coe
                      MAlonzo.Code.Algebra.Bundles.du_rawSemiring_2260
                      (coe
                         MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                         (coe
                            MAlonzo.Code.Algebra.Bundles.du_semiring_2600
                            (coe
                               MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.du_commutativeSemiring_320
                               (coe v5)))))
                   (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v11) (coe v10))
                   (coe v12))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                            (let v13
                                   = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                       (coe v5) in
                             coe
                               (let v14
                                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe v13) in
                                coe
                                  (let v15
                                         = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                             (coe v14) in
                                   coe
                                     (let v16
                                            = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                (coe v15) in
                                      coe
                                        (let v17
                                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                   (coe v16) in
                                         coe
                                           (let v18
                                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                      (coe v17) in
                                            coe
                                              (let v19
                                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                         (coe v18) in
                                               coe
                                                 (coe
                                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                    (coe
                                                       MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                       (coe v19)))))))))))))
                   (coe
                      MAlonzo.Code.Algebra.Definitions.RawSemiring.du__'94'__90
                      (coe
                         MAlonzo.Code.Algebra.Bundles.du_rawSemiring_2260
                         (coe
                            MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                            (coe
                               MAlonzo.Code.Algebra.Bundles.du_semiring_2600
                               (coe
                                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.du_commutativeSemiring_320
                                  (coe v5)))))
                      (coe
                         d_'10214'_'10215''8595'_874 (coe v0) (coe v1) (coe v2) (coe v3)
                         (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v11) (coe v10))
                      (coe v12))
                   (coe
                      MAlonzo.Code.Algebra.Definitions.RawSemiring.du__'94'__90
                      (coe
                         MAlonzo.Code.Algebra.Bundles.du_rawSemiring_2260
                         (coe
                            MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                            (coe
                               MAlonzo.Code.Algebra.Bundles.du_semiring_2600
                               (coe
                                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.du_commutativeSemiring_320
                                  (coe v5)))))
                      (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v11) (coe v10))
                      (coe v12))
                   (coe
                      MAlonzo.Code.Algebra.Definitions.RawSemiring.du__'94'__90
                      (coe
                         MAlonzo.Code.Algebra.Bundles.du_rawSemiring_2260
                         (coe
                            MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                            (coe
                               MAlonzo.Code.Algebra.Bundles.du_semiring_2600
                               (coe
                                  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.du_commutativeSemiring_320
                                  (coe v5)))))
                      (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v11) (coe v10))
                      (coe v12))
                   (let v13
                          = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                 (let v13
                                        = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                            (coe v5) in
                                  coe
                                    (let v14
                                           = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                               (coe v13) in
                                     coe
                                       (let v15
                                              = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                  (coe v14) in
                                        coe
                                          (let v16
                                                 = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                     (coe v15) in
                                           coe
                                             (let v17
                                                    = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                        (coe v16) in
                                              coe
                                                (let v18
                                                       = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                           (coe v17) in
                                                 coe
                                                   (let v19
                                                          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                              (coe v18) in
                                                    coe
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                            (coe v19))))))))))) in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                            (coe v13))
                         (coe
                            MAlonzo.Code.Algebra.Definitions.RawSemiring.du__'94'__90
                            (coe
                               MAlonzo.Code.Algebra.Bundles.du_rawSemiring_2260
                               (coe
                                  MAlonzo.Code.Algebra.Bundles.du_semiringWithoutAnnihilatingZero_2422
                                  (coe
                                     MAlonzo.Code.Algebra.Bundles.du_semiring_2600
                                     (coe
                                        MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.du_commutativeSemiring_320
                                        (coe v5)))))
                            (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v11) (coe v10))
                            (coe v12))))
                   (coe
                      MAlonzo.Code.Function.Base.du__'10216'_'10217'__240
                      (coe
                         d_correct_1320 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                         (coe v5) (coe v6) (coe v7) (coe v8) (coe v11) (coe v10))
                      (\ v13 v14 ->
                         coe
                           MAlonzo.Code.Algebra.Properties.Semiring.Exp.du_'94''45'cong_222
                           (coe
                              MAlonzo.Code.Algebra.Bundles.du_semiring_2600
                              (coe
                                 MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.du_commutativeSemiring_320
                                 (coe v5)))
                           (coe
                              d_'10214'_'10215''8595'_874 (coe v0) (coe v1) (coe v2) (coe v3)
                              (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v11) (coe v10))
                           (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v11) (coe v10))
                           (coe v12) v13)
                      erased))
                (d_'94'N'45'homo_1240
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                   (coe v7) (coe v8)
                   (coe
                      d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                      (coe v5) (coe v6) (coe v7) (coe v8) (coe v11))
                   (coe v12) (coe v10)))
      C_'58''45'__454 v11
        -> coe
             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
             (\ v12 v13 v14 ->
                coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v14)
             (d_'10214'_'10215'N_520
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                (coe v7) (coe v8)
                (coe
                   d_'45'N__834 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                   (coe v6) (coe v7) (coe v8)
                   (coe
                      d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                      (coe v5) (coe v6) (coe v7) (coe v8) (coe v11)))
                (coe v10))
             (coe
                MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                v5
                (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v11) (coe v10)))
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                   (coe
                      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                      (coe
                         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                         (let v12
                                = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                    (coe v5) in
                          coe
                            (let v13
                                   = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                       (coe v12) in
                             coe
                               (let v14
                                      = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                          (coe v13) in
                                coe
                                  (let v15
                                         = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                             (coe v14) in
                                   coe
                                     (let v16
                                            = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                (coe v15) in
                                      coe
                                        (let v17
                                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                   (coe v16) in
                                         coe
                                           (let v18
                                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                      (coe v17) in
                                            coe
                                              (coe
                                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                 (coe
                                                    MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                    (coe v18)))))))))))))
                (d_'10214'_'10215'N_520
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                   (coe v7) (coe v8)
                   (coe
                      d_'45'N__834 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                      (coe v6) (coe v7) (coe v8)
                      (coe
                         d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                         (coe v5) (coe v6) (coe v7) (coe v8) (coe v11)))
                   (coe v10))
                (coe
                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                   v5
                   (d_'10214'_'10215''8595'_874
                      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                      (coe v7) (coe v8) (coe v11) (coe v10)))
                (coe
                   MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                   v5
                   (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v11) (coe v10)))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                            (let v12
                                   = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                       (coe v5) in
                             coe
                               (let v13
                                      = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                          (coe v12) in
                                coe
                                  (let v14
                                         = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                             (coe v13) in
                                   coe
                                     (let v15
                                            = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                (coe v14) in
                                      coe
                                        (let v16
                                               = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                   (coe v15) in
                                         coe
                                           (let v17
                                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                      (coe v16) in
                                            coe
                                              (let v18
                                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                         (coe v17) in
                                               coe
                                                 (coe
                                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                    (coe
                                                       MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                       (coe v18)))))))))))))
                   (coe
                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                      v5
                      (d_'10214'_'10215''8595'_874
                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                         (coe v7) (coe v8) (coe v11) (coe v10)))
                   (coe
                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                      v5
                      (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v11) (coe v10)))
                   (coe
                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                      v5
                      (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v11) (coe v10)))
                   (let v12
                          = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                 (let v12
                                        = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                                            (coe v5) in
                                  coe
                                    (let v13
                                           = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                                               (coe v12) in
                                     coe
                                       (let v14
                                              = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710
                                                  (coe v13) in
                                        coe
                                          (let v15
                                                 = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                                                     (coe v14) in
                                           coe
                                             (let v16
                                                    = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                                                        (coe v15) in
                                              coe
                                                (let v17
                                                       = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                           (coe v16) in
                                                 coe
                                                   (let v18
                                                          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                              (coe v17) in
                                                    coe
                                                      (coe
                                                         MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                         (coe
                                                            MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                            (coe v18))))))))))) in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                            (coe v12))
                         (coe
                            MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45'__208
                            v5
                            (coe
                               du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v11) (coe v10)))))
                   (coe
                      MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_'45''8255'cong_64
                      (MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                         (coe v5))
                      (d_'10214'_'10215''8595'_874
                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                         (coe v7) (coe v8) (coe v11) (coe v10))
                      (coe du_'10214'_'10215'_478 (coe v5) (coe v6) (coe v11) (coe v10))
                      (d_correct_1320
                         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                         (coe v7) (coe v8) (coe v11) (coe v10))))
                (d_'45'N'8255''45'homo_1266
                   (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
                   (coe v7) (coe v8)
                   (coe
                      d_normalise_854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                      (coe v5) (coe v6) (coe v7) (coe v8) (coe v11))
                   (coe v10)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Solver.Ring._._⊜_
d__'8860'__1354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  T_Polynomial_426 ->
  T_Polynomial_426 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'8860'__1354 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du__'8860'__1354
du__'8860'__1354 ::
  Integer ->
  T_Polynomial_426 ->
  T_Polynomial_426 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'8860'__1354 v0
  = coe MAlonzo.Code.Relation.Binary.Reflection.du__'8860'__142
-- Algebra.Solver.Ring._.prove
d_prove_1356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  T_Polynomial_426 -> T_Polynomial_426 -> AgdaAny -> AgdaAny
d_prove_1356 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Relation.Binary.Reflection.du_prove_90
      (let v8
             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                 (coe v5) in
       coe
         (let v9
                = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                    (coe v8) in
          coe
            (let v10
                   = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v9) in
             coe
               (let v11
                      = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                          (coe v10) in
                coe
                  (let v12
                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                             (coe v11) in
                   coe
                     (let v13
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v12) in
                      coe
                        (let v14
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v13) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v14))))))))))
      (\ v8 v9 v10 ->
         coe du_'10214'_'10215'_478 (coe v5) (coe v6) v9 v10)
      (coe
         d_'10214'_'10215''8595'_874 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4) (coe v5) (coe v6) (coe v7))
      (coe
         d_correct_1320 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7))
-- Algebra.Solver.Ring._.solve
d_solve_1358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T_AlmostCommutativeRing_178 ->
  MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.T__'45'Raw'45'AlmostCommutative'10230'__358 ->
  (AgdaAny -> AgdaAny -> Maybe AgdaAny) ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_solve_1358 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Relation.Binary.Reflection.du_solve_114
      (let v8
             = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isAlmostCommutativeRing_214
                 (coe v5) in
       coe
         (let v9
                = MAlonzo.Code.Algebra.Solver.Ring.AlmostCommutativeRing.d_isCommutativeSemiring_62
                    (coe v8) in
          coe
            (let v10
                   = MAlonzo.Code.Algebra.Structures.d_isSemiring_1710 (coe v9) in
             coe
               (let v11
                      = MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1602
                          (coe v10) in
                coe
                  (let v12
                         = MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1506
                             (coe v11) in
                   coe
                     (let v13
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v12) in
                      coe
                        (let v14
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v13) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v14))))))))))
      (coe (\ v8 -> coe C_var_444))
      (\ v8 v9 v10 ->
         coe du_'10214'_'10215'_478 (coe v5) (coe v6) v9 v10)
      (coe
         d_'10214'_'10215''8595'_874 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4) (coe v5) (coe v6) (coe v7))
      (coe
         d_correct_1320 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6) (coe v7))
