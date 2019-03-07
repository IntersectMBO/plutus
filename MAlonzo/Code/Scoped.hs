{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Scoped where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Builtin.Constant.Type
import qualified MAlonzo.Code.Category.Monad.Indexed
import qualified MAlonzo.Code.Data.Fin
import qualified MAlonzo.Code.Data.Maybe
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.String
import qualified MAlonzo.Code.Data.Vec
import qualified MAlonzo.Code.Raw
import qualified MAlonzo.Code.Relation.Nullary

import Scoped
name2 = "Scoped.ScopedKind"
d2 = ()
type T2 = ScKind
pattern C4 = ScKiStar
pattern C6 = ScKiSize
pattern C8 a0 a1 = ScKiFun a0 a1
check4 :: T2
check4 = ScKiStar
check6 :: T2
check6 = ScKiSize
check8 :: T2 -> T2 -> T2
check8 = ScKiFun
cover2 :: ScKind -> ()
cover2 x
  = case x of
      ScKiStar -> ()
      ScKiSize -> ()
      ScKiFun _ _ -> ()
name12 = "Scoped.ScopedTy"
d12 a0 = ()
data T12
  = C16 MAlonzo.Code.Data.Fin.T4 | C18 T12 T12 | C20 T2 T12 |
    C22 T2 T12 | C24 T12 T12 |
    C26 MAlonzo.Code.Builtin.Constant.Type.T248 | C28 Integer
name30 = "Scoped.Weirdℕ"
d30 = ()
data T30 = C32 | C34 T30 | C36 T30
name38 = "Scoped.WeirdFin"
d38 a0 = ()
data T38 = C42 | C46 T38 | C50 T38
name52 = "Scoped.∥_∥"
d52 :: T30 -> Integer
d52 v0
  = case coe v0 of
      C32 -> coe (0 :: Integer)
      C34 v1 -> coe (d52 (coe v1))
      C36 v1 -> coe (addInt (coe (1 :: Integer)) (coe (d52 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
name58 = "Scoped.SizedTermCon"
d58 = ()
data T58
  = C64 Integer Integer MAlonzo.Code.Agda.Builtin.Sigma.T14 |
    C70 Integer MAlonzo.Code.Builtin.Constant.Type.T6
        MAlonzo.Code.Data.Nat.Base.T6 |
    C72 Integer | C74 MAlonzo.Code.Agda.Builtin.String.T6
name76 = "Scoped.ScopedTm"
d76 a0 = ()
data T76
  = C80 T38 | C84 T2 T76 | C88 T76 T12 | C92 T12 T76 | C96 T76 T76 |
    C100 T58 | C104 T12 | C108 MAlonzo.Code.Builtin.T2
name110 = "Scoped.deBruijnifyK"
d110 :: MAlonzo.Code.Raw.T2 -> T2
d110 v0
  = case coe v0 of
      MAlonzo.Code.Raw.C4 -> coe C4
      MAlonzo.Code.Raw.C6 v1 v2
        -> coe (C8 (coe (d110 (coe v1))) (coe (d110 (coe v2))))
      MAlonzo.Code.Raw.C8 -> coe C6
      _ -> MAlonzo.RTE.mazUnreachableError
name154 = "Scoped.velemIndex"
d154 ::
  MAlonzo.Code.Agda.Builtin.String.T6 ->
  Integer ->
  MAlonzo.Code.Data.Vec.T8 ->
  MAlonzo.Code.Data.Maybe.Base.T10 AgdaAny MAlonzo.Code.Data.Fin.T4
d154 v0 v1 v2 = du154 v0 v2
du154 ::
  MAlonzo.Code.Agda.Builtin.String.T6 ->
  MAlonzo.Code.Data.Vec.T8 ->
  MAlonzo.Code.Data.Maybe.Base.T10 AgdaAny MAlonzo.Code.Data.Fin.T4
du154 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Vec.C14 -> coe MAlonzo.Code.Data.Maybe.Base.C20
      MAlonzo.Code.Data.Vec.C22 v3 v4
        -> let v5 = MAlonzo.Code.Data.String.d14 (coe v0) (coe v3) in
           case coe v5 of
             MAlonzo.Code.Relation.Nullary.C22 v6
               -> coe
                    (MAlonzo.Code.Data.Maybe.Base.C18
                       (coe (\ v7 -> MAlonzo.Code.Data.Fin.C8) erased))
             MAlonzo.Code.Relation.Nullary.C26
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du116 MAlonzo.Code.Data.Fin.C14
                    (du154 (coe v0) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name186 = "Scoped.deBruijnifyTy"
d186 ::
  Integer ->
  MAlonzo.Code.Data.Vec.T8 ->
  MAlonzo.Code.Raw.T10 ->
  MAlonzo.Code.Data.Maybe.Base.T10 AgdaAny T12
d186 v0 v1 v2 = du186 v1 v2
du186 ::
  MAlonzo.Code.Data.Vec.T8 ->
  MAlonzo.Code.Raw.T10 ->
  MAlonzo.Code.Data.Maybe.Base.T10 AgdaAny T12
du186 v0 v1
  = case coe v1 of
      MAlonzo.Code.Raw.C12 v2
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du116 C16 (du154 (coe v2) (coe v0))
      MAlonzo.Code.Raw.C14 v2 v3
        -> coe
             MAlonzo.Code.Category.Monad.Indexed.d58
             MAlonzo.Code.Data.Maybe.du64 erased erased erased erased erased
             (du186 (coe v0) (coe v2))
             (\ v4 ->
                coe
                  MAlonzo.Code.Category.Monad.Indexed.d58
                  MAlonzo.Code.Data.Maybe.du64 erased erased erased erased erased
                  (du186 (coe v0) (coe v3))
                  (\ v5 ->
                     coe
                       MAlonzo.Code.Category.Monad.Indexed.d46
                       MAlonzo.Code.Data.Maybe.du64 erased erased
                       (C18 (coe v4) (coe v5))))
      MAlonzo.Code.Raw.C16 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du116 (C20 (coe (d110 (coe v3))))
             (du186
                (coe (\ v5 v6 v7 -> MAlonzo.Code.Data.Vec.C22 v6 v7) erased v2 v0)
                (coe v4))
      MAlonzo.Code.Raw.C18 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du116 (C22 (coe (d110 (coe v3))))
             (du186
                (coe (\ v5 v6 v7 -> MAlonzo.Code.Data.Vec.C22 v6 v7) erased v2 v0)
                (coe v4))
      MAlonzo.Code.Raw.C20 v2 v3
        -> coe
             MAlonzo.Code.Category.Monad.Indexed.d58
             MAlonzo.Code.Data.Maybe.du64 erased erased erased erased erased
             (du186 (coe v0) (coe v2))
             (\ v4 ->
                coe
                  MAlonzo.Code.Category.Monad.Indexed.d58
                  MAlonzo.Code.Data.Maybe.du64 erased erased erased erased erased
                  (du186 (coe v0) (coe v3))
                  (\ v5 ->
                     coe
                       MAlonzo.Code.Category.Monad.Indexed.d46
                       MAlonzo.Code.Data.Maybe.du64 erased erased
                       (C24 (coe v4) (coe v5))))
      MAlonzo.Code.Raw.C22 v2
        -> coe (MAlonzo.Code.Data.Maybe.Base.C18 (coe (C26 (coe v2))))
      MAlonzo.Code.Raw.C24 v2
        -> coe (MAlonzo.Code.Data.Maybe.Base.C18 (coe (C28 (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
name238 = "Scoped.WeirdVec"
d238 a0 a1 = ()
data T238 = C242 | C246 AgdaAny T238 | C250 AgdaAny T238
name256 = "Scoped.∥_∥Vec"
d256 :: () -> T30 -> T238 -> MAlonzo.Code.Data.Vec.T8
d256 v0 v1 v2 = du256 v1 v2
du256 :: T30 -> T238 -> MAlonzo.Code.Data.Vec.T8
du256 v0 v1
  = case coe v1 of
      C242 -> coe MAlonzo.Code.Data.Vec.C14
      C246 v3 v4
        -> case coe v0 of
             C34 v5 -> coe (du256 (coe v5) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C250 v3 v4
        -> case coe v0 of
             C36 v5
               -> coe
                    (\ v6 v7 v8 -> MAlonzo.Code.Data.Vec.C22 v7 v8) erased v3
                    (du256 (coe v5) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name268 = "Scoped.velemIndexWeird"
d268 ::
  MAlonzo.Code.Agda.Builtin.String.T6 ->
  T30 -> T238 -> MAlonzo.Code.Data.Maybe.Base.T10 AgdaAny T38
d268 v0 v1 v2
  = case coe v2 of
      C242 -> coe MAlonzo.Code.Data.Maybe.Base.C20
      C246 v4 v5
        -> case coe v1 of
             C34 v6
               -> let v7 = MAlonzo.Code.Data.String.d14 (coe v0) (coe v4) in
                  case coe v7 of
                    MAlonzo.Code.Relation.Nullary.C22 v8
                      -> coe
                           (MAlonzo.Code.Data.Maybe.Base.C18 (coe (\ v9 -> C42) erased))
                    MAlonzo.Code.Relation.Nullary.C26
                      -> coe
                           MAlonzo.Code.Data.Maybe.Base.du116 C46
                           (d268 (coe v0) (coe v6) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C250 v4 v5
        -> case coe v1 of
             C36 v6
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du116 C50
                    (d268 (coe v0) (coe v6) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
name300 = "Scoped.checkSize"
d300 ::
  MAlonzo.Code.Raw.T26 ->
  MAlonzo.Code.Data.Maybe.Base.T10 AgdaAny T58
d300 v0
  = case coe v0 of
      MAlonzo.Code.Raw.C28 v1 v2
        -> let v3
                 = MAlonzo.Code.Builtin.Constant.Type.d164 (coe v1) (coe v2) in
           case coe v3 of
             MAlonzo.Code.Relation.Nullary.C22 v4
               -> coe
                    (MAlonzo.Code.Data.Maybe.Base.C18
                       (coe (C64 (coe v1) (coe v2) (coe v4))))
             MAlonzo.Code.Relation.Nullary.C26
               -> coe MAlonzo.Code.Data.Maybe.Base.C20
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Raw.C30 v1 v2
        -> let v3
                 = MAlonzo.Code.Builtin.Constant.Type.d196 (coe v1) (coe v2) in
           case coe v3 of
             MAlonzo.Code.Relation.Nullary.C22 v4
               -> coe
                    (MAlonzo.Code.Data.Maybe.Base.C18
                       (coe (C70 (coe v1) (coe v2) (coe v4))))
             MAlonzo.Code.Relation.Nullary.C26
               -> coe MAlonzo.Code.Data.Maybe.Base.C20
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Raw.C32 v1
        -> coe (MAlonzo.Code.Data.Maybe.Base.C18 (coe (C72 (coe v1))))
      MAlonzo.Code.Raw.C34 v1
        -> coe (MAlonzo.Code.Data.Maybe.Base.C18 (coe (C74 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
name348 = "Scoped.deBruijnifyTm"
d348 ::
  T30 ->
  T238 ->
  MAlonzo.Code.Raw.T36 ->
  MAlonzo.Code.Data.Maybe.Base.T10 AgdaAny T76
d348 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Raw.C38 v3
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du116 C80
             (d268 (coe v3) (coe v0) (coe v1))
      MAlonzo.Code.Raw.C40 v3 v4 v5
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du116 (C84 (coe (d110 (coe v4))))
             (d348
                (coe (C36 (coe v0))) (coe (\ v6 v7 v8 -> C250 v7 v8) erased v3 v1)
                (coe v5))
      MAlonzo.Code.Raw.C42 v3 v4
        -> coe
             MAlonzo.Code.Category.Monad.Indexed.d58
             MAlonzo.Code.Data.Maybe.du64 erased erased erased erased erased
             (d348 (coe v0) (coe v1) (coe v3))
             (\ v5 ->
                coe
                  MAlonzo.Code.Category.Monad.Indexed.d58
                  MAlonzo.Code.Data.Maybe.du64 erased erased erased erased erased
                  (du186 (coe (du256 (coe v0) (coe v1))) (coe v4))
                  (\ v6 ->
                     coe
                       MAlonzo.Code.Category.Monad.Indexed.d46
                       MAlonzo.Code.Data.Maybe.du64 erased erased
                       (coe (\ v7 v8 v9 -> C88 v8 v9) erased v5 v6)))
      MAlonzo.Code.Raw.C44 v3 v4 v5
        -> coe
             MAlonzo.Code.Category.Monad.Indexed.d58
             MAlonzo.Code.Data.Maybe.du64 erased erased erased erased erased
             (du186 (coe (du256 (coe v0) (coe v1))) (coe v4))
             (\ v6 ->
                coe
                  MAlonzo.Code.Category.Monad.Indexed.d58
                  MAlonzo.Code.Data.Maybe.du64 erased erased erased erased erased
                  (d348
                     (coe (C34 (coe v0))) (coe (\ v7 v8 v9 -> C246 v8 v9) erased v3 v1)
                     (coe v5))
                  (\ v7 ->
                     coe
                       MAlonzo.Code.Category.Monad.Indexed.d46
                       MAlonzo.Code.Data.Maybe.du64 erased erased
                       (coe (\ v8 v9 v10 -> C92 v9 v10) erased v6 v7)))
      MAlonzo.Code.Raw.C46 v3 v4
        -> coe
             MAlonzo.Code.Category.Monad.Indexed.d58
             MAlonzo.Code.Data.Maybe.du64 erased erased erased erased erased
             (d348 (coe v0) (coe v1) (coe v3))
             (\ v5 ->
                coe
                  MAlonzo.Code.Category.Monad.Indexed.d58
                  MAlonzo.Code.Data.Maybe.du64 erased erased erased erased erased
                  (d348 (coe v0) (coe v1) (coe v4))
                  (\ v6 ->
                     coe
                       MAlonzo.Code.Category.Monad.Indexed.d46
                       MAlonzo.Code.Data.Maybe.du64 erased erased
                       (coe (\ v7 v8 v9 -> C96 v8 v9) erased v5 v6)))
      MAlonzo.Code.Raw.C48 v3
        -> coe MAlonzo.Code.Data.Maybe.Base.du116 C100 (d300 (coe v3))
      MAlonzo.Code.Raw.C50 v3
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du116 C104
             (du186 (coe (du256 (coe v0) (coe v1))) (coe v3))
      MAlonzo.Code.Raw.C52 v3
        -> coe
             (MAlonzo.Code.Data.Maybe.Base.C18
                (coe (\ v4 v5 -> C108 v5) erased v3))
      _ -> MAlonzo.RTE.mazUnreachableError
