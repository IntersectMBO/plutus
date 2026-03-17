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

module MAlonzo.Code.Class.DecEq.Instances where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Data.Bool.Properties
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Fin.Properties
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.List.NonEmpty.Base
import qualified MAlonzo.Code.Data.List.Properties
import qualified MAlonzo.Code.Data.Maybe.Properties
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Product.Properties
import qualified MAlonzo.Code.Data.Rational.Properties
import qualified MAlonzo.Code.Data.Refinement.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Properties
import qualified MAlonzo.Code.Data.These.Properties
import qualified MAlonzo.Code.Data.Unit.Properties
import qualified MAlonzo.Code.Data.Vec.Properties
import qualified MAlonzo.Code.Reflection.AST.Argument
import qualified MAlonzo.Code.Reflection.AST.Argument.Information
import qualified MAlonzo.Code.Reflection.AST.Argument.Modality
import qualified MAlonzo.Code.Reflection.AST.Argument.Visibility
import qualified MAlonzo.Code.Reflection.AST.Literal
import qualified MAlonzo.Code.Reflection.AST.Meta
import qualified MAlonzo.Code.Reflection.AST.Name
import qualified MAlonzo.Code.Reflection.AST.Term
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Class.DecEq.Instances.DecEq-⊥
d_DecEq'45''8869'_6 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45''8869'_6
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe (\ v0 -> MAlonzo.RTE.mazUnreachableError))
-- Class.DecEq.Instances.DecEq-⊤
d_DecEq'45''8868'_10 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45''8868'_10
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (\ v0 v1 -> coe MAlonzo.Code.Data.Unit.Properties.du__'8799'__8)
-- Class.DecEq.Instances.DecEq-Bool
d_DecEq'45'Bool_16 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'Bool_16
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe MAlonzo.Code.Data.Bool.Properties.d__'8799'__3104)
-- Class.DecEq.Instances.DecEq-ℕ
d_DecEq'45'ℕ_22 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'ℕ_22
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe MAlonzo.Code.Data.Nat.Properties.d__'8799'__2710)
-- Class.DecEq.Instances.DecEq-ℤ
d_DecEq'45'ℤ_28 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'ℤ_28
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe MAlonzo.Code.Data.Integer.Properties.d__'8799'__2714)
-- Class.DecEq.Instances.DecEq-ℚ
d_DecEq'45'ℚ_34 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'ℚ_34
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe MAlonzo.Code.Data.Rational.Properties.d__'8799'__2706)
-- Class.DecEq.Instances.DecEq-Char
d_DecEq'45'Char_40 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'Char_40
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
-- Class.DecEq.Instances.DecEq-String
d_DecEq'45'String_46 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'String_46
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54)
-- Class.DecEq.Instances.DecEq-Fin
d_DecEq'45'Fin_52 ::
  Integer -> MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'Fin_52 ~v0 = du_DecEq'45'Fin_52
du_DecEq'45'Fin_52 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
du_DecEq'45'Fin_52
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe MAlonzo.Code.Data.Fin.Properties.du__'8799'__50)
-- Class.DecEq.Instances.DecEq-List
d_DecEq'45'List_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'List_58 ~v0 ~v1 v2 = du_DecEq'45'List_58 v2
du_DecEq'45'List_58 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
du_DecEq'45'List_58 v0
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe
         MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
         (coe MAlonzo.Code.Class.DecEq.Core.d__'8799'__16 (coe v0)))
-- Class.DecEq.Instances.∷-injective
d_'8759''45'injective_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8759''45'injective_72 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8759''45'injective_72
du_'8759''45'injective_72 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8759''45'injective_72
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Class.DecEq.Instances._.DecEq-List⁺
d_DecEq'45'List'8314'_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'List'8314'_82 ~v0 ~v1 v2 = du_DecEq'45'List'8314'_82 v2
du_DecEq'45'List'8314'_82 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
du_DecEq'45'List'8314'_82 v0
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe
         (\ v1 ->
            case coe v1 of
              MAlonzo.Code.Data.List.NonEmpty.Base.C__'8759'__34 v2 v3
                -> coe
                     (\ v4 ->
                        case coe v4 of
                          MAlonzo.Code.Data.List.NonEmpty.Base.C__'8759'__34 v5 v6
                            -> let v7
                                     = coe MAlonzo.Code.Class.DecEq.Core.d__'8799'__16 v0 v2 v5 in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                      -> if coe v8
                                           then coe
                                                  seq (coe v9)
                                                  (let v10
                                                         = coe
                                                             MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
                                                             (coe
                                                                MAlonzo.Code.Class.DecEq.Core.d__'8799'__16
                                                                (coe v0))
                                                             (coe v3) (coe v6) in
                                                   coe
                                                     (case coe v10 of
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                          -> if coe v11
                                                               then coe
                                                                      seq (coe v12)
                                                                      (coe
                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                         (coe v11)
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                            erased))
                                                               else coe
                                                                      seq (coe v12)
                                                                      (coe
                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                         (coe v11)
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                           else coe
                                                  seq (coe v9)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v8)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Class.DecEq.Instances._.DecEq-Vec
d_DecEq'45'Vec_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  Integer -> MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'Vec_136 ~v0 ~v1 v2 ~v3 = du_DecEq'45'Vec_136 v2
du_DecEq'45'Vec_136 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
du_DecEq'45'Vec_136 v0
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe
         MAlonzo.Code.Data.Vec.Properties.du_'8801''45'dec_92
         (coe MAlonzo.Code.Class.DecEq.Core.d__'8799'__16 (coe v0)))
-- Class.DecEq.Instances._.DecEq-Maybe
d_DecEq'45'Maybe_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'Maybe_142 ~v0 ~v1 v2 = du_DecEq'45'Maybe_142 v2
du_DecEq'45'Maybe_142 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
du_DecEq'45'Maybe_142 v0
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe
         MAlonzo.Code.Data.Maybe.Properties.du_'8801''45'dec_24
         (coe MAlonzo.Code.Class.DecEq.Core.d__'8799'__16 (coe v0)))
-- Class.DecEq.Instances._.DecEq-Refinement
d_DecEq'45'Refinement_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) -> MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'Refinement_150 ~v0 ~v1 v2 ~v3 ~v4
  = du_DecEq'45'Refinement_150 v2
du_DecEq'45'Refinement_150 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
du_DecEq'45'Refinement_150 v0
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe
         (\ v1 v2 ->
            let v3
                  = coe
                      MAlonzo.Code.Class.DecEq.Core.d__'8799'__16 v0
                      (MAlonzo.Code.Data.Refinement.Base.d_value_38 (coe v1))
                      (MAlonzo.Code.Data.Refinement.Base.d_value_38 (coe v2)) in
            coe
              (case coe v3 of
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                   -> if coe v4
                        then coe
                               seq (coe v5)
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe v4)
                                  (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
                        else coe
                               seq (coe v5)
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe v4)
                                  (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                 _ -> MAlonzo.RTE.mazUnreachableError)))
-- Class.DecEq.Instances._.DecEq-×
d_DecEq'45''215'_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45''215'_182 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_DecEq'45''215'_182 v4 v5
du_DecEq'45''215'_182 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
du_DecEq'45''215'_182 v0 v1
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe
         MAlonzo.Code.Data.Product.Properties.du_'8801''45'dec_78
         (coe MAlonzo.Code.Class.DecEq.Core.d__'8799'__16 (coe v0))
         (coe
            (\ v2 -> MAlonzo.Code.Class.DecEq.Core.d__'8799'__16 (coe v1))))
-- Class.DecEq.Instances._.DecEq-⊎
d_DecEq'45''8846'_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45''8846'_188 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_DecEq'45''8846'_188 v4 v5
du_DecEq'45''8846'_188 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
du_DecEq'45''8846'_188 v0 v1
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe
         MAlonzo.Code.Data.Sum.Properties.du_'8801''45'dec_54
         (coe MAlonzo.Code.Class.DecEq.Core.d__'8799'__16 (coe v0))
         (coe MAlonzo.Code.Class.DecEq.Core.d__'8799'__16 (coe v1)))
-- Class.DecEq.Instances._.DecEq-These
d_DecEq'45'These_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'These_194 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_DecEq'45'These_194 v4 v5
du_DecEq'45'These_194 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
du_DecEq'45'These_194 v0 v1
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe
         MAlonzo.Code.Data.These.Properties.du_'8801''45'dec_60
         (coe MAlonzo.Code.Class.DecEq.Core.d__'8799'__16 (coe v0))
         (coe MAlonzo.Code.Class.DecEq.Core.d__'8799'__16 (coe v1)))
-- Class.DecEq.Instances.DecEq-Name
d_DecEq'45'Name_200 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'Name_200
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe MAlonzo.Code.Reflection.AST.Name.d__'8799'__12)
-- Class.DecEq.Instances.DecEq-Lit
d_DecEq'45'Lit_206 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'Lit_206
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe MAlonzo.Code.Reflection.AST.Literal.d__'8799'__48)
-- Class.DecEq.Instances.DecEq-Meta
d_DecEq'45'Meta_212 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'Meta_212
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe MAlonzo.Code.Reflection.AST.Meta.d__'8799'__10)
-- Class.DecEq.Instances.DecEq-Term
d_DecEq'45'Term_218 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'Term_218
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe MAlonzo.Code.Reflection.AST.Term.d__'8799'__224)
-- Class.DecEq.Instances.DecEq-Mod
d_DecEq'45'Mod_224 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'Mod_224
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe MAlonzo.Code.Reflection.AST.Argument.Modality.d__'8799'__30)
-- Class.DecEq.Instances.DecEq-Vis
d_DecEq'45'Vis_230 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'Vis_230
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe MAlonzo.Code.Reflection.AST.Argument.Visibility.d__'8799'__8)
-- Class.DecEq.Instances.DecEq-ArgI
d_DecEq'45'ArgI_236 :: MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'ArgI_236
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe
         MAlonzo.Code.Reflection.AST.Argument.Information.d__'8799'__30)
-- Class.DecEq.Instances.DecEq-Arg
d_DecEq'45'Arg_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'Arg_242 ~v0 ~v1 v2 = du_DecEq'45'Arg_242 v2
du_DecEq'45'Arg_242 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
du_DecEq'45'Arg_242 v0
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe
         MAlonzo.Code.Reflection.AST.Argument.du_'8801''45'dec_96
         (coe MAlonzo.Code.Class.DecEq.Core.d__'8799'__16 (coe v0)))
