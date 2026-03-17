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

module MAlonzo.Code.Reflection.Utils.Debug where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Functor.Instances
import qualified MAlonzo.Code.Class.Monad.Core
import qualified MAlonzo.Code.Class.Monad.Instances
import qualified MAlonzo.Code.Class.Show.Core
import qualified MAlonzo.Code.Class.Show.Instances
import qualified MAlonzo.Code.Class.Traversable.Core
import qualified MAlonzo.Code.Class.Traversable.Instances
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Meta.Prelude
import qualified MAlonzo.Code.Reflection.AST.Show

-- Reflection.Utils.Debug.error
d_error_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_error_6 v0 ~v1 v2 = du_error_6 v0 v2
du_error_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
du_error_6 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.d_typeError_344 v0 erased
      (coe
         MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
         (coe MAlonzo.Code.Agda.Builtin.Reflection.C_strErr_310 (coe v1)))
-- Reflection.Utils.Debug._IMPOSSIBLE_
d__IMPOSSIBLE__10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny
d__IMPOSSIBLE__10 v0 ~v1 = du__IMPOSSIBLE__10 v0
du__IMPOSSIBLE__10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> AgdaAny
du__IMPOSSIBLE__10 v0
  = coe du_error_6 (coe v0) (coe ("IMPOSSIBLE" :: Data.Text.Text))
-- Reflection.Utils.Debug.Debug.print
d_print_16 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_print_16 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.d_debugPrint_462
      (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0))
      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0))
      (coe
         MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
         (coe MAlonzo.Code.Agda.Builtin.Reflection.C_strErr_310 (coe v1)))
-- Reflection.Utils.Debug.Debug.printLn
d_printLn_18 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_printLn_18 v0 v1
  = coe
      d_print_16 (coe v0)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
         ("\n" :: Data.Text.Text))
-- Reflection.Utils.Debug.Debug.printLns
d_printLns_24 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> AgdaAny
d_printLns_24 v0 v1
  = coe
      d_print_16 (coe v0)
      (coe MAlonzo.Code.Data.String.Base.d_unlines_36 v1)
-- Reflection.Utils.Debug.Debug.printS
d_printS_28 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Class.Show.Core.T_Show_10 -> AgdaAny -> AgdaAny
d_printS_28 v0 ~v1 ~v2 v3 v4 = du_printS_28 v0 v3 v4
du_printS_28 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 -> AgdaAny -> AgdaAny
du_printS_28 v0 v1 v2
  = coe
      d_print_16 (coe v0)
      (coe MAlonzo.Code.Class.Show.Core.d_show_16 v1 v2)
-- Reflection.Utils.Debug.Debug.errorP
d_errorP_30 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_errorP_30 v0 v1 ~v2 v3 = du_errorP_30 v0 v1 v3
du_errorP_30 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
du_errorP_30 v0 v1 v2
  = coe
      MAlonzo.Code.Class.Monad.Core.du__'62''62'__24
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6) (coe ())
      (coe v1) (coe d_printLn_18 (coe v0) (coe v2))
      (coe du_error_6 (coe v1) (coe v2))
-- Reflection.Utils.Debug.Debug.printTerm
d_printTerm_34 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_printTerm_34 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () () erased
      erased
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_inferType_346 v2)
      (\ v3 ->
         d_printLns_24
           (coe v0)
           (coe
              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
              (coe
                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v1
                 (": {" :: Data.Text.Text))
              (coe
                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                 (coe MAlonzo.Code.Reflection.AST.Show.d_showTerm_40 (coe v3))
                 (coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe (" \8715 " :: Data.Text.Text))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Reflection.AST.Show.d_showTerm_40 (coe v2))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe ("}\n" :: Data.Text.Text))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
-- Reflection.Utils.Debug.Debug.printContext
d_printContext_42 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_printContext_42 v0 v1
  = coe
      MAlonzo.Code.Class.Monad.Core.du__'62''62'__24
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6) (coe ())
      (coe ())
      (coe d_print_16 (coe v0) (coe ("\t----CTX----" :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Class.Monad.Core.du_void_134
         MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6 ()
         (coe
            MAlonzo.Code.Class.Traversable.Core.du_traverse_44
            (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_92)
            (coe
               MAlonzo.Code.Class.Traversable.Instances.d_TraversableM'45'List_28)
            (coe ()) (coe ())
            (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
            (coe du_go_50 (coe v0))
            (coe MAlonzo.Code.Meta.Prelude.du_enumerate_44 v1)))
-- Reflection.Utils.Debug.Debug._.go
d_go_50 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_go_50 v0 ~v1 v2 = du_go_50 v0 v2
du_go_50 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_go_50 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    d_print_16 (coe v0)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       ("\t#" :: Data.Text.Text)
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                          (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             (" " :: Data.Text.Text)
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v4
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   (" : " :: Data.Text.Text)
                                   (coe
                                      MAlonzo.Code.Class.Show.Core.d_show_16
                                      (coe
                                         MAlonzo.Code.Class.Show.Instances.du_Show'45'Arg_78
                                         (coe
                                            MAlonzo.Code.Class.Show.Core.C_mkShow_18
                                            (coe MAlonzo.Code.Reflection.AST.Show.d_showTerm_40)))
                                      v5))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Debug.Debug.printCurrentContext
d_printCurrentContext_58 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_printCurrentContext_58 v0
  = coe
      MAlonzo.Code.Class.Monad.Core.du__'61''60''60'__32
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6) (coe ())
      (coe ()) (coe d_printContext_42 (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_getContext_376)
-- Reflection.Utils.Debug.Debug.genSimpleDef
d_genSimpleDef_60 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_genSimpleDef_60 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.du__'62''62'__24
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6) (coe ())
      (coe ())
      (coe d_print_16 (coe v0) (coe ("Generaring..." :: Data.Text.Text)))
      (coe
         MAlonzo.Code.Class.Monad.Core.du__'62''62'__24
         (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6) (coe ())
         (coe ())
         (coe
            MAlonzo.Code.Agda.Builtin.Reflection.d_declareDef_392
            (coe
               MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
               (coe
                  MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                  (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                  (coe
                     MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                     (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                     (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
               (coe v1))
            v2)
         (coe
            MAlonzo.Code.Class.Monad.Core.du__'62''62'__24
            (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6) (coe ())
            (coe ())
            (coe
               d_print_16 (coe v0)
               (coe
                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                  ("```\n" :: Data.Text.Text)
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowQName_12 v1)
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        (" : " :: Data.Text.Text)
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (" " :: Data.Text.Text)
                           (MAlonzo.Code.Reflection.AST.Show.d_showTerm_40 (coe v2)))))))
            (coe
               MAlonzo.Code.Class.Monad.Core.du__'62''62'__24
               (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6) (coe ())
               (coe ())
               (coe
                  MAlonzo.Code.Agda.Builtin.Reflection.d_defineFun_404 v1
                  (coe
                     MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                     (coe
                        MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v3))))
               (coe
                  d_print_16 (coe v0)
                  (coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     (coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowQName_12 v1)
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        (" = " :: Data.Text.Text)
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (" " :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (MAlonzo.Code.Reflection.AST.Show.d_showTerm_40 (coe v3))
                              ("\n```" :: Data.Text.Text)))))))))
-- Reflection.Utils.Debug.DebugI._.errorP
d_errorP_74 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_errorP_74 v0 v1 v2 v3
  = coe
      du_errorP_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
         (coe (0 :: Integer)))
      v1 v3
-- Reflection.Utils.Debug.DebugI._.genSimpleDef
d_genSimpleDef_76 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_genSimpleDef_76 v0
  = coe
      d_genSimpleDef_60
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
         (coe (0 :: Integer)))
-- Reflection.Utils.Debug.DebugI._.print
d_print_78 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_print_78 v0
  = coe
      d_print_16
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
         (coe (0 :: Integer)))
-- Reflection.Utils.Debug.DebugI._.printContext
d_printContext_80 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_printContext_80 v0
  = coe
      d_printContext_42
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
         (coe (0 :: Integer)))
-- Reflection.Utils.Debug.DebugI._.printCurrentContext
d_printCurrentContext_82 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_printCurrentContext_82 v0
  = coe
      d_printCurrentContext_58
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
         (coe (0 :: Integer)))
-- Reflection.Utils.Debug.DebugI._.printLn
d_printLn_84 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_printLn_84 v0
  = coe
      d_printLn_18
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
         (coe (0 :: Integer)))
-- Reflection.Utils.Debug.DebugI._.printLns
d_printLns_86 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> AgdaAny
d_printLns_86 v0
  = coe
      d_printLns_24
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
         (coe (0 :: Integer)))
-- Reflection.Utils.Debug.DebugI._.printS
d_printS_88 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Class.Show.Core.T_Show_10 -> AgdaAny -> AgdaAny
d_printS_88 v0 v1 v2 v3 v4
  = coe
      du_printS_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
         (coe (0 :: Integer)))
      v3 v4
-- Reflection.Utils.Debug.DebugI._.printTerm
d_printTerm_90 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_printTerm_90 v0
  = coe
      d_printTerm_34
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
         (coe (0 :: Integer)))
-- Reflection.Utils.Debug.trace
d_trace_96 ::
  () ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_trace_96 ~v0 v1 v2 v3 v4 = du_trace_96 v1 v2 v3 v4
du_trace_96 ::
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_trace_96 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.du__'62''62'__24
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6) (coe ())
      (coe ())
      (coe
         d_print_16
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe ("trace" :: Data.Text.Text)) (coe (100 :: Integer)))
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("trace: " :: Data.Text.Text)
            (coe MAlonzo.Code.Class.Show.Core.d_show_16 v0 v1)))
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_unify_338 v3 v2)
-- Reflection.Utils.Debug._._.errorP
d_errorP_110 ::
  () ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_errorP_110 ~v0 ~v1 ~v2 ~v3 ~v4 = du_errorP_110
du_errorP_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
du_errorP_110 v0 v1 v2
  = coe
      du_errorP_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe ("trace" :: Data.Text.Text)) (coe (100 :: Integer)))
      v0 v2
-- Reflection.Utils.Debug._._.genSimpleDef
d_genSimpleDef_112 ::
  () ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_genSimpleDef_112 ~v0 ~v1 ~v2 ~v3 ~v4 = du_genSimpleDef_112
du_genSimpleDef_112 ::
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_genSimpleDef_112
  = coe
      d_genSimpleDef_60
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe ("trace" :: Data.Text.Text)) (coe (100 :: Integer)))
-- Reflection.Utils.Debug._._.print
d_print_114 ::
  () ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_print_114 ~v0 ~v1 ~v2 ~v3 ~v4 = du_print_114
du_print_114 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
du_print_114
  = coe
      d_print_16
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe ("trace" :: Data.Text.Text)) (coe (100 :: Integer)))
-- Reflection.Utils.Debug._._.printContext
d_printContext_116 ::
  () ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_printContext_116 ~v0 ~v1 ~v2 ~v3 ~v4 = du_printContext_116
du_printContext_116 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
du_printContext_116
  = coe
      d_printContext_42
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe ("trace" :: Data.Text.Text)) (coe (100 :: Integer)))
-- Reflection.Utils.Debug._._.printCurrentContext
d_printCurrentContext_118 ::
  () ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_printCurrentContext_118 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_printCurrentContext_118
du_printCurrentContext_118 :: AgdaAny
du_printCurrentContext_118
  = coe
      d_printCurrentContext_58
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe ("trace" :: Data.Text.Text)) (coe (100 :: Integer)))
-- Reflection.Utils.Debug._._.printLn
d_printLn_120 ::
  () ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_printLn_120 ~v0 ~v1 ~v2 ~v3 ~v4 = du_printLn_120
du_printLn_120 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
du_printLn_120
  = coe
      d_printLn_18
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe ("trace" :: Data.Text.Text)) (coe (100 :: Integer)))
-- Reflection.Utils.Debug._._.printLns
d_printLns_122 ::
  () ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> AgdaAny
d_printLns_122 ~v0 ~v1 ~v2 ~v3 ~v4 = du_printLns_122
du_printLns_122 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> AgdaAny
du_printLns_122
  = coe
      d_printLns_24
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe ("trace" :: Data.Text.Text)) (coe (100 :: Integer)))
-- Reflection.Utils.Debug._._.printS
d_printS_124 ::
  () ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Class.Show.Core.T_Show_10 -> AgdaAny -> AgdaAny
d_printS_124 ~v0 ~v1 ~v2 ~v3 ~v4 = du_printS_124
du_printS_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Class.Show.Core.T_Show_10 -> AgdaAny -> AgdaAny
du_printS_124 v0 v1 v2 v3
  = coe
      du_printS_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe ("trace" :: Data.Text.Text)) (coe (100 :: Integer)))
      v2 v3
-- Reflection.Utils.Debug._._.printTerm
d_printTerm_126 ::
  () ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_printTerm_126 ~v0 ~v1 ~v2 ~v3 ~v4 = du_printTerm_126
du_printTerm_126 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_printTerm_126
  = coe
      d_printTerm_34
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe ("trace" :: Data.Text.Text)) (coe (100 :: Integer)))
