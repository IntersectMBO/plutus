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

module MAlonzo.Code.Relation.Binary.Consequences where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Bool qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Empty qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Relation.Binary.Definitions qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Relation.Nullary.Reflects qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Consequences._.subst⇒respˡ
d_subst'8658'resp'737'_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_subst'8658'resp'737'_38 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
                          v11
  = du_subst'8658'resp'737'_38 v5 v6 v7 v8 v9 v10 v11
du_subst'8658'resp'737'_38 ::
  (AgdaAny -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_subst'8658'resp'737'_38 v0 v1 v2 v3 v4 v5 v6
  = coe v1 (\ v7 -> coe v0 v7 v2) v3 v4 v5 v6
-- Relation.Binary.Consequences._.subst⇒respʳ
d_subst'8658'resp'691'_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_subst'8658'resp'691'_48 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
                          v11
  = du_subst'8658'resp'691'_48 v5 v6 v7 v8 v9 v10 v11
du_subst'8658'resp'691'_48 ::
  (AgdaAny -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_subst'8658'resp'691'_48 v0 v1 v2 v3 v4 v5 v6
  = coe v1 (coe v0 v2) v3 v4 v5 v6
-- Relation.Binary.Consequences._.subst⇒resp₂
d_subst'8658'resp'8322'_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_subst'8658'resp'8322'_58 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_subst'8658'resp'8322'_58 v6
du_subst'8658'resp'8322'_58 ::
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_subst'8658'resp'8322'_58 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_subst'8658'resp'691'_48 erased (coe v0))
      (coe du_subst'8658'resp'737'_38 erased (coe v0))
-- Relation.Binary.Consequences._.resp⇒¬-resp
d_resp'8658''172''45'resp_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_resp'8658''172''45'resp_76 = erased
-- Relation.Binary.Consequences._.sym⇒¬-sym
d_sym'8658''172''45'sym_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_sym'8658''172''45'sym_98 = erased
-- Relation.Binary.Consequences._.cotrans⇒¬-trans
d_cotrans'8658''172''45'trans_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_cotrans'8658''172''45'trans_106 = erased
-- Relation.Binary.Consequences._.irrefl⇒¬-refl
d_irrefl'8658''172''45'refl_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl'8658''172''45'refl_132 = erased
-- Relation.Binary.Consequences._.total⇒refl
d_total'8658'refl_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_total'8658'refl_152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_total'8658'refl_152 v6 v7 v8 v9 v10 v11
du_total'8658'refl_152 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_total'8658'refl_152 v0 v1 v2 v3 v4 v5
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> let v8 = coe v2 v3 v4 in
           coe
             (case coe v8 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> coe v9
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                  -> coe v6 v3 v3 v4 v5 (coe v7 v3 v4 v3 (coe v1 v3 v4 v5) v9)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Consequences._.total∧dec⇒dec
d_total'8743'dec'8658'dec_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_total'8743'dec'8658'dec_204 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
                              v10 v11
  = du_total'8743'dec'8658'dec_204 v6 v7 v8 v9 v10 v11
du_total'8743'dec'8658'dec_204 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_total'8743'dec'8658'dec_204 v0 v1 v2 v3 v4 v5
  = let v6 = coe v2 v4 v5 in
    coe
      (case coe v6 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 (coe v7))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                (coe v0 v4 v5) (coe (\ v8 -> coe v1 v4 v5 v8 v7)) (coe v3 v4 v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Relation.Binary.Consequences._.mono⇒cong
d_mono'8658'cong_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mono'8658'cong_276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 v12 v13 v14 v15 v16 v17 v18 v19
  = du_mono'8658'cong_276 v12 v13 v14 v15 v16 v17 v18 v19
du_mono'8658'cong_276 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_mono'8658'cong_276 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      v2
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292 v3
         (\ v8 v9 -> v8) v5 v6)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v8 v9 -> v9) v3 v5 v6)
      (coe v4 v5 v6 (coe v1 v5 v6 v7))
      (coe v4 v6 v5 (coe v1 v6 v5 (coe v0 v5 v6 v7)))
-- Relation.Binary.Consequences._.antimono⇒cong
d_antimono'8658'cong_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antimono'8658'cong_290 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 v12 v13 v14 v15 v16 v17 v18 v19
  = du_antimono'8658'cong_290 v12 v13 v14 v15 v16 v17 v18 v19
du_antimono'8658'cong_290 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antimono'8658'cong_290 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      v2
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v8 v9 -> v9) v3 v6 v5)
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292 v3
         (\ v8 v9 -> v8) v6 v5)
      (coe v4 v6 v5 (coe v1 v6 v5 (coe v0 v5 v6 v7)))
      (coe v4 v5 v6 (coe v1 v5 v6 v7))
-- Relation.Binary.Consequences._.mono₂⇒cong₂
d_mono'8322''8658'cong'8322'_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mono'8322''8658'cong'8322'_304 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10 ~v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22
  = du_mono'8322''8658'cong'8322'_304
      v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22
du_mono'8322''8658'cong'8322'_304 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_mono'8322''8658'cong'8322'_304 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      v2 (coe v3 v5 v7) (coe v3 v6 v8)
      (coe v4 v5 v6 v7 v8 (coe v1 v5 v6 v9) (coe v1 v7 v8 v10))
      (coe
         v4 v6 v5 v8 v7 (coe v1 v6 v5 (coe v0 v5 v6 v9))
         (coe v1 v8 v7 (coe v0 v7 v8 v10)))
-- Relation.Binary.Consequences._.trans∧irr⇒asym
d_trans'8743'irr'8658'asym_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_trans'8743'irr'8658'asym_332 = erased
-- Relation.Binary.Consequences._.irr∧antisym⇒asym
d_irr'8743'antisym'8658'asym_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irr'8743'antisym'8658'asym_344 = erased
-- Relation.Binary.Consequences._.asym⇒antisym
d_asym'8658'antisym_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_asym'8658'antisym_354 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10
  = du_asym'8658'antisym_354
du_asym'8658'antisym_354 :: AgdaAny
du_asym'8658'antisym_354
  = coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_14
-- Relation.Binary.Consequences._.asym⇒irr
d_asym'8658'irr_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym'8658'irr_362 = erased
-- Relation.Binary.Consequences._.tri⇒asym
d_tri'8658'asym_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_tri'8658'asym_380 = erased
-- Relation.Binary.Consequences._.tri⇒irr
d_tri'8658'irr_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_tri'8658'irr_432 = erased
-- Relation.Binary.Consequences._.tri⇒dec≈
d_tri'8658'dec'8776'_492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_tri'8658'dec'8776'_492 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_tri'8658'dec'8776'_492 v6 v7 v8
du_tri'8658'dec'8776'_492 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_tri'8658'dec'8776'_492 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v4
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v5
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 (coe v5))
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v6
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Relation.Binary.Consequences._.tri⇒dec<
d_tri'8658'dec'60'_528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_tri'8658'dec'60'_528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_tri'8658'dec'60'_528 v6 v7 v8
du_tri'8658'dec'60'_528 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_tri'8658'dec'60'_528 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v4
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 (coe v4))
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v5
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v6
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Relation.Binary.Consequences._.trans∧tri⇒respʳ
d_trans'8743'tri'8658'resp'691'_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans'8743'tri'8658'resp'691'_564 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 v9 v10 ~v11 v12 ~v13 ~v14
  = du_trans'8743'tri'8658'resp'691'_564 v9 v10 v12
du_trans'8743'tri'8658'resp'691'_564 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_trans'8743'tri'8658'resp'691'_564 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v4 -> coe v4
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v5
           -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_14
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v6
           -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_14
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Relation.Binary.Consequences._.trans∧tri⇒respˡ
d_trans'8743'tri'8658'resp'737'_648 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans'8743'tri'8658'resp'737'_648 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8 v9 ~v10 v11 ~v12 ~v13
  = du_trans'8743'tri'8658'resp'737'_648 v8 v9 v11
du_trans'8743'tri'8658'resp'737'_648 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_trans'8743'tri'8658'resp'737'_648 v0 v1 v2
  = let v3 = coe v0 v2 v1 in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v4 -> coe v4
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v5
           -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_14
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v6
           -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_14
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Relation.Binary.Consequences._.trans∧tri⇒resp
d_trans'8743'tri'8658'resp_716 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_trans'8743'tri'8658'resp_716 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               v9
  = du_trans'8743'tri'8658'resp_716 v9
du_trans'8743'tri'8658'resp_716 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_trans'8743'tri'8658'resp_716 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v1 v2 v3 v4 v5 ->
         coe du_trans'8743'tri'8658'resp'691'_564 (coe v0) v1 v3)
      (\ v1 v2 v3 v4 v5 ->
         coe du_trans'8743'tri'8658'resp'737'_648 (coe v0) v1 v3)
-- Relation.Binary.Consequences._.wlog
d_wlog_748 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_wlog_748 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10
  = du_wlog_748 v6 v7 v8 v9 v10
du_wlog_748 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_wlog_748 v0 v1 v2 v3 v4
  = let v5 = coe v0 v3 v4 in
    coe
      (case coe v5 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6 -> coe v2 v3 v4 v6
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
           -> coe v1 v4 v3 (coe v2 v4 v3 v6)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Relation.Binary.Consequences._.dec⇒weaklyDec
d_dec'8658'weaklyDec_800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> Maybe AgdaAny
d_dec'8658'weaklyDec_800 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_dec'8658'weaklyDec_800 v6 v7 v8
du_dec'8658'weaklyDec_800 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> Maybe AgdaAny
du_dec'8658'weaklyDec_800 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_dec'8658'maybe_106
      (coe v0 v1 v2)
-- Relation.Binary.Consequences._.dec⇒recomputable
d_dec'8658'recomputable_808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_dec'8658'recomputable_808 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_dec'8658'recomputable_808 v6 v7 v8
du_dec'8658'recomputable_808 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_dec'8658'recomputable_808 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_recompute_54
      (coe v0 v1 v2)
-- Relation.Binary.Consequences._.map-NonEmpty
d_map'45'NonEmpty_832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Definitions.T_NonEmpty_440 ->
  MAlonzo.Code.Relation.Binary.Definitions.T_NonEmpty_440
d_map'45'NonEmpty_832 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_map'45'NonEmpty_832 v8 v9
du_map'45'NonEmpty_832 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Definitions.T_NonEmpty_440 ->
  MAlonzo.Code.Relation.Binary.Definitions.T_NonEmpty_440
du_map'45'NonEmpty_832 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Definitions.C_nonEmpty_460
      (coe MAlonzo.Code.Relation.Binary.Definitions.d_x_454 (coe v1))
      (coe MAlonzo.Code.Relation.Binary.Definitions.d_y_456 (coe v1))
      (coe
         v0 (MAlonzo.Code.Relation.Binary.Definitions.d_x_454 (coe v1))
         (MAlonzo.Code.Relation.Binary.Definitions.d_y_456 (coe v1))
         (MAlonzo.Code.Relation.Binary.Definitions.d_proof_458 (coe v1)))
-- Relation.Binary.Consequences._.flip-Connex
d_flip'45'Connex_854 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_flip'45'Connex_854 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_flip'45'Connex_854 v8 v9 v10
du_flip'45'Connex_854 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_flip'45'Connex_854 v0 v1 v2
  = coe MAlonzo.Code.Data.Sum.Base.du_swap_78 (coe v0 v2 v1)
-- Relation.Binary.Consequences.subst⟶respˡ
d_subst'10230'resp'737'_862 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_subst'10230'resp'737'_862 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe du_subst'8658'resp'737'_38 v5 v6 v7 v8 v9 v10 v11
-- Relation.Binary.Consequences.subst⟶respʳ
d_subst'10230'resp'691'_864 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_subst'10230'resp'691'_864 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe du_subst'8658'resp'691'_48 v5 v6 v7 v8 v9 v10 v11
-- Relation.Binary.Consequences.subst⟶resp₂
d_subst'10230'resp'8322'_866 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_subst'10230'resp'8322'_866 v0 v1 v2 v3 v4 v5 v6
  = coe du_subst'8658'resp'8322'_58 v6
-- Relation.Binary.Consequences.P-resp⟶¬P-resp
d_P'45'resp'10230''172'P'45'resp_868 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_P'45'resp'10230''172'P'45'resp_868 = erased
-- Relation.Binary.Consequences.total⟶refl
d_total'10230'refl_870 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_total'10230'refl_870 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe du_total'8658'refl_152 v6 v7 v8 v9 v10 v11
-- Relation.Binary.Consequences.total+dec⟶dec
d_total'43'dec'10230'dec_872 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_total'43'dec'10230'dec_872 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe du_total'8743'dec'8658'dec_204 v6 v7 v8 v9 v10 v11
-- Relation.Binary.Consequences.trans∧irr⟶asym
d_trans'8743'irr'10230'asym_874 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_trans'8743'irr'10230'asym_874 = erased
-- Relation.Binary.Consequences.irr∧antisym⟶asym
d_irr'8743'antisym'10230'asym_876 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irr'8743'antisym'10230'asym_876 = erased
-- Relation.Binary.Consequences.asym⟶antisym
d_asym'10230'antisym_878 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_asym'10230'antisym_878 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe du_asym'8658'antisym_354
-- Relation.Binary.Consequences.asym⟶irr
d_asym'10230'irr_880 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym'10230'irr_880 = erased
-- Relation.Binary.Consequences.tri⟶asym
d_tri'10230'asym_882 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_tri'10230'asym_882 = erased
-- Relation.Binary.Consequences.tri⟶irr
d_tri'10230'irr_884 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_tri'10230'irr_884 = erased
-- Relation.Binary.Consequences.tri⟶dec≈
d_tri'10230'dec'8776'_886 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_tri'10230'dec'8776'_886 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe du_tri'8658'dec'8776'_492 v6 v7 v8
-- Relation.Binary.Consequences.tri⟶dec<
d_tri'10230'dec'60'_888 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_tri'10230'dec'60'_888 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe du_tri'8658'dec'60'_528 v6 v7 v8
-- Relation.Binary.Consequences.trans∧tri⟶respʳ≈
d_trans'8743'tri'10230'resp'691''8776'_890 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans'8743'tri'10230'resp'691''8776'_890 v0 v1 v2 v3 v4 v5 v6 v7
                                           v8 v9 v10 v11 v12 v13 v14
  = coe du_trans'8743'tri'8658'resp'691'_564 v9 v10 v12
-- Relation.Binary.Consequences.trans∧tri⟶respˡ≈
d_trans'8743'tri'10230'resp'737''8776'_892 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans'8743'tri'10230'resp'737''8776'_892 v0 v1 v2 v3 v4 v5 v6 v7
                                           v8 v9 v10 v11 v12 v13
  = coe du_trans'8743'tri'8658'resp'737'_648 v8 v9 v11
-- Relation.Binary.Consequences.trans∧tri⟶resp≈
d_trans'8743'tri'10230'resp'8776'_894 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_trans'8743'tri'10230'resp'8776'_894 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe du_trans'8743'tri'8658'resp_716 v9
-- Relation.Binary.Consequences.dec⟶weaklyDec
d_dec'10230'weaklyDec_896 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> Maybe AgdaAny
d_dec'10230'weaklyDec_896 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe du_dec'8658'weaklyDec_800 v6 v7 v8
-- Relation.Binary.Consequences.dec⟶recomputable
d_dec'10230'recomputable_898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_dec'10230'recomputable_898 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe du_dec'8658'recomputable_808 v6 v7 v8
