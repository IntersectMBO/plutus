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

module MAlonzo.Code.Reflection.Syntax where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Reflection.Syntax.PatTelescope
d_PatTelescope_262 :: ()
d_PatTelescope_262 = erased
-- Reflection.Syntax.Context
d_Context_264 :: ()
d_Context_264 = erased
-- Reflection.Syntax.TTerm
d_TTerm_266 :: ()
d_TTerm_266 = erased
-- Reflection.Syntax.Hole
d_Hole_268 :: ()
d_Hole_268 = erased
-- Reflection.Syntax.THole
d_THole_270 :: ()
d_THole_270 = erased
