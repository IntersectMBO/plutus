{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use const" #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:conservative-optimisation #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

{-| Separate module with GHC optimisation flags disabled, matching the flags
used by Philip DiSarro in PR #7562 (ValidatorOptimized.hs). This ensures
that INLINE pragmas behave as intended and builtinAnd gets inlined at the
call site before the plugin compiles, preserving short-circuit semantics. -}
module Budget.BuiltinAndLib where

import PlutusTx.Bool (Bool (..))
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Integer (Integer)
import PlutusTx.Ord ((<))

{-# INLINE builtinIf #-}
builtinIf :: Bool -> (BI.BuiltinUnit -> a) -> (BI.BuiltinUnit -> a) -> a
builtinIf cond t f = BI.ifThenElse cond t f BI.unitval

{-# INLINE builtinAnd #-}
builtinAnd :: Bool -> Bool -> Bool
builtinAnd b1 b2 = builtinIf b1 (\_ -> b2) (\_ -> False)

{-# INLINE andBuiltinAndPattern #-}
andBuiltinAndPattern :: Integer -> Integer -> Integer -> Bool
andBuiltinAndPattern x y z =
  builtinAnd (x < 100) (builtinAnd (y < 100) (z < 100))

{-# INLINE andDirectIfThenElsePattern #-}
andDirectIfThenElsePattern :: Integer -> Integer -> Integer -> Bool
andDirectIfThenElsePattern x y z =
  BI.ifThenElse
    (x < 100)
    ( \_ ->
        BI.ifThenElse
          (y < 100)
          (\_ -> z < 100)
          (\_ -> False)
          BI.unitval
    )
    (\_ -> False)
    BI.unitval
