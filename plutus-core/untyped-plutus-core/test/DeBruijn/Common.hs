{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}
module DeBruijn.Common where

import Data.Semigroup
import PlutusCore.MkPlc
import UntypedPlutusCore as UPLC

timesT :: Index -> (a -> a)  -> a -> a
timesT n = appEndo . stimes n . Endo

-- a big debruijn index for testing.
-- the actual number does not matter, as long as it is sufficiently large to not interfere with the rest of the test code.
ix99 :: DeBruijn
ix99 = DeBruijn 999999

-- An out-of-scope variable in these tests.
outVar :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
outVar = Var () ix99

true :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
true = mkConstant @Bool () True

-- A helper that just places index 0 to the binder (the only "reasonable" index for the binders)
lamAbs0 :: (t ~ UPLC.Term DeBruijn DefaultUni DefaultFun ()) => t -> t
lamAbs0 = LamAbs () (DeBruijn 0)

-- A helper that constructs a lamabs with the binder having a nonsensical index.
-- See NOTE: [DeBruijn indices of Binders]
lamAbs99 :: (t ~ UPLC.Term DeBruijn DefaultUni DefaultFun ()) => t -> t
lamAbs99 = LamAbs () ix99

constFun :: UPLC.Term DeBruijn DefaultUni DefaultFun ()
constFun = lamAbs0 $ lamAbs0 $ Var () $ DeBruijn 2

delayforce :: (t ~ UPLC.Term DeBruijn DefaultUni DefaultFun ()) => t -> t
delayforce t = Delay () $ Force () t
