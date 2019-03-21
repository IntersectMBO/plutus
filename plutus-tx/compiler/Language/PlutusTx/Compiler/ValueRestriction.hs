{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}

-- | Functions for dealing with the Plutus Core value restriction.
module Language.PlutusTx.Compiler.ValueRestriction where

import           Language.PlutusTx.Compiler.Error
import           Language.PlutusTx.Compiler.Laziness
import           Language.PlutusTx.Compiler.Types
import           Language.PlutusTx.PIRTypes

import qualified Language.PlutusIR                   as PIR
import qualified Language.PlutusIR.Value             as PIR

import           Control.Monad.Reader

-- Value restriction

{- Note [Value restriction]
Plutus Core has the traditional *value restriction* on type abstractions - namely, the
body of a type abstraction must be a value.

This causes problems for us because *Haskell* has no such thing. (There is the monomorphism
restriciton, which is similar, but not as restrictive, so it doesn't help us.)

There are two approaches to solving this problem. Currently we use "passing on the value restriction",
but I include a description of mangling to illustrate why the current solution is preferable.

-- Mangling

We can get around this by delaying the body of all our abstractions, thus making them lambdas, which are values.
This then means that we need to change the *types* of all foralls to include the unit argument,
and all instantiations to force the value.

We need to do this everywhere so that the translation of the users' program remains
well-typed. Consider

runST :: (forall s. ST s a) -> a

myCalc :: Int
myCalc = runST $ pure 1

Converting `pure 1`, we would normally turn it into something of type

(all s (type) [ST s Int])

After mangling, this becomes

(all s (type) (fun unit [ST s Int]))

This means we had better convert `runST` into something that expects things of that type instead of
the original type! And we need to add forces to the instantiations inside `runST` otherwise its
body won't be well-typed too.

Note that it's no good to convert some other abstraction where the body is already a value without the delay -
if we did that, then `runST` would be in an impossible place, since it would need to take
either mangled or non-mangled abstractions. The only way we can get away with this without doing complicated
accounting is to do it uniformly: i.e. absolutely everywhere whether we need it in that
case or not.

We need to do this even for the abstractions in our generated matchers for Scott-encoding,
because constructors are user-visible and so can be passed to functions, which might expect them to be
mangled.

-- Passing on the value restriction

An alternative approach would be to pass on the value restriction to the client Haskell code.
This has the advantage of much simpler codegen. However, it has a few annoying cases:

- We can't provide `error :: forall a. a` any more.
- We can't handle `void# :: forall a. a` well any more.

The first is easy: we just make the primitive be mangled `error :: forall a. () -> a`.

The second is a pain. GHC *does* use the polymorphic void. So we take the ad-hoc
expedient of mangling *just* the 'Void#' type. Since nothing can use this "for real",
there are no uses to go wrong so long as we change the type uniformly. This is a
bit of a hack, though.
-}

-- See Note [Value restriction]
mangleTyForall :: Converting m => PIRType -> m PIRType
mangleTyForall = \case
    PIR.TyForall a t k body -> PIR.TyForall a t k <$> delayType body
    x -> pure x

-- See Note [Value restriction]
mangleTyAbs :: Converting m => PIRTerm -> m PIRTerm
mangleTyAbs = \case
    PIR.TyAbs a t k body -> PIR.TyAbs a t k <$> delay body
    x -> pure x

checkTyAbsBody :: Converting m => PIRTerm -> m ()
checkTyAbsBody t = do
    ConvertingContext {ccOpts=opts} <- ask
    -- we sometimes need to turn this off, as checking for term values also checks for normalized types at the moment
    unless (not (coCheckValueRestriction opts) || PIR.isTermValue t) $ throwPlain ValueRestrictionError
