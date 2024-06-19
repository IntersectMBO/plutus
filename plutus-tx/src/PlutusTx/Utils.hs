{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}
module PlutusTx.Utils where

-- We do not use qualified import because the whole module contains off-chain code
import PlutusTx.Builtins.Internal qualified as BI
import Prelude as Haskell

mustBeReplaced :: String -> a
mustBeReplaced placeholder =
  error $
    "The " <> show placeholder <> " placeholder must have been replaced by the \
      \core-to-plc plugin during compilation."

-- | Delay evalaution of the expression inside the 'Delay' constructor.
data Delay a = Delay ~(forall b. a)

-- | Force the evaluation of the expression delayed by the 'Delay'.
force :: Delay a -> a
-- We can use any type here, but the type instantiation will keep the
-- type alive, so best to use a builtin type to avoid keeping other stuff
-- needlessly live.
force (Delay a) = a @BI.BuiltinUnit

{- Note [The Delay type]
Occasionally we need to explicitly delay evaluation of an expression, since PLC
is strict. Ideally, this would eventually translate into the underlying 'delay'
and 'force' constructors of UPLC, as this is the fastest way to do it.

Our typed intermediate languages do not have 'delay' and 'force', however.
What they do have is type abstractions and type instantiations, which get
compiled into 'delay' and 'force', respectively. So what we want is something
which will create a (needless) type abstraction/type instantiation.

This is what 'Delay' does: the constructor accepts a 'forall' type, so the
expression inside the constructor application should be a type abstraction;
and 'force' just instantiates this to an arbitrary type, in this case
'BuiltinUnit'.
-}
