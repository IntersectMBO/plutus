{-# LANGUAGE LambdaCase #-}
module UntypedPlutusCore.Transform.ForceDelay
    ( forceDelayCancel
    ) where

import UntypedPlutusCore.Core

import Control.Lens (transformOf)

forceDelayCancel :: Term name uni fun a -> Term name uni fun a
forceDelayCancel = transformOf termSubterms processTerm

processTerm :: Term name uni fun a -> Term name uni fun a
processTerm = \case
    Force _ (Delay _ t)          -> t
    -- TODO: flag to turn this off, see
    -- Note [Removing delays makes more programs succeed]
    Delay _ t | canRemoveDelay t -> t
    Force _ t | canRemoveForce t -> t
    t                            -> t

{- Note [Removing redundant delays and forces]

We do a few transformations here. The simplest and best is to cancel out
a force/delay pair. This is a pure win, since it's exactly what the machine
would do.

The next thing we try and do is to get rid of force/delays that are independently
pointless. In particular
- delaying something that does no work does nothing
- forcing something that cannot be a delay does nothing

So we can remove them in those cases.

However, there are a few wrinkles. The first is that we don't want this to
cannibalize our opportunities to do force/delay pair cancellations. Consider:

let x = delay (\y . t)
in force x
---> (remove delay)
let x = \y . t
in force x
---> (inline)
force (\y . t)

In this case it's fine because the term _inside_ the delay was something
that we can remove the force from around (a lambda). But we need to be
careful that this is always the case. So we require that the set of terms
that we remove delays from around be a _subset_ of the set of terms that
we remove forces from around.

The case where this is strange is delay itself. Consider:

let x = delay (delay [f z])
in force (force x)
---> (remove delay)
let x = delay [f z]
in force (force x)
---> (inline)
force (force (delay [f z]))
---> (force/delay cancel)
force [f z]

We now can't remove the last force, whereas if we had just
inlined the first thing we could have removed both by
repeated force/delay cancellation.

So although it seems like it _should_ be fine to remove a delay
from around a delay, we don't do this for the above reason.
In practice this doesn't matter much.
-}

{- Note [Removing delays makes more programs succeed]

Note that removing redundant delays doesn't quite preserve the
semantics of the program! It can make some programs that would
otherwise fail succeed instead, e.g.

let f = delay (\y. t)
in f x

This would fail with the delay (can't apply a delay!) but will
succeed if we take it out. That makes this transformation ever
so slightly questionable, and so we should provide a flag to turn
it off.
-}

-- | Can we remove a 'delay' from around this term?
--
-- Broadly, this means anything that's a value, but
-- also this must be a subset of 'canRemoveForce', see
-- Note [Removing redundant delays and forces] for why.
canRemoveDelay :: Term name uni fun a -> Bool
canRemoveDelay = \case
  LamAbs{}   -> True
  Constant{} -> True
  -- You would expect this to be true, since it's a
  -- value, but that would violate the subset condition.
  Delay{}    -> False
  _          -> False

-- | Can we remove a 'force' from around this term?
--
-- Broadly, this means anything that we know can't turn
-- out to be a 'delay' (which would need the 'force').
canRemoveForce :: Term name uni fun a -> Bool
canRemoveForce = \case
  -- Delay is delay
  Delay{}    -> False

  -- Everything that computes could turn into delay

  -- A variable might be delay, we don't know
  Var{}      -> False
  -- An application might compute to anything, including delay
  Apply{}    -> False
  -- A force will compute to whatever's inside it,
  -- which could be a delay
  Force{}    -> False
  -- Builtins can't be delay, but they can require forcing
  Builtin{}  -> False

  -- Everything else can't be delay
  Constant{} -> True
  LamAbs{}   -> True
  Error{}    -> True
