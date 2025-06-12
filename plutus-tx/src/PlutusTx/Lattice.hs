{-# LANGUAGE ConstraintKinds #-}

module PlutusTx.Lattice where

import PlutusTx.Bool
import PlutusTx.Monoid
import PlutusTx.Semigroup

{-| A join semi-lattice, i.e. a partially ordered set equipped with a
binary operation '(\/)'.

Note that the mathematical definition would require an ordering constraint -
we omit that so we can define instances for e.g. '(->)'.
-}
class JoinSemiLattice a where
  (\/) :: a -> a -> a

{-| A meet semi-lattice, i.e. a partially ordered set equipped with a
binary operation '(/\)'.

Note that the mathematical definition would require an ordering constraint -
we omit that so we can define instances for e.g. '(->)'.
-}
class MeetSemiLattice a where
  (/\) :: a -> a -> a

-- | A lattice.
type Lattice a = (JoinSemiLattice a, MeetSemiLattice a)

{-| A bounded join semi-lattice, i.e. a join semi-lattice augmented with
a distinguished element 'bottom' which is the unit of '(\/)'.
-}
class (JoinSemiLattice a) => BoundedJoinSemiLattice a where
  bottom :: a

{-| A bounded meet semi-lattice, i.e. a meet semi-lattice augmented with
a distinguished element 'top' which is the unit of '(/\)'.
-}
class (MeetSemiLattice a) => BoundedMeetSemiLattice a where
  top :: a

-- | A bounded lattice.
type BoundedLattice a = (BoundedJoinSemiLattice a, BoundedMeetSemiLattice a)

-- Wrappers

-- | A wrapper witnessing that a join semi-lattice is a monoid with '(\/)' and 'bottom'.
newtype Join a = Join a

instance (JoinSemiLattice a) => Semigroup (Join a) where
  Join l <> Join r = Join (l \/ r)

instance (BoundedJoinSemiLattice a) => Monoid (Join a) where
  mempty = Join bottom

-- | A wrapper witnessing that a meet semi-lattice is a monoid with '(/\)' and 'top'.
newtype Meet a = Meet a

instance (MeetSemiLattice a) => Semigroup (Meet a) where
  Meet l <> Meet r = Meet (l /\ r)

instance (BoundedMeetSemiLattice a) => Monoid (Meet a) where
  mempty = Meet top

-- Instances

instance JoinSemiLattice Bool where
  {-# INLINEABLE (\/) #-}
  (\/) = (||)

instance BoundedJoinSemiLattice Bool where
  {-# INLINEABLE bottom #-}
  bottom = False

instance MeetSemiLattice Bool where
  {-# INLINEABLE (/\) #-}
  (/\) = (&&)

instance BoundedMeetSemiLattice Bool where
  {-# INLINEABLE top #-}
  top = True

instance (JoinSemiLattice a, JoinSemiLattice b) => JoinSemiLattice (a, b) where
  {-# INLINEABLE (\/) #-}
  (a1, b1) \/ (a2, b2) = (a1 \/ a2, b1 \/ b2)

instance (BoundedJoinSemiLattice a, BoundedJoinSemiLattice b) => BoundedJoinSemiLattice (a, b) where
  {-# INLINEABLE bottom #-}
  bottom = (bottom, bottom)

instance (MeetSemiLattice a, MeetSemiLattice b) => MeetSemiLattice (a, b) where
  {-# INLINEABLE (/\) #-}
  (a1, b1) /\ (a2, b2) = (a1 /\ a2, b1 /\ b2)

instance (BoundedMeetSemiLattice a, BoundedMeetSemiLattice b) => BoundedMeetSemiLattice (a, b) where
  {-# INLINEABLE top #-}
  top = (top, top)

instance (JoinSemiLattice b) => JoinSemiLattice (a -> b) where
  {-# INLINEABLE (\/) #-}
  (f \/ g) a = f a \/ g a

instance (BoundedJoinSemiLattice b) => BoundedJoinSemiLattice (a -> b) where
  {-# INLINEABLE bottom #-}
  bottom _ = bottom

instance (MeetSemiLattice b) => MeetSemiLattice (a -> b) where
  {-# INLINEABLE (/\) #-}
  (f /\ g) a = f a /\ g a

instance (BoundedMeetSemiLattice b) => BoundedMeetSemiLattice (a -> b) where
  {-# INLINEABLE top #-}
  top _ = top
