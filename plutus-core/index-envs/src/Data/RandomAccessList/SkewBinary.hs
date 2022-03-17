{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE ViewPatterns    #-}
module Data.RandomAccessList.SkewBinary
    ( RAList(Cons,Nil)
    , CekValue(..)
    , CekValEnv
    , safeIndexZero
    , unsafeIndexZero
    , safeIndexOne
    , unsafeIndexOne
    , Data.RandomAccessList.SkewBinary.null
    , Data.RandomAccessList.SkewBinary.head
    , Data.RandomAccessList.SkewBinary.tail
    , uncons
    , cons
    ) where

import Data.Bits (unsafeShiftR)
import Data.Maybe
import Data.Word


import UntypedPlutusCore.Core
import Universe

import PlutusCore.Builtin
import PlutusCore.DeBruijn




-- | βA complete binary tree.
-- Note: the size of the tree is not stored/cached,
-- unless it appears as a root tree in 'RAList', which the size is stored inside the Cons.
data Tree uni fun = Leaf (CekValue uni fun)
                  | Node (CekValue uni fun) !(Tree uni fun) !(Tree uni fun)

-- | A strict list of complete binary trees accompanied by their size.
-- The trees appear in >=-size order.
-- Note: this list is strict in its spine, unlike the Prelude list
data RAList uni fun = BHead
               {-# UNPACK #-} !Word64 -- ^ the size of the head tree
               !(Tree uni fun) -- ^ the head tree
               !(RAList uni fun) -- ^ the tail trees
             | Nil

{-# INLINABLE null #-}
null :: RAList uni fun -> Bool
null Nil = True
null _   = False

{-# complete Cons, Nil #-}
{-# complete BHead, Nil #-}

-- /O(1)/
pattern Cons :: CekValue uni fun -> RAList uni fun -> RAList uni fun
pattern Cons x xs <- (uncons -> Just (x, xs)) where
  Cons x xs = cons x xs

-- O(1) worst-case
cons :: CekValue uni fun -> RAList uni fun -> RAList uni fun
cons x = \case
    (BHead w1 t1 (BHead w2 t2 ts')) | w1 == w2 -> BHead (2*w1+1) (Node x t1 t2) ts'
    ts                                         -> BHead 1 (Leaf x) ts

-- /O(1)/
uncons :: RAList uni fun -> Maybe (CekValue uni fun, RAList uni fun)
uncons = \case
    BHead _ (Leaf x) ts -> Just (x, ts)
    BHead treeSize (Node x t1 t2) ts ->
        -- probably faster than `div w 2`
        let halfSize = unsafeShiftR treeSize 1
            -- split the node in two)
        in Just (x, BHead halfSize t1 $ BHead halfSize t2 ts)
    Nil -> Nothing

{-# INLINABLE head #-}
-- O(1) worst-case
head :: RAList uni fun -> CekValue uni fun
head = fst . fromMaybe (error "empty RAList") . uncons

{-# INLINABLE tail #-}
-- O(1) worst-case
tail :: RAList uni fun -> RAList uni fun
tail = snd. fromMaybe (error "empty RAList") . uncons

-- 0-based
unsafeIndexZero :: RAList uni fun -> Word64 -> CekValue uni fun
unsafeIndexZero Nil _  = error "out of bounds"
unsafeIndexZero (BHead w t ts) !i  =
    if i < w
    then indexTree w i t
    else unsafeIndexZero ts (i-w)
  where
    indexTree :: Word64 -> Word64 -> Tree uni fun -> CekValue uni fun
    indexTree 1 0 (Leaf x) = x
    indexTree _ _ (Leaf _) = error "out of bounds"
    indexTree _ 0 (Node x _ _) = x
    indexTree treeSize offset (Node _ t1 t2) =
        let halfSize = unsafeShiftR treeSize 1 -- probably faster than `div w 2`
        in if offset <= halfSize
           then indexTree halfSize (offset - 1) t1
           else indexTree halfSize (offset - 1 - halfSize) t2

-- 0-based
safeIndexZero :: RAList uni fun -> Word64 -> Maybe (CekValue uni fun)
safeIndexZero Nil _  = Nothing
safeIndexZero (BHead w t ts) !i  =
    if i < w
    then indexTree w i t
    else safeIndexZero ts (i-w)
  where
    indexTree :: Word64 -> Word64 -> Tree uni fun -> Maybe (CekValue uni fun)
    indexTree 1 0 (Leaf x) = Just x
    indexTree _ _ (Leaf _) = Nothing
    indexTree _ 0 (Node x _ _) = Just x
    indexTree treeSize offset (Node _ t1 t2) =
        let halfSize = unsafeShiftR treeSize 1 -- probably faster than `div w 2`
        in if offset <= halfSize
           then indexTree halfSize (offset - 1) t1
           else indexTree halfSize (offset - 1 - halfSize) t2

-- 1-based
-- NOTE: no check if zero 0 index is passed, if 0 is passed it MAY overflow the index
unsafeIndexOne :: RAList uni fun -> Word64 -> CekValue uni fun
unsafeIndexOne Nil _ = error "out of bounds"
unsafeIndexOne (BHead w t ts) !i =
    if i <= w
    then indexTree w i t
    else unsafeIndexOne ts (i-w)
  where
    indexTree :: Word64 -> Word64 -> Tree uni fun -> CekValue uni fun
    indexTree 1 1 (Leaf x) = x
    indexTree _ _ (Leaf _) = error "out of bounds"
    indexTree _ 1 (Node x _ _) = x
    indexTree treeSize offset (Node _ t1 t2) =
        let halfSize = unsafeShiftR treeSize 1 -- probably faster than `div w 2`
            offset' = offset - 1
        in if offset' <= halfSize
           then indexTree halfSize offset' t1
           else indexTree halfSize (offset' - halfSize) t2

-- 1-based
-- NOTE: no check if zero 0 index is passed, if 0 is passed it MAY overflow the index
safeIndexOne :: RAList uni fun -> Word64 -> Maybe (CekValue uni fun)
safeIndexOne Nil _ = Nothing
safeIndexOne (BHead w t ts) !i =
    if i <= w
    then indexTree w i t
    else safeIndexOne ts (i-w)
  where
    indexTree :: Word64 -> Word64 -> Tree uni fun -> Maybe (CekValue uni fun)
    indexTree 1 1 (Leaf x) = Just x
    indexTree _ _ (Leaf _) = Nothing
    indexTree _ 1 (Node x _ _) = Just x
    indexTree treeSize offset (Node _ t1 t2) =
        let halfSize = unsafeShiftR treeSize 1 -- probably faster than `div w 2`
            offset' = offset - 1
        in if offset' <= halfSize
           then indexTree halfSize offset' t1
           else indexTree halfSize (offset' - halfSize) t2



-- 'Values' for the modified CEK machine.
data CekValue uni fun =
    -- This bang gave us a 1-2% speed-up at the time of writing.
    VCon !(Some (ValueOf uni))
  | VDelay (Term NamedDeBruijn uni fun ()) !(CekValEnv uni fun)
  | VLamAbs NamedDeBruijn (Term NamedDeBruijn uni fun ()) !(CekValEnv uni fun)
  | VBuiltin            -- A partial builtin application, accumulating arguments for eventual full application.
      !fun                   -- So that we know, for what builtin we're calculating the cost.
                             -- TODO: any chance we could sneak this into 'BuiltinRuntime'
                             -- where we have a partially instantiated costing function anyway?
      (Term NamedDeBruijn uni fun ()) -- This must be lazy. It represents the partial application of the
                             -- builtin function that we're going to run when it's fully saturated.
                             -- We need the 'Term' to be able to return it in case full saturation
                             -- is never achieved and a partial application needs to be returned
                             -- in the result. The laziness is important, because the arguments are
                             -- discharged values and discharging is expensive, so we don't want to
                             -- do it unless we really have to. Making this field strict resulted
                             -- in a 3-4.5% slowdown at the time of writing.
      (CekValEnv uni fun)    -- For discharging.
      !(BuiltinRuntime (CekValue uni fun))  -- The partial application and its costing function.
                                            -- Check the docs of 'BuiltinRuntime' for details.

type CekValEnv uni fun = RAList uni fun


instance Show (RAList uni fun) where
  show _ = "ralist"


instance Show (CekValue uni fun) where
  show _ = "cekvalue"
