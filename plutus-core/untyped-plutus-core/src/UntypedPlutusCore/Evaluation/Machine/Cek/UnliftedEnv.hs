{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE UnliftedDatatypes #-}

{-| Skew-binary environments with evaluated, unlifted elements. The tree sizes and
lookup algorithm follow 'Data.RandomAccessList.SkewBinary', but no lifted element
wrapper is stored at a binding. Continuations avoid lifted tuples and 'Maybe's. -}
module UntypedPlutusCore.Evaluation.Machine.Cek.UnliftedEnv
  ( RAList (Nil)
  , LookupResult (..)
  , consU
  , contUncons
  , contIndexZero
  , contIndexOne
  , lengthU
  , showsPrecWith
  ) where

import Data.Bits (setBit, unsafeShiftL, unsafeShiftR)
import Data.Kind (Type)
import Data.Word (Word64)
import GHC.Exts (UnliftedType)

type Tree :: UnliftedType -> Type
data Tree a = Node a !(Tree a) !(Tree a) | Leaf a

type RAList :: UnliftedType -> Type
data RAList a = BHead {-# UNPACK #-} !Word64 !(Tree a) !(RAList a) | Nil

consU :: a -> RAList a -> RAList a
consU x (BHead w1 t1 (BHead w2 t2 ts))
  | w1 == w2 = BHead (unsafeShiftL w1 1 `setBit` 0) (Node x t1 t2) ts
consU x ts = BHead 1 (Leaf x) ts
{-# INLINE consU #-}

contUncons :: b -> (a -> RAList a -> b) -> RAList a -> b
contUncons z _ Nil = z
contUncons _ f (BHead _ (Leaf x) ts) = f x ts
contUncons _ f (BHead treeSize (Node x t1 t2) ts) =
  let halfSize = unsafeShiftR treeSize 1
   in f x (BHead halfSize t1 $ BHead halfSize t2 ts)
{-# INLINE contUncons #-}

-- | A lookup result whose element has kind @UnliftedType@.
type LookupResult :: UnliftedType -> Type
data LookupResult a = Missing | Found a

-- See Note [Optimizations of contIndexZero] in Data.RandomAccessList.SkewBinary.
-- Inlining the continuation eliminates the result constructor and keeps construction
-- of the open-variable error inside the missing branch.
contIndexZero :: forall a b. (LookupResult a -> b) -> RAList a -> Word64 -> b
contIndexZero k = findTree
  where
    findTree :: RAList a -> Word64 -> b
    findTree Nil !_ = k Missing
    findTree (BHead w t ts) i =
      if i < w then indexTree w i t else findTree ts (i - w)

    indexTree :: Word64 -> Word64 -> Tree a -> b
    indexTree !w 0 t = case t of
      Node x _ _ -> k (Found x)
      Leaf x -> if w == 1 then k (Found x) else k Missing
    indexTree _ _ (Leaf _) = k Missing
    indexTree treeSize offset (Node _ t1 t2) =
      let halfSize = unsafeShiftR treeSize 1
       in if offset <= halfSize
            then indexTree halfSize (offset - 1) t1
            else indexTree halfSize (offset - 1 - halfSize) t2
{-# INLINE contIndexZero #-}

contIndexOne :: (LookupResult a -> b) -> RAList a -> Word64 -> b
contIndexOne k _ 0 = k Missing
contIndexOne k ts n = contIndexZero k ts (n - 1)
{-# INLINE contIndexOne #-}

lengthU :: RAList a -> Word64
lengthU = go 0
  where
    go !acc Nil = acc
    go !acc (BHead size _ ts) = go (acc + size) ts
{-# INLINE lengthU #-}

-- The element printer lets us retain the lifted skew-binary list's debug output.
showsPrecWith :: forall a. (Int -> a -> ShowS) -> Int -> RAList a -> ShowS
showsPrecWith _ _ Nil = showString "Nil"
showsPrecWith showValue p (BHead size tree rest) =
  showParen (p > 10) $
    showString "BHead "
      . showsPrec 11 size
      . showChar ' '
      . showTree 11 tree
      . showChar ' '
      . showsPrecWith showValue 11 rest
  where
    showTree :: Int -> Tree a -> ShowS
    showTree d (Leaf x) = showParen (d > 10) $ showString "Leaf " . showValue 11 x
    showTree d (Node x t1 t2) =
      showParen (d > 10) $
        showString "Node "
          . showValue 11 x
          . showChar ' '
          . showTree 11 t1
          . showChar ' '
          . showTree 11 t2
