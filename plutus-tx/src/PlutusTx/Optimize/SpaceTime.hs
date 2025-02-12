{-# LANGUAGE TemplateHaskell #-}

-- | Utilities for space-time tradeoff, such as recursion unrolling.
module PlutusTx.Optimize.SpaceTime (peel) where

import Language.Haskell.TH.Syntax.Compat qualified as TH
import PlutusTx.Function (fix)
import Prelude

{-| Given @n@, and the functional (or algebra) for a recursive function, peel @n@ layers
off of the recursion.

For example @peel 2 (\f xs -> case xs of [] -> 0; (_:ys) -> 1 + f ys)@ yields the
equivalence of the following function:

@
   lengthPeeled :: [a] -> a
   lengthPeeled xs = case xs of
     [] -> 0
     y:ys -> 1 + case ys of
       [] -> 0
       z:zs -> 1 + case zs of
         [] -> 0
         w:ws -> 1 + length ws
@

where @length@ is the regular recursive definition.
-}
peel
  :: forall a b
   . Int
  -> (TH.SpliceQ (a -> b) -> TH.SpliceQ (a -> b))
  -> TH.SpliceQ (a -> b)
peel 0 f = [||fix (\g -> $$(f [||g||]))||]
peel n f
  | n > 0 = f (peel (n - 1) f)
  | otherwise = error $ "PlutusTx.Optimize.SpaceTime.peel: negative n: " <> show n
