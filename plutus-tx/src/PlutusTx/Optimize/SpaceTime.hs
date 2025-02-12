{-# LANGUAGE BlockArguments  #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Utilities for space-time tradeoff, such as recursion unrolling.
module PlutusTx.Optimize.SpaceTime (peel, unroll, unrollBound) where

import Language.Haskell.TH.Syntax.Compat qualified as TH
import PlutusTx.Function (fix)
import Prelude

{-| Given @n@, and the step function for a recursive function, peel @n@ layers
off of the recursion.

For example @peel 3 (\self -> [[| \case [] -> 0; _ : ys -> 1 + self ys||])@
yields the equivalence of the following function:

@
  lengthPeeled :: [a] -> a
  lengthPeeled xs =
    case xs of                     -- first recursion step
      []     -> 0
      _ : ys -> 1 +
        case ys of                 -- second recursion step
          []     -> 0
          _ : zs -> 1 +
            case zs of             -- third recursion step
              []     -> 0
              _ : ws -> 1 +
                ( fix \self qs ->  -- rest of recursion steps in a tight loop
                    case qs of
                      []     -> 0
                      _ : ts -> 1 + self ts
                ) ws
@

-}
peel
  :: forall a b
   . Int
  -- ^ How many recursion steps to move outside of the recursion loop.
  -> (TH.SpliceQ (a -> b) -> TH.SpliceQ (a -> b))
  {- ^ Function that given a continuation splice returns
  a splice representing a single recursion step calling this continuation.
  -}
  -> TH.SpliceQ (a -> b)
peel 0 f = [||fix \self -> $$(f [||self||])||]
peel n f
  | n > 0 = f (peel (n - 1) f)
  | otherwise = error $ "PlutusTx.Optimize.SpaceTime.peel: negative n: " <> show n

{-| Given @n@, and the step function for a recursive function,
    unroll recursion @n@ layers at a time

For example @unroll 3 (\self -> [|| \case [] -> 0; _ : ys -> 1 + self ys ||])@
yields the equivalence of the following function:

@
  lengthUnrolled :: [a] -> a
  lengthUnrolled =
    fix \self xs ->                   -- beginning of the recursion "loop"
      case xs of                      -- first recursion step
        []     -> 0
        _ : ys -> 1 +
          case ys of                  -- second recursion step
            []     -> 0
            _ : zs -> 1 +
              case zs of              -- third recursion step
                []     -> 0
                _ : ws -> 1 + self ws -- end of the "loop"

@

-}
unroll
  :: forall a b
   . Int
  -- ^ How many recursion steps to perform inside the recursion loop.
  -> (TH.SpliceQ (a -> b) -> TH.SpliceQ (a -> b))
  {- ^ Function that given a continuation splice returns
  a splice representing a single recursion step calling this continuation.
  -}
  -> TH.SpliceQ (a -> b)
unroll n f = [||fix \self -> $$(unrollBound n f [||self||])||]

unrollBound
  :: forall a b
   . Int
  -- ^ How many recursion steps to perform inside the recursion loop.
  -> (TH.SpliceQ (a -> b) -> TH.SpliceQ (a -> b))
  {- ^ Function that given a continuation splice returns
  a splice representing a single recursion step calling this continuation.
  -}
  -> TH.SpliceQ (a -> b)
  -- ^ Splice representing continuation
  -> TH.SpliceQ (a -> b)
unrollBound 0 _step self = self
unrollBound n step self
  | n > 0 = unrollBound (n - 1) step (step self)
  | otherwise = error $ "PlutusTx.Optimize.SpaceTime.unrollBound: negative n: " <> show n
