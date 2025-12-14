{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Utilities for space-time tradeoff, such as recursion unrolling.
module PlutusTx.Optimize.SpaceTime (peel, unroll) where

import Prelude

import Language.Haskell.TH.Syntax qualified as TH
import PlutusTx.Function (fix)

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
@ -}
peel
  :: forall a b
   . Int
  -- ^ How many recursion steps to move outside of the recursion loop.
  -> (TH.Code TH.Q (a -> b) -> TH.Code TH.Q (a -> b))
  {-^ Function that given a continuation splice returns
  a splice representing a single recursion step calling this continuation. -}
  -> TH.Code TH.Q (a -> b)
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

@ -}
unroll
  :: forall a b
   . Int
  -- ^ How many recursion steps to perform inside the recursion loop.
  -> (TH.Code TH.Q (a -> b) -> TH.Code TH.Q (a -> b))
  {-^ Function that given a continuation splice returns
  a splice representing a single recursion step calling this continuation. -}
  -> TH.Code TH.Q (a -> b)
unroll n f = [||fix \self -> $$(nTimes n f [||self||])||]

-- | Apply a function @n@ times to a given value.
nTimes :: Int -> (a -> a) -> (a -> a)
nTimes 0 _ = id
nTimes 1 f = f
nTimes n f = f . nTimes (n - 1) f
