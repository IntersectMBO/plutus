{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module PlutusTx.Data.List.TH where

import Data.Set (Set)
import Data.Set qualified as Set
import Data.Traversable (for)
import Language.Haskell.TH qualified as TH
import PlutusTx.Data.List qualified as List
import Prelude

{-| Generate variables bound to the given indices of a @BuiltinList@.

Sample Usage:

 @
   f :: List Integer -> Integer
   f list =
   $( destructList
        "s"
        (Set.fromList [1, 4, 5])
        'list
        [|s1 + s4 + s5|]
    )
 @

This computes the sum of list elements at indices 1, 4 and 5. -}
destructList
  :: String
  -- ^ Prefix of the generated bindings
  -> Set Int
  -- ^ Element ids you need, starting from 0
  -> TH.Name
  -- ^ The builtin list to destruct
  -> TH.ExpQ
  -- ^ The computation that consumes the elements
  -> TH.ExpQ
destructList p is n k = do
  let strict = TH.bangP . TH.varP
      nonstrict = TH.tildeP . TH.varP
      elemName i = TH.mkName $ p ++ show i
  tailNames <- for [0 .. maximum is] $ \i -> TH.newName ("tail" ++ show i)
  decs <- fmap (concat . concat) . for [0 .. maximum is] $ \i -> do
    let
      -- if tailx is only used once, make it non-strict so that it can be inlined
      tailStrictness = if Set.member (i + 1) is then strict else nonstrict
      n' = if i == 0 then n else tailNames !! (i - 1)
    sequence $
      [ [d|$(strict (elemName i)) = List.head $(TH.varE n')|]
      | Set.member i is
      ]
        ++ [ [d|$(tailStrictness (tailNames !! i)) = List.tail $(TH.varE n')|]
           | i /= maximum is
           ]
  TH.letE (pure <$> decs) k
