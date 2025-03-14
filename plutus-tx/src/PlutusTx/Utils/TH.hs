{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}

module PlutusTx.Utils.TH where

import Data.Set (Set)
import Data.Set qualified as Set
import Data.Traversable (for)
import Language.Haskell.TH qualified as TH
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.IsData.Class (UnsafeFromData (..))
import Prelude

-- | Generate variables bound to the given indices of a @BuiltinList@.
--
-- Sample Usage:
--
--  @
--    f :: BI.BuiltinList BI.BuiltinData -> Integer
--    f list =
--    $( destructBuiltinList
--         "s"
--         (Set.fromList [1, 4, 5])
--         [t|Integer|]
--         'list
--         [|s1 + s4 + s5|]
--     )
--  @
--
-- This computes the sum of list elements at indices 1, 4 and 5.
destructBuiltinList
  :: String
  -- ^ Prefix of the generated bindings
  -> Set Int
  -- ^ Element ids you need, starting from 0
  -> TH.TypeQ
  -- ^ The type of elements
  -> TH.Name
  -- ^ The builtin list to destruct
  -> TH.ExpQ
  -- ^ The computation that consumes the elements
  -> TH.ExpQ
destructBuiltinList p is ty n k = do
  let strict = TH.bangP . TH.varP
      nonstrict = TH.tildeP . TH.varP
      elemName i = TH.mkName $ p ++ show i
  tailNames <- for [0 .. maximum is] $ \i -> TH.newName ("tail" ++ show i)
  decs <- fmap (concat . concat) . for [0 .. maximum is] $ \i -> do
    let -- if tailx is only used once, make it non-strict so that it can be inlined
        tailStrictness = if Set.member (i + 1) is then strict else nonstrict
        n' = if i == 0 then n else tailNames !! (i - 1)
    sequence $
      [ [d|$(strict (elemName i)) = unsafeFromBuiltinData @($ty) (BI.head $(TH.varE n'))|]
      | Set.member i is
      ]
        ++ [ [d|$(tailStrictness (tailNames !! i)) = BI.tail $(TH.varE n')|]
           | i /= maximum is
           ]
  TH.letE (pure <$> decs) k
