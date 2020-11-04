module Halogen.Extra where

import Prelude
import Control.Applicative.Free (hoistFreeAp)
import Control.Monad.Free (hoistFree)
import Data.Bifunctor (bimap)
import Data.Lens (Lens', set, view)
import Data.Newtype (over)
import Data.Tuple (Tuple(..))
import Halogen (ComponentHTML, HalogenF(..), HalogenM(..), get)
import Halogen.Query (HalogenM)
import Halogen.Query.HalogenM (HalogenAp(..), mapAction)

-- | This is a version of imapState that uses a lens
-- | With the official version it is easy to make a mistake and
-- | 'freeze' the old state and end up replacing and changes to
-- | the state that have happened asynchronously
imapState ::
  forall state state' action slots output m.
  Lens' state' state ->
  HalogenM state action slots output m
    ~> HalogenM state' action slots output m
imapState lens (HalogenM h) = HalogenM (hoistFree go h)
  where
  go :: HalogenF state action slots output m ~> HalogenF state' action slots output m
  go = case _ of
    State fs ->
      State
        ( \s' ->
            let
              (Tuple a s) = fs (view lens s')
            in
              (Tuple a (set lens s s'))
        )
    Subscribe fes k -> Subscribe fes k
    Unsubscribe sid a -> Unsubscribe sid a
    Lift q -> Lift q
    ChildQuery cq -> ChildQuery cq
    Raise o a -> Raise o a
    Par p -> Par (over HalogenAp (hoistFreeAp (imapState lens)) p)
    Fork hmu k -> Fork (imapState lens hmu) k
    Kill fid a -> Kill fid a
    GetRef p k -> GetRef p k

mapSubmodule ::
  forall m action action' state state' slots msg.
  Functor m =>
  Lens' state state' ->
  (action' -> action) ->
  HalogenM state' action' slots msg m
    ~> HalogenM state action slots msg m
mapSubmodule lens wrapper halogen = (imapState lens <<< mapAction wrapper) halogen

renderSubmodule ::
  forall m action action' state state' slots.
  Lens' state state' ->
  (action' -> action) ->
  (state' -> ComponentHTML action' slots m) ->
  state ->
  ComponentHTML action slots m
renderSubmodule lens wrapper renderer state = bimap (map wrapper) wrapper (renderer (view lens state))
