module Halogen.Extra where

import Prelude
import Control.Applicative.Free (hoistFreeAp)
import Control.Monad.Free (hoistFree)
import Control.Monad.State (get)
import Data.Bifunctor (bimap)
import Data.Foldable (for_)
import Data.Lens (Lens', Traversal', preview, set, view)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (over)
import Data.Tuple (Tuple(..))
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Uncurried (EffectFn1, runEffectFn1)
import Halogen (ComponentHTML, HalogenF(..), HalogenM(..), RefLabel, getHTMLElementRef)
import Halogen.HTML (IProp)
import Halogen.HTML.Core (Prop)
import Halogen.HTML.Core as Core
import Halogen.Query (HalogenM)
import Halogen.Query.HalogenM (HalogenAp(..), mapAction)
import Halogen.Query.HalogenM (imapState) as Halogen
import Halogen.Query.Input (Input)
import Halogen.Query.Input as Input
import Unsafe.Coerce (unsafeCoerce)
import Web.HTML.HTMLElement (HTMLElement)

-- | This is a version of imapState that uses a lens.
-- | With the official version it is easy to make a mistake and
-- | 'freeze' the old state and end up replacing any changes to
-- | the state that have happened asynchronously.
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

-- | This lets you map the state of a submodule that may not exist,
-- | given an affine traversal into that optional substate. It's
-- | an ugly solution, and it suffers from the same problem with
-- | Halogen's `imapState` noted above. But for now, at least it works.
mapMaybeSubmodule ::
  forall m state state' action action' slots msg.
  Functor m =>
  Traversal' state state' ->
  (action' -> action) ->
  state' ->
  HalogenM state' action' slots msg m Unit ->
  HalogenM state action slots msg m Unit
mapMaybeSubmodule traversal wrapper submoduleDefaultState submoduleHandleAction = do
  state <- get
  let
    mSubmoduleState :: Maybe state'
    mSubmoduleState = preview traversal state

    subToMain :: state' -> state
    subToMain submoduleState = set traversal submoduleState state

    mainToSub :: state -> state'
    mainToSub = fromMaybe submoduleDefaultState <<< preview traversal
  Halogen.imapState subToMain mainToSub $ mapAction wrapper $ submoduleHandleAction

foreign import scrollIntoView_ :: EffectFn1 HTMLElement Unit

scrollIntoView :: forall surface action slots output m. MonadEffect m => RefLabel -> HalogenM surface action slots output m Unit
scrollIntoView ref = do
  mElement <- getHTMLElementRef ref
  for_ mElement (liftEffect <<< runEffectFn1 scrollIntoView_)

-- This HTML property dispatch lifecycle actions when the element is added or removed to the DOM
lifeCycleEvent :: forall r action. { onInit :: Maybe action, onFinilize :: Maybe action } -> IProp r action
lifeCycleEvent handlers = (unsafeCoerce :: Prop (Input action) -> IProp r action) $ Core.ref onLifecycleEvent
  where
  onLifecycleEvent (Just _) = Input.Action <$> handlers.onInit

  onLifecycleEvent Nothing = Input.Action <$> handlers.onFinilize
