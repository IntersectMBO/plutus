module Projects.State where

import Prelude hiding (div)
import Control.Monad.Except (runExceptT)
import Control.Monad.Reader (runReaderT)
import Data.Array (sortBy)
import Data.Bifunctor (lmap, rmap)
import Data.DateTime (DateTime)
import Data.DateTime.ISO as ISO
import Data.Either (hush)
import Data.Lens (assign)
import Data.Maybe (fromMaybe)
import Data.Newtype (unwrap)
import Data.Ordering (invert)
import Effect.Aff.Class (class MonadAff)
import Gist (Gist(..))
import Halogen (HalogenM)
import MainFrame.Types (ChildSlots)
import Marlowe (SPParams_, getApiGists)
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Prelude (Unit, Void, bind, bottom, compare, const, discard, flip, map, mempty, pure, unit, ($), (<<<))
import Prim.TypeError (class Warn, Text)
import Projects.Types (Action(..), Lang(..), State, _projects)
import Servant.PureScript.Ajax (errorToString)
import Servant.PureScript.Settings (SPSettings_)
import Text.Parsing.Parser (runParser)

handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Action -> HalogenM State Action ChildSlots Void m Unit
handleAction settings LoadProjects = do
  assign _projects Loading
  resp <- flip runReaderT settings $ runExceptT getApiGists
  assign _projects $ rmap sortGists $ lmap errorToString $ RemoteData.fromEither resp

handleAction settings (LoadProject lang gistId) = pure unit

handleAction settings (Cancel) = pure unit

sortGists :: Array Gist -> Array Gist
sortGists = sortBy f
  where
  dt :: String -> DateTime
  dt s = fromMaybe bottom <<< map unwrap <<< hush $ runParser s ISO.parseISO

  f (Gist { _gistUpdatedAt: a }) (Gist { _gistUpdatedAt: b }) = invert $ compare (dt a) (dt b)
