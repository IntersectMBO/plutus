module Projects.State where

import Prelude hiding (div)
import Control.Monad.Except (runExceptT)
import Control.Monad.Reader (class MonadAsk, runReaderT, asks)
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
import Env (Env)
import Gist (Gist(..))
import Halogen (HalogenM)
import MainFrame.Types (ChildSlots)
import Marlowe (getApiGists)
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Projects.Types (Action(..), State, _projects)
import Servant.PureScript.Ajax (errorToString)
import Text.Parsing.Parser (runParser)

handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  Action ->
  HalogenM State Action ChildSlots Void m Unit
handleAction LoadProjects = do
  assign _projects Loading
  settings <- asks _.ajaxSettings
  resp <- flip runReaderT settings $ runExceptT getApiGists
  assign _projects $ rmap sortGists $ lmap errorToString $ RemoteData.fromEither resp

handleAction (LoadProject lang gistId) = pure unit

handleAction (Cancel) = pure unit

sortGists :: Array Gist -> Array Gist
sortGists = sortBy f
  where
  dt :: String -> DateTime
  dt s = fromMaybe bottom <<< map unwrap <<< hush $ runParser s ISO.parseISO

  f (Gist { _gistUpdatedAt: a }) (Gist { _gistUpdatedAt: b }) = invert $ compare (dt a) (dt b)
