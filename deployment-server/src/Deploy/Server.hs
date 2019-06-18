{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Deploy.Server
    ( app
    ) where

import           Control.Concurrent.Chan      (Chan, writeChan)
import           Control.Monad.IO.Class       (liftIO)
import           Data.Maybe                   (isJust)
import           Data.Proxy                   (Proxy (Proxy))
import           GitHub.Data.Webhooks.Events  (PullRequestEvent (evPullReqPayload),
                                               PullRequestEventAction (PullRequestClosedAction))
import           GitHub.Data.Webhooks.Payload (HookPullRequest (whPullReqMergedAt))
import           Network.Wai                  (Application)
import           Servant                      (Context ((:.), EmptyContext), Handler, serveWithContext)
import           Servant.API                  ((:<|>) ((:<|>)), (:>), Get, JSON, Post)
import           Servant.GitHub.Webhook       (GitHubEvent, GitHubKey, GitHubSignedReqBody,
                                               RepoWebhookEvent (WebhookPullRequestEvent))

type Api
     = "github" :> (GitHubEvent '[ 'WebhookPullRequestEvent] :> GitHubSignedReqBody '[ JSON] PullRequestEvent :> Post '[ JSON] ()
                   :<|> "health" :> Get '[JSON] ())

isMergePullRequestEvent :: PullRequestEvent -> Bool
isMergePullRequestEvent = isJust . whPullReqMergedAt . evPullReqPayload

prEventAction :: Chan PullRequestEvent -> RepoWebhookEvent -> ((), PullRequestEvent) -> Handler ()
prEventAction chan _ (_, event)
    | isMergePullRequestEvent event = liftIO $ writeChan chan event
prEventAction _ _ _ = liftIO $ putStrLn "non-merge PullRequestEvent"

healthCheck :: Handler ()
healthCheck = pure ()

app :: Chan PullRequestEvent -> GitHubKey PullRequestEvent -> Application
app chan key =
    serveWithContext (Proxy :: Proxy Api) (key :. EmptyContext) $ prEventAction chan :<|> healthCheck
