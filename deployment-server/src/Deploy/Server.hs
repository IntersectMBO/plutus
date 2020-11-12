{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Deploy.Server
    ( app
    ) where

import           Control.Concurrent.Chan      (Chan, writeChan)
import           Control.Monad.IO.Class       (liftIO)
import           Control.Newtype.Generics     (unpack)
import           Data.Maybe                   (isJust)
import           Data.Proxy                   (Proxy (Proxy))
import           Deploy.Types                 (Ref)
import           GitHub.Data.Webhooks.Events  (PullRequestEvent (evPullReqPayload))
import           GitHub.Data.Webhooks.Payload (HookPullRequest (whPullReqBase, whPullReqMergedAt),
                                               PullRequestTarget (whPullReqTargetRef))
import           Network.Wai                  (Application)
import           Servant                      (Context (EmptyContext, (:.)), Handler, serveWithContext)
import           Servant.API                  (Get, JSON, Post, (:<|>) ((:<|>)), (:>))
import           Servant.GitHub.Webhook       (GitHubEvent, GitHubKey, GitHubSignedReqBody,
                                               RepoWebhookEvent (WebhookPullRequestEvent))

type Api
     = "github" :> (GitHubEvent '[ 'WebhookPullRequestEvent] :> GitHubSignedReqBody '[ JSON] PullRequestEvent :> Post '[ JSON] ()
                    :<|> "health" :> Get '[ JSON] ())

isMergePullRequestEvent :: PullRequestEvent -> Bool
isMergePullRequestEvent = isJust . whPullReqMergedAt . evPullReqPayload

hasTargetRef :: Ref -> PullRequestEvent -> Bool
hasTargetRef ref = (==) (unpack ref) . whPullReqTargetRef . whPullReqBase . evPullReqPayload

prEventAction ::
       Ref
    -> Chan PullRequestEvent
    -> RepoWebhookEvent
    -> ((), PullRequestEvent)
    -> Handler ()
prEventAction ref chan _ (_, event)
    | isMergePullRequestEvent event && hasTargetRef ref event = liftIO $ writeChan chan event
prEventAction _ _ _ (_, event)
    | isMergePullRequestEvent event = liftIO $ putStrLn "PullRequestEvent not for target ref"
prEventAction _ _ _ _ = liftIO $ putStrLn "non-merge PullRequestEvent"

healthCheck :: Handler ()
healthCheck = pure ()

app :: Ref -> Chan PullRequestEvent -> GitHubKey PullRequestEvent -> Application
app ref chan key =
    serveWithContext (Proxy :: Proxy Api) (key :. EmptyContext) $
    prEventAction ref chan :<|> healthCheck
