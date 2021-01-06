{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.Resumable(
    -- * The 'Resumable' effect
    -- $resumable
    Resumable(..)
    , prompt
    , select
    -- * Handling the 'Resumable' effect
    , Request(..)
    , Response(..)
    , RequestID(..)
    , IterationID(..)
    , Requests(..)
    , ResumableInterpreter
    , Responses(..)
    , insertResponse
    , responses
    -- * Handling the 'Resumable' effect with continuations
    , handleResumable
    , suspendNonDet
    , SuspendedNonDet(..)
    , NonDetCont(..)
    , SuspMap(..)
    ) where

import           Control.Applicative
import           Data.Aeson                    (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import           Data.Map                      (Map)
import qualified Data.Map                      as Map
import           Data.Semigroup                (Max (..))
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                  (Generic)
import           Numeric.Natural               (Natural)

import           Control.Monad.Freer
import           Control.Monad.Freer.Coroutine
import           Control.Monad.Freer.NonDet
import           Control.Monad.Freer.State

-- $resumable
-- This module defines the 'Resumable' effect and its handlers. Programs that
-- use the 'Resumable' effect can non-deterministically ask for values from the
-- environment. Non-deterministically here means that we can issue multiple
-- prompts at the same time, each with its own continuation, and continue with
-- the one that is answered first while discarding the other ones.
--
-- == Constructing resumable programs
-- Resumable programs can be constructed using 'prompt' and 'select'. 'prompt'
-- has one argument that describes the request.
--
-- >>> (prompt "A") 'select' (prompt "B")
--
-- makes two requests and returns the answer of the one that is responded to
-- first.
--
-- == Running resumable programs
-- The 'Resumable' effect is handled in two stages, using 'handleResumable' and
-- 'handleNonDetPrompt' (see note [Running resumable programs] for a description
-- of how it works). The types 'Requests' and 'Responses' store the requests
-- made by, and responses given to, a resumable program.
--
-- == 'Resumable' and non-determinism
-- The kind of non-determinism used in 'Resumable' is different from the kind
-- encoded in 'Control.Applicative.Alternative' in that it does not allow
-- for backtracking (because it's not meant to encode "searching a problem
-- space for a solution"). 'Resumable' programs do not have the ability to call
-- 'Control.Applicative.Alternative.empty' and therefore do not implement
-- the 'Control.Applicative.Alternative' class.


-- | A data type for representing non-deterministic prompts.
data Resumable i o r where
    RRequest :: o -> Resumable i o i
    -- See https://hackage.haskell.org/package/freer-simple-1.2.1.1/docs/src/Control.Monad.Freer.Internal.html#NonDet
    RSelect :: Resumable i o Bool

prompt :: Member (Resumable i o) effs => o -> Eff effs i
prompt o = send (RRequest o)

select ::
    forall i o effs a.
    Member (Resumable i o) effs
    => Eff effs a
    -> Eff effs a
    -> Eff effs a
select l r = send @(Resumable i o) RSelect >>= \b -> if b then l else r

-- | A value that uniquely identifies requests made during the execution of
--   'Resumable' programs.
newtype RequestID = RequestID Natural
    deriving stock (Eq, Ord, Show, Generic)
    deriving newtype (ToJSON, FromJSON, ToJSONKey, FromJSONKey, Pretty, Enum, Num)

-- | A value that uniquely identifies groups of requests.
newtype IterationID = IterationID Natural
    deriving stock (Eq, Ord, Show, Generic)
    deriving newtype (ToJSON, FromJSON, ToJSONKey, FromJSONKey, Pretty, Enum, Num)
    deriving (Semigroup) via (Max Natural)

instance Monoid IterationID where
    mappend = (<>)
    mempty = IterationID 0

data Request o =
    Request
        { rqID      :: RequestID
        , itID      :: IterationID
        , rqRequest :: o
        } deriving stock (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)
           deriving anyclass (ToJSON, FromJSON)

instance Pretty o => Pretty (Request o) where
    pretty Request{rqID, itID, rqRequest} =
        indent 2 $ vsep [
            "Iteration" <+> pretty itID <+> "request ID" <+> pretty rqID,
            "Request:" <+> pretty rqRequest
        ]

data Response i =
    Response
        { rspRqID     :: RequestID
        , rspItID     :: IterationID
        , rspResponse :: i
        }  deriving stock (Eq, Ord, Show, Generic, Functor, Foldable, Traversable)
           deriving anyclass (ToJSON, FromJSON)

instance Pretty i => Pretty (Response i) where
    pretty Response{rspRqID, rspItID, rspResponse} =
        indent 2 $ vsep [
            "Iteration" <+> pretty rspItID <+> "request ID" <+> pretty rspRqID,
            "Response:" <+> pretty rspResponse
        ]

newtype Requests o = Requests { unRequests :: [Request o] }
    deriving newtype (Eq, Ord, Show, Semigroup, Monoid)
    deriving anyclass (ToJSON, FromJSON)
    deriving stock (Generic, Functor, Foldable, Traversable)

instance Pretty o => Pretty (Requests o) where
    pretty Requests{unRequests} =
        indent 2 $ vsep ("Requests:" : (pretty <$> unRequests))

newtype Responses i = Responses { unResponses :: Map (IterationID, RequestID) i }
    deriving newtype (Eq, Ord, Show, Semigroup, Monoid)
    deriving anyclass (ToJSON, FromJSON)
    deriving stock (Generic, Functor, Foldable, Traversable)

-- | A list of all responses ordered by iteration and request ID
responses :: Responses i -> [Response i]
responses =
    let mkResp (itId, rqId) evt = Response{rspRqID = rqId, rspItID = itId, rspResponse=evt}
    in fmap (uncurry mkResp) . Map.toAscList . unResponses

instance Pretty i => Pretty (Responses i) where
    pretty (Responses mp) =
        let entries = Map.toList mp
            prettyEntry ((itID, reqID), i) =
                hang 2 $ vsep ["IterationID:" <+> pretty itID, "RequestID:" <+> pretty reqID, "Event:" <+> pretty i]
        in vsep (prettyEntry <$> entries)

{- Note [Running resumable programs]

Running 'Resumable' programs involves two stages. First we transform the programs
into ones that use the 'NonDet' and 'Yield' effects that come with
'freer-simple'. Then we interpret the resulting program with 'Reader' and
'State' effects to capture the state of open requests.

#### Stage 1

Stage 1 is implemented in 'handleResumable'. The result is a program that uses
'NonDet' and 'Yield' in a very specific way to implement the resumable
functionality. The reason why we don't say something like @type Resumable effs
= Members '[NonDet, Yield] effs@ instead of the 'Resumable' data type is that
'NonDet' allows for backtracking, which we do not want to expose to the users.

The programs produced by 'handleResumable' have at most one level of
backtracking (to the next call to 'prompt'). There is no 'empty'
constructor (and no 'Alternative' instance for contracts) because the only
thing that can cause backtracking to happen is the provisioning of an answer
to a 'prompt' call from the environment.

#### Stage 2

Stage 2 is implemented in 'suspendNonDet'. Here we handle the 'Yield' and
'NonDet' effects that were introduced in the previous stage. In this stage we
assign two numbers to each request issued by the contract, a 'RequestID' and an
'IterationID'. The request ID is simply a consecutive numbering of every
request that is made during the lifetime of the contract. The iteration ID is
unique for each group of open requests that the contract produces.

Of particular importance is the 'runStep' function, which deals with the
'Status' values that we get from 'runC'. It uses the 'ResumableInterpreter' effects:

>>> type ResumableInterpreter i o effs = State IterationID ': NonDet ': State RequestID ': effs

Note that the 'IterationID' state comes before 'NonDet', and the 'RequestID'
state comes after 'NonDet'. This is done so that we increase the 'RequestID'
whenever a request is made, and the 'IterationID' only when a request is
answered.

-}

-- Effects that are used to interpret the Yield/NonDet combination
-- produced by 'handleResumable'.
type ResumableInterpreter i o effs a =
    -- anything that comes before 'NonDet' can be backtracked.

    -- We put 'State IterationID' here to ensure that only
    -- the 'State IterationID' effects of the branch that is
    -- selected will persist, so that the iteration ID is increased
    -- exactly once per branching level.
     State IterationID
     ': NonDet
     ': State RequestID
     ': State (SuspMap i o effs a)
     ': State (Requests o)
     ': effs

-- | Interpret the 'Resumable' effect in terms of the 'Yield' and 'NonDet'
--   effects.
handleResumable ::
    forall i o effs.
    ( Member (Yield o i) effs
    , Member NonDet effs
    )
    => Eff (Resumable i o ': effs)
    ~> Eff effs
handleResumable = interpret $ \case
    RRequest o -> yield o id
    RSelect    -> send MPlus

-- | Status of a suspended comptutation
data SuspendedNonDet i o effs a =
    -- | The computation is done
    AResult a
     -- | The computation is waiting for inputs
    | AContinuation (NonDetCont i o effs a)

-- | Continuation of a suspended computation that is waiting for one of several possible responses.
data NonDetCont i o effs a =
    NonDetCont
        { ndcCont     :: Response i -> Eff effs (Maybe (SuspendedNonDet i o effs a))
        , ndcRequests :: Requests o
        }

newtype SuspMap i o effs a = SuspMap (Map (RequestID, IterationID) (i -> Eff (ResumableInterpreter i o effs a) a))

-- | Handle the 'ResumableInterpreter' effects, returning a new suspended
--   computation.
runSuspInt ::
    forall i o a effs.
    Eff (ResumableInterpreter i o effs a) a
    -> Eff effs (Maybe (SuspendedNonDet i o effs a))
runSuspInt = go mempty where
    go currentIteration action = do
        let suspMap = SuspMap Map.empty -- start with a fresh map in every step to make sure that the old continuations are discarded
        result <- runState @(Requests o) mempty $ runState suspMap $ evalState (RequestID 0) $ makeChoiceA @Maybe $ evalState currentIteration action
        case  result of
            ((Nothing, SuspMap mp), rqs) ->
                let k Response{rspRqID, rspItID, rspResponse} = do
                        case Map.lookup (rspRqID, rspItID) mp of
                            Nothing -> pure Nothing
                            Just k' -> go (succ currentIteration) (k' rspResponse)
                in pure $ Just $ AContinuation $ NonDetCont { ndcCont = k, ndcRequests = rqs}
            ((Just a, _), _) -> pure $ Just $ AResult a

-- | Given the status of a suspended computation, either
--   return the result or record the request and store
--   the continuation in the 'SuspMap'
runStep ::
    forall i o a effs.
    Status (ResumableInterpreter i o effs a) o i a
    -> Eff (ResumableInterpreter i o effs a) a
runStep = \case
    Done a -> pure a
    Continue o k -> do

        -- nextRequestID' generates a pair of 'RequestID' and 'IterationID' for
        -- the current request. It writes the value 'a', which describes the
        -- request, to the 'Requests', alongside the two identifiers.
        (iid,nid) <- nextRequestID o

        -- 'continue' is the continuation for a response to the current
        -- request.
        let continue v = clearRequests @o >> k v >>= runStep
        modify @(SuspMap i o effs a) (\(SuspMap mp) -> SuspMap $ Map.insert (nid, iid) continue mp)
        empty

-- | Interpret 'Yield' as a prompt-type effect using 'NonDet' to
--   branch out and choose a branch, and the 'State' effects to
--   keep track of request IDs.
suspendNonDet ::
    forall i o a effs.
    Eff (Yield o i ': ResumableInterpreter i o effs a) a
    -> Eff effs (Maybe (SuspendedNonDet i o effs a))
suspendNonDet e = runSuspInt (runC e >>= runStep) where

insertResponse :: Response i -> Responses i -> Responses i
insertResponse Response{rspRqID,rspItID,rspResponse} (Responses r) =
    Responses $ Map.insert (rspItID, rspRqID) rspResponse r

nextRequestID ::
    ( Member (State (Requests o)) effs
    , Member (State IterationID) effs
    , Member (State RequestID) effs
    )
    => o
    -> Eff effs (IterationID, RequestID)
nextRequestID s = do
    Requests{unRequests} <- get
    requestID <- get @RequestID
    iid <- get @IterationID
    let niid = succ iid
        nid  = succ requestID
    put $ Requests
            { unRequests = Request{rqRequest=s,rqID=nid,itID=niid} : unRequests
            }
    put niid
    put nid
    pure (niid, nid)

clearRequests :: forall o effs. Member (State (Requests o)) effs => Eff effs ()
clearRequests = modify @(Requests o) (\rq -> rq{unRequests = [] })
