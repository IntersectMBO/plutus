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
    , handleResumable
    , handleNonDetPrompt
    ) where

import           Control.Applicative
import           Data.Aeson                    (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import           Data.List.NonEmpty            (NonEmpty (..))
import           Data.Map                      (Map)
import qualified Data.Map                      as Map
import           Data.Semigroup                (Max (..))
import           Data.Semigroup.Foldable       (foldMap1)
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                  (Generic)
import           Numeric.Natural               (Natural)

import           Control.Monad.Freer
import           Control.Monad.Freer.Coroutine
import           Control.Monad.Freer.NonDet
import           Control.Monad.Freer.Reader
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

instance Pretty i => Pretty (Responses i) where
    pretty (Responses mp) =
        let entries = Map.toList mp
            prettyEntry ((itID, reqID), i) =
                hang 2 $ vsep ["IterationID:" <+> pretty itID, "RequestID:" <+> pretty reqID, "Event:" <+> pretty i]
        in vsep (prettyEntry <$> entries)

{- Note [Running resumable programs]

Running 'Resumable' programs involves two stages. First we transform the programs into ones that use the 'NonDet' and 'Yield' effects that come with 'freer-simple'. Then we interpret the resulting program with 'Reader' and 'State' effects to capture the state of open requests.

#### Stage 1

Stage 1 is implemented in 'handleResumable'. The result is a program that uses 'NonDet' and 'Yield' in a very specific way to implement the resumable functionality. The reason why we don't say something like 'type Resumable effs = Members '[NonDet, Yield] effs' instead of the 'Resumable' data type is that 'NonDet' allows for backtracking, which we do not want to expose to the users.

The programs produced by 'handleResumable' have at most one level of backtracking (to the next call to 'prompt'). There is no 'empty' constructor (and no 'Alternative' instance for contracts) because the only thing that can cause backtracking to happen is the provisioning of an answer to a 'prompt' call from the environment.

#### Stage 2

Stage 2 is implemented in 'handleNonDetPrompt'. Here we handle the 'Yield' and 'NonDet' effects that were introduced in the previous stage. In this stage we assign two numbers to each request issued by the contract, a 'RequestID' and an 'IterationID'. The request ID is simply a consecutive numbering of every request that is made during the lifetime of the contract. The iteration ID is unique for each group of open requests that the contract produces.

Of particular importance is the 'loop' function, which deals with the 'Status' values that we get from 'runC'. It uses the 'ResumableInterpreter' effects:

>>> type ResumableInterpreter i o effs = State IterationID ': NonDet ': State RequestID ': effs

Note that the 'IterationID' state comes before 'NonDet', and the 'RequestID' state comes after 'NonDet'. This is done so that we increase the 'RequestID' whenever a request is made, and the 'IterationID' only when a request is answered.

-}

-- Effects that are used to interpret the Yield/NonDet combination
-- produced by 'handleResumable'.
type ResumableInterpreter i o effs =
    -- anything that comes before 'NonDet' can be backtracked.

    -- We put 'State IterationID' here to ensure that only
    -- the 'State IterationID' effects of the branch that is
    -- selected will persist, so that the iteration ID is increased
    -- exactly once per branching level.
     State IterationID
     ': NonDet
     ': State RequestID
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

-- | Interpret 'Yield' as a prompt-type effect using 'NonDet' to
--   branch out and choose a branch, and the 'State' effects to
--   keep track of request IDs.
handleNonDetPrompt ::
    forall i o a effs.
    ( Member (Reader (Responses i)) effs
    , Member (State (Requests o)) effs
    )
    => Eff (Yield o i ': ResumableInterpreter i o effs) a
    -> Eff effs (Maybe a)
handleNonDetPrompt e = result where
    result =
        mkResult @effs @o @a =<<
            (evalState (RequestID 0) $ makeChoiceA @Maybe $ evalState mempty $ (loop =<< runC e))

    -- Check the result and write a request to the state if
    -- the computation is waiting for input
    loop :: Status (ResumableInterpreter i o effs) o i a -> Eff (ResumableInterpreter i o effs) a
    loop (Continue a k) = do
        Responses mp' <- ask

        -- nextRequestID' generates a pair of 'RequestID' and 'IterationID' for
        -- the current request. It writes the value 'a', which describes the
        -- request, to the 'Requests', alongside the two identifiers.
        (iid,nid) <- nextRequestID a
        case Map.lookup (iid, nid) mp' of

            -- If our current request has not been answered then we fail, so
            -- the other branches will be tried. At this point the change to
            -- 'IterationID' is rolled back but the change to 'RequestID'
            -- persists, due to the ordering of effects in
            -- 'ResumableInterpreter'
            Nothing -> empty

            -- If there is an answer for the current request then we feed it to
            -- the continuation 'k' and proceed to the next iteration. The
            -- changes to 'RequestID' and 'IterationID' both are kept.
            Just v  -> clearRequests @o >> k v >>= loop

    loop (Done a)       = pure a


-- Return the answer or the remaining requests
mkResult ::
    forall effs o a.
    Member (State (Requests o)) effs
    => Maybe a
    -> Eff effs (Maybe a)
mkResult (Just a) = modify @(Requests o) (\rs -> rs { unRequests = [] }) >> pure (Just a)
mkResult Nothing  = modify @(Requests o) (\rs -> rs { unRequests = pruneRequests (unRequests rs)}) >> pure Nothing

insertResponse :: Response i -> Responses i -> Responses i
insertResponse Response{rspRqID,rspItID,rspResponse} (Responses r) =
    Responses $ Map.insert (rspItID, rspRqID) rspResponse r

pruneRequests :: [Request o] -> [Request o]
pruneRequests [] = []
pruneRequests (r:rs) =
    let Max maxIteration = foldMap1 (Max . itID) (r :| rs)
    in filter ((==) maxIteration . itID) (r:rs)

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
