{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
-- | A version of 'Language.Plutus.Contract.Contract' that
--   writes checkpoints.
module Language.Plutus.Contract.Resumable(
    Resumable(..)
    , ResumableError(..)
    , ResumableResult(..)
    , Step(..)
    , contramapI
    , mapO
    , step
    , pretty
    , lowerM
    , mapStep
    , withResumableError
    , checkpoint
    -- * Records
    , initialise
    , insertAndUpdate
    , updateRecord
    , execResumable
    , runResumable
    ) where

import           Control.Applicative
import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Morph
import           Control.Monad.Reader
import           Control.Monad.Writer
import qualified Data.Aeson                      as Aeson
import qualified Data.Aeson.Types                as Aeson
import           Data.Bifunctor                  (Bifunctor (..))

import           Language.Plutus.Contract.Record

{- Note [Handling state in contracts]

The 'Resumable' type encodes programs with a serialisable state that operate on
event streams. 'Resumable e (Step i o)' consumes inputs of type 'i' and produces
requests (describing the inputs that are expected next) of type 'o'. As such,
'Resumable e (Step i o)' is similar to the @Prompt i o@ type found in the
@prompt@ package.

Unlike the 'Prompt' type however, 'Resumable e (Step i o)' programs have a
builtin way of serialising their state *efficiently*: While we can always take
the state of a stream-consuming program to be the list of events it has seen so
far, we have to replay all the previous events every time a new event is
received, making the complexity of recovering the current state from the event
list quadratic.

We avoid this in 'Resumable e (Step i o)' by adding checkpoints at which the state can be serialised and resumed without having to replay all the previous
events.

The current state of 'Resumable e (Step i o)' programs is captured by the 'Record
i' type. Every 'Record' is a tree with branches that match the structure of the
'Resumable' program whose state it represents.

Given a 'Resumable e (Step i o)'  we can use 'initialise' to get the initial
'Record' that captures the state after zero events have been consumed.
'initialise' uses the writer to collect all 'o' values that describe the inputs
the progam is waiting for. When we have a new input, we call
'insertAndUpdate' with our resumable program, the previous 'Record', and the
input to get the 'Record'.

How does the checkpointing work? Note the 'CJSONCheckpoint' constructor of
'Resumable'. This constructor is used to insert a checkpoint into the resumable
program. Whenever as part of a call to 'insertAndUpdate' we encounter a
'CJSONCheckpoint n' node, we throw away the sub-tree of the old 'Record' that
contained the state of 'n', and replace it with the serialised value of the
result of 'n'. From now on, whenever we want to restore the state of
'CJSONCheckpoint' n, we use the serialised value in the 'Record', so we don't
ever need to evaluate 'n' again.

-}

-- | 'Step i o a' is a single step in a resumable program, consuming an input
--   of type 'i' and producing either a result of type 'a', or a request 'o'
--   asking for a different input value. 'Step i o' is like an inverted request-
--   response pair: We offer the response (in form of 'i'), and only if it
--   is the wrong response do we record the request in form of 'o'.
newtype Step i o a = Step { runStep :: i -> Either o a }
    deriving stock Functor
    deriving (Applicative, Monad, MonadReader i, MonadError o) via (ReaderT i (Either o))

contramapI :: (i -> j) -> Step j o a -> Step i o a
contramapI f (Step a) = Step (a . f)

mapO :: (o -> p) -> Step i o a -> Step i p a
mapO f (Step a) = Step (fmap (first f) a)

-- | A resumable program made up of 'Step's.
data Resumable e f a where
    CMap :: (a' -> a) -> Resumable e f a' -> Resumable e f a
    CAp :: Resumable e f (a' -> a) -> Resumable e f a' -> Resumable e f a
    CAlt :: Resumable e f a -> Resumable e f a -> Resumable e f a
    CEmpty :: Resumable e f a
    CBind :: Resumable e f a' -> (a' -> Resumable e f a) -> Resumable e f a

    CStep :: f a -> Resumable e f a
    CJSONCheckpoint :: (Aeson.FromJSON a, Aeson.ToJSON a) => Resumable e f a -> Resumable e f a
    CError :: e -> Resumable e f a

instance MFunctor (Resumable e) where
    hoist = mapStep

-- | An error that can occur when updating a 'Record' using a
--   'Resumable e (Step i o)'.
data ResumableError e =
    RecordMismatch [String]
    -- ^ The structure of the record does not match the structure of the
    --   'Resumable'.
    | AesonError String
    -- ^ Something went wrong while decoding a JSON value
    | ProgressError
    -- ^ Progress was made unexpectedly.
    | OtherError e
    deriving (Eq, Ord, Show)

throwRecordmismatchError :: MonadError (ResumableError e) m => String -> m a
throwRecordmismatchError = throwError . RecordMismatch . pure

addRecordMismatchInfo :: (MonadError (ResumableError e) m) => String -> m a -> m a
addRecordMismatchInfo s m = catchError m $ \case
    RecordMismatch es -> throwError $ RecordMismatch (s:es)
    e                 -> throwError e

throwAesonError :: MonadError (ResumableError e) m => String -> m a
throwAesonError = throwError . AesonError

runStepWriter :: (MonadWriter o m) => Step i o a -> i -> m (Maybe a)
runStepWriter s i = case runStep s i of
    Left o  -> writer (Nothing, o)
    Right a -> pure (Just a)

mapStep :: (forall b. f b -> g b) -> Resumable e f a -> Resumable e g a
mapStep f = \case
    CMap f' c -> CMap f' (mapStep f c)
    CAp l r -> CAp (mapStep f l) (mapStep f r)
    CAlt l r -> CAlt (mapStep f l) (mapStep f r)
    CEmpty -> CEmpty
    CBind l f' -> CBind (mapStep f l) (fmap (mapStep f) f')
    CStep con -> CStep (f con)
    CJSONCheckpoint c -> CJSONCheckpoint (mapStep f c)
    CError e -> CError e

-- | Transform any exceptions thrown by the 'Resumable' using the given function.
withResumableError :: (e -> e') -> Resumable e f a -> Resumable e' f a
withResumableError f = \case
    CMap f' c -> CMap f' (withResumableError f c)
    CAp l r -> CAp (withResumableError f l) (withResumableError f r)
    CAlt l r -> CAlt (withResumableError f l) (withResumableError f r)
    CEmpty -> CEmpty
    CBind l f' -> CBind (withResumableError f l) (fmap (withResumableError f) f')
    CStep con -> CStep con
    CJSONCheckpoint c -> CJSONCheckpoint (withResumableError f c)
    CError e -> CError (f e)

initialise
    :: forall o e i m a.
    ( MonadError (ResumableError e) m
    , MonadWriter o m )
    => Resumable e (Step (Maybe i) o) a
    -> m (Either (OpenRecord i) (ClosedRecord i, a))
initialise con = addRecordMismatchInfo ("initialise on: " <> pretty con) $ case con of
    CMap f con' -> fmap (fmap f) <$> initialise con'
    CAp conL conR -> do
        l' <- initialise conL
        r' <- initialise conR
        case (l', r') of
            (Left l, Left r)             -> pure $ Left (OpenBoth l r)
            (Right (l, _), Left r)       -> pure $ Left (OpenRight l r)
            (Left l, Right (r, _))       -> pure $ Left (OpenLeft l r)
            (Right (l, f), Right (r, a)) -> pure $ Right (ClosedBin l r, f a)
    CAlt conL conR -> do
        (l', wl) <- runWriterT (initialise conL)
        (r', wr) <- runWriterT (initialise conR)
        case (l', r') of
            (Right (_, a), _) -> pure $ Right (ClosedAlt (Left (ClosedLeaf (FinalEvents Nothing))), a)
            (_, Right (_, a)) -> pure $ Right (ClosedAlt (Right (ClosedLeaf (FinalEvents Nothing))), a)
            (Left l, Left r)  -> writer (Left (OpenBoth l r), wl <> wr)
    CBind c f -> do
        l <- initialise c
        case l of
            Left l' -> pure $ Left (OpenBind l')
            Right (l', a) -> do
                r <- initialise (f a)
                case r of
                    Left r'       -> pure $ Left $ OpenRight l' r'
                    Right (r', b) -> pure $ Right (ClosedBin l' r', b)
    CEmpty -> pure (Left $ OpenLeaf Nothing)
    CStep con' -> do
        con'' <- runStepWriter con' Nothing
        case con'' of
            Nothing -> pure $ Left $ OpenLeaf Nothing
            Just a  -> pure $ Right (ClosedLeaf (FinalEvents Nothing), a)
    CJSONCheckpoint con' -> do
        r <- initialise con'
        case r of
            Left _       -> pure r
            Right (_, a) -> pure $ Right (jsonLeaf a, a)
    CError e -> throwError (OtherError e)

checkpoint :: (Aeson.FromJSON a, Aeson.ToJSON a) => Resumable e f a -> Resumable e f a
checkpoint = CJSONCheckpoint

step :: f a -> Resumable e f a
step = CStep

pretty :: Resumable e f a -> String
pretty = \case
    CMap _ c -> "cmap (" ++ pretty c ++ ")"
    CAp l r -> "cap (" ++ pretty l ++ ") (" ++ pretty r ++ ")"
    CBind l _ -> "cbind (" ++ pretty l ++  ") f"
    CStep _ -> "ccontract"
    CAlt l r -> "calt (" ++ pretty l ++ ") (" ++ pretty r ++ ")"
    CEmpty -> "cempty"
    CJSONCheckpoint j -> "json(" ++ pretty j ++ ")"
    CError _ -> "error"

instance Functor (Resumable e f) where
    fmap = CMap

instance Applicative f => Applicative (Resumable e f) where
    pure = CStep . pure
    (<*>) = CAp

instance Applicative f => Alternative (Resumable e f) where
    empty = CEmpty
    (<|>) = CAlt

instance Applicative f => MonadPlus (Resumable e f) where
    mzero = empty
    mplus = (<|>)

instance Applicative f => Monad (Resumable e f) where
    (>>=) = CBind

instance Applicative f => MonadError e (Resumable e f) where
    throwError = CError
    catchError m f = case m of
        CError e -> f e
        _        -> m

-- | Interpret a 'Resumable' program in some other monad.
lowerM
    :: (Monad m, Alternative m, MonadError e m)
    => (forall a'. (Aeson.FromJSON a', Aeson.ToJSON a') => m a' -> m a')
    -- ^ What to do with JSON checkpoints
    -> (forall a'. f a' -> m a')
    -- ^ What to do with the steps
    -> Resumable e f a
    -> m a
lowerM fj fc = \case
    CMap f c' -> f <$> lowerM fj fc c'
    CAp l r -> lowerM fj fc l <*> lowerM fj fc r
    CBind c' f -> lowerM fj fc c' >>= fmap (lowerM fj fc) f
    CAlt l r -> lowerM fj fc l <|> lowerM fj fc r
    CEmpty -> empty
    CStep c' -> fc c'
    CJSONCheckpoint c' -> fj (lowerM fj fc c')
    CError e -> throwError e

-- | Run a resumable program on a closed record to obtain the final result.
--   Note that unlike 'runOpen', 'runClosed' does not have a 'MonadWriter'
--   constraint. This reflects the fact that a finished program is not waiting
--   for any inputs.
runClosed
    :: ( MonadError (ResumableError e) m )
    => Resumable e (Step (Maybe i) o) a
    -> ClosedRecord i
    -> m a
runClosed con rc = addRecordMismatchInfo ("runClosed on: " <> pretty con) $
    case con of
        CMap f c' -> fmap f (runClosed c' rc)
        _ -> case rc of
                ClosedLeaf (FinalEvents evt) ->
                    case con of
                        CStep con' -> do
                            let r = runStep con' evt
                            case r of
                                Left _ ->
                                    throwRecordmismatchError "ClosedLeaf, contract not finished"
                                Right a  ->
                                    pure a
                        _ -> throwRecordmismatchError "ClosedLeaf, expected CStep "
                ClosedLeaf (FinalJSON vl) ->
                    case con of
                        CJSONCheckpoint _ ->
                            case Aeson.parseEither Aeson.parseJSON vl of
                                Left e    -> throwAesonError e
                                Right vl' -> pure vl'
                        _ -> throwRecordmismatchError ("Expected JSON checkpoint, got " ++ pretty con)
                ClosedAlt e ->
                    case con of
                        CAlt conL conR -> either (runClosed conL) (runClosed conR) e
                        _              -> throwRecordmismatchError ("ClosedAlt with wrong contract type: " ++ pretty con)

                ClosedBin l r ->
                    case con of
                        CMap f con' -> fmap f (runClosed con' (ClosedBin l r))
                        CAp l' r'   -> runClosed l' l <*> runClosed r' r
                        CBind l' f  -> runClosed l' l >>= flip runClosed r . f
                        o           -> throwRecordmismatchError ("ClosedBin with wrong contract type: " ++ pretty o)

-- | 'RunOpenProgress' indicats whether progress was made when running a 
--   resumable program on an open record. Progress was made if one of the 
--   branches of the open record switched from open to closed.
data RunOpenProgress = 
    Progress 
    | NoProgress

-- | Run an unfinished resumable program on an open record,
--   throwing an error if any progress is made.
runOpenNoProgress
    :: ( MonadWriter o m
       , MonadError (ResumableError e) m)
    => Resumable e (Step (Maybe i) o) a
    -> OpenRecord i
    -> m ()
runOpenNoProgress con opr = do
    result <- runOpen con opr
    case result of
        Left (_, NoProgress) -> pure ()
        _                    -> throwError ProgressError
    -- TODO: The sole purpose of 'runOpenNoProgress' is to run the 'MonadWriter'
    --       effects. But every time we call 'runOpenNoProgress', 'runOpen con 
    --       opr' has already been run before. If we could store the 
    --       'o' that it produced in the record then we can avoid 
    --       'runOpenNoProgress' altogether.

runOpenRightNoProgress
    :: ( MonadWriter o m
       , MonadError (ResumableError e) m)
    => Resumable e (Step (Maybe i) o) a
    -> OpenRecord i
    -> OpenRecord i
    -> m (OpenRecord i, RunOpenProgress)
runOpenRightNoProgress r oL oR = do
    let oR' = clear oR
    runOpenNoProgress r oR'
    pure (OpenBoth oL oR', Progress)

-- | Run an unfinished resumable program on an open record. Returns the updated
--   record.
runOpen
    :: ( MonadWriter o m
       , MonadError (ResumableError e) m)
    => Resumable e (Step (Maybe i) o) a
    -> OpenRecord i
    -> m (Either (OpenRecord i, RunOpenProgress) (ClosedRecord i, a))
runOpen con opr =
    case (con, opr) of
        (CMap f con', _) -> (fmap .fmap $ fmap f) (runOpen con' opr)
        (CAp l r, OpenLeft opr' cr) -> do
            lr <- runOpen l opr'
            rr <- runClosed r cr
            case lr of
                Left (opr'', prog)     -> pure (Left (OpenLeft opr'' cr, prog))
                Right (cr', a) -> pure (Right (ClosedBin cr' cr, a rr))
        (CAp l r, OpenRight cr opr') -> do
            lr <- runClosed l cr
            rr <- runOpen r opr'
            case rr of
                Left (opr'', prog) -> pure (Left (OpenRight cr opr'', prog))
                Right (cr', a)     -> pure (Right (ClosedBin cr cr', lr a))
        (CAp l r, OpenBoth orL orR) -> do
            -- we only need to update the right branch if no progress was made
            -- in the left branch. So we run the left branch first, look at the
            -- result, and then run the right branch if necessary.
            lr <- runOpen l orL
            case lr of
                Right (crL, _) -> do
                    let oR' = clear orR
                    runOpenNoProgress r oR'
                    pure (Left (OpenRight crL oR', Progress))
                Left (oL, Progress) -> Left <$> runOpenRightNoProgress r oL orR
                Left (oL, NoProgress) -> do
                    rr <- runOpen r orR
                    case rr of
                        Right (cR, _) -> pure (Left (OpenLeft orL cR, Progress))
                        Left (oR, pR) -> pure (Left (OpenBoth oL oR, pR))

        (CAp{}, OpenLeaf _) -> throwRecordmismatchError "CAp OpenLeaf"

        (CAlt l r, OpenBoth orL orR) -> do
            -- If one of the two branches is done then we need to
            -- discard the requests of the other branch. So we evaluate
            -- both of them in 'runWriterT'.
            (lr, wl) <- runWriterT (runOpen l orL)
            case lr of
                Right (crL, a) -> pure (Right (ClosedAlt (Left crL), a))
                Left (oL, Progress) -> do
                    tell wl
                    Left <$> runOpenRightNoProgress r oL orR
                Left (oL, NoProgress) -> do
                    (rr, wr) <- runWriterT (runOpen r orR)
                    case rr of
                        Right (cR, a) -> pure (Right (ClosedAlt (Right cR), a))
                        Left (oR, pR) -> writer (Left (OpenBoth oL oR, pR), wl <> wr)

        (CAlt{}, OpenLeaf _) -> throwRecordmismatchError "CAlt OpenLeaf"

        (CBind c f, OpenBind bnd) -> do
            lr <- runOpen c bnd
            case lr of
                Left (orL', prog) -> pure $ Left (OpenBind orL', prog)
                Right (crL, a) -> do
                    let con' = f a
                    orR' <- initialise con'
                    case orR' of
                        Right (crrrr, a') -> pure (Right (ClosedBin crL crrrr, a'))
                        Left orrrr        -> pure (Left (OpenRight crL orrrr, Progress))

        (CBind c f, OpenRight cr opr') -> do
            lr <- runClosed c cr
            rr <- runOpen (f lr) opr'
            case rr of
                Left (opr'', prog)     -> pure (Left (OpenRight cr opr'', prog))
                Right (cr', a) -> pure (Right (ClosedBin cr cr', a))
        (CBind{}, _) -> throwRecordmismatchError "CBind"

        (CStep con', OpenLeaf evt) -> do
                r <- runStepWriter con' evt
                case r of
                    Just a  -> pure $ Right (ClosedLeaf (FinalEvents evt), a)
                    Nothing -> pure $ Left (OpenLeaf evt, NoProgress)
        (CStep{}, _) -> throwRecordmismatchError "CStep non leaf "

        (CJSONCheckpoint con', opr') ->
            fmap (\(_, a) -> (jsonLeaf a, a)) <$> runOpen con' opr'
        _ -> throwRecordmismatchError "runOpen"

-- | The result of running a 'Resumable'
data ResumableResult i o a =
    ResumableResult
        { wcsRecord     :: Record i -- The record with the resumable's execution history
        , wcsHandlers   :: o -- Handlers that the 'Resumable' has registered
        , wcsFinalState :: Maybe a -- Final state of the 'Resumable'
        }

insertAndUpdate
    :: Monoid o
    => Resumable e (Step (Maybe i) o) a
    -> Record i
    -> i
    -> Either (ResumableError e) (ResumableResult i o a)
insertAndUpdate con rc e = updateRecord con (insert e rc)

updateRecord
    :: forall a e i o. Monoid o
    => Resumable e (Step (Maybe i) o) a
    -> Record i
    -> Either (ResumableError e) (ResumableResult i o a)
updateRecord con rc =
    case rc of
        ClosedRec cl ->
            fmap (\(a, _) -> ResumableResult { wcsRecord = ClosedRec cl, wcsHandlers = mempty, wcsFinalState = Just a })
            $ runExcept
            $ runWriterT @o
            $ runClosed con cl
        OpenRec cl  ->
            let mkResult (Left openRec, o) = 
                    ResumableResult { wcsRecord = OpenRec openRec, wcsHandlers = o, wcsFinalState = Nothing }
                mkResult (Right (closedrec, a), o) =
                    ResumableResult { wcsRecord = ClosedRec closedrec, wcsHandlers = o, wcsFinalState = Just a} 
            in fmap mkResult
            $ runExcept
            $ runWriterT
            $ fmap (first fst) (runOpen con cl)

execResumable
    :: Monoid o
    => [i]
    -> Resumable e (Step (Maybe i) o) a
    -> Either (ResumableError e) o
execResumable es = fmap wcsHandlers . runResumable es

runResumable
    :: Monoid o
    => [i]
    -> Resumable e (Step (Maybe i) o) a
    -> Either (ResumableError e) (ResumableResult i o a)
runResumable es con = do
    initial <- runExcept $ runWriterT (initialise con)
    let go r e =
            let r' = over (from record) (insert e) (fst <$> fst r)
                result = case r' of
                    Left open -> 
                        runExcept 
                        $ runWriterT 
                        $ fmap (first fst) (runOpen con open)
                    Right closed -> 
                        fmap (\(a, h) -> (Right (closed, a), h))
                        $ runExcept 
                        $ runWriterT 
                        $ runClosed con closed
            in result
    foldM go initial es >>= \case
        (Left openRec, o) -> pure ResumableResult{wcsRecord=OpenRec openRec, wcsHandlers = o, wcsFinalState = Nothing}
        (Right (cr, a), o) -> pure ResumableResult{wcsRecord=ClosedRec cr, wcsHandlers = o, wcsFinalState = Just a}
