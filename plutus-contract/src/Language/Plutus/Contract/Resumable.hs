{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
-- | A version of 'Language.Plutus.Contract.Contract' that
--   writes checkpoints.
module Language.Plutus.Contract.Resumable(
    Resumable
    , ResumableError(..)
    , Step(..)
    , step
    , checkpoint
    , pretty
    , lowerM
    , mapStep
    -- * Records
    , initialise
    , insertAndUpdate
    , updateRecord
    , execResumable
    , runResumable
    ) where

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.Morph
import           Control.Monad.Writer
import qualified Data.Aeson                      as Aeson
import qualified Data.Aeson.Types                as Aeson
import           Data.Bifunctor                  (Bifunctor (..))

import           Language.Plutus.Contract.Record

{- Note [Handling state in contracts]

The 'Resumable' type encodes programs with a serialisable state that operate on
event streams. 'Resumable (Step i o)' consumes inputs of type 'i' and produces
requests (describing the inputs that are expected next) of type 'o'. As such,
'Resumable (Step i o)' is similar to the @Prompt i o@ type found in the
@prompt@ package.

Unlike the 'Prompt' type however, 'Resumable (Step i o)' programs have a
builtin way of serialising their state *efficiently*: While we can always take
the state of a stream-consuming program to be the list of events it has seen so
far, we have to replay all the previous events every time a new event is
received, making the complexity of recovering the current state from the event
list quadratic.

We avoid this in 'Resumable (Step i o)' by adding checkpoints at which the state can be serialised and resumed without having to replay all the previous
events.

The current state of 'Resumable (Step i o)' programs is captured by the 'Record
i' type. Every 'Record' is a tree with branches that match the structure of the
'Resumable' program whose state it represents.

Given a 'Resumable (Step i o)'  we can use 'initialise' to get the initial
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

-- | A resumable program made up of 'Step's.
data Resumable f a where
    CMap :: (a' -> a) -> Resumable f a' -> Resumable f a
    CAp :: Resumable f (a' -> a) -> Resumable f a' -> Resumable f a
    CAlt :: Resumable f a -> Resumable f a -> Resumable f a
    CEmpty :: Resumable f a
    CBind :: Resumable f a' -> (a' -> Resumable f a) -> Resumable f a

    CStep :: f a -> Resumable f a
    CJSONCheckpoint :: (Aeson.FromJSON a, Aeson.ToJSON a) => Resumable f a -> Resumable f a

instance MFunctor Resumable where
    hoist = mapStep

-- | An error that can occur when updating a 'Record' using a
--   'Resumable (Step i o)'.
data ResumableError =
    RecordMismatch String
    -- ^ The structure of the record does not match the structure of the
    --   'Resumable'.
    | AesonError String
    -- ^ Something went wrong while decoding a JSON value
    deriving (Eq, Ord, Show)

throwRecordmismatchError :: MonadError ResumableError m => String -> m a
throwRecordmismatchError = throwError . RecordMismatch

throwAesonError :: MonadError ResumableError m => String -> m a
throwAesonError = throwError . AesonError

runStepWriter :: (MonadWriter o m, MonadError ResumableError m) => Step i (Either String o) a -> i -> m (Maybe a)
runStepWriter s i = case runStep s i of
    Left (Left e)  -> throwAesonError e
    Left (Right o) -> writer (Nothing, o)
    Right a        -> pure (Just a)

mapStep :: (forall b. f b -> g b) -> Resumable f a -> Resumable g a
mapStep f = \case
    CMap f' c -> CMap f' (mapStep f c)
    CAp l r -> CAp (mapStep f l) (mapStep f r)
    CAlt l r -> CAlt (mapStep f l) (mapStep f r)
    CEmpty -> CEmpty
    CBind l f' -> CBind (mapStep f l) (fmap (mapStep f) f')
    CStep con -> CStep (f con)
    CJSONCheckpoint c -> CJSONCheckpoint (mapStep f c)

initialise
    :: ( MonadError ResumableError m
       , MonadWriter o m )
    => Resumable (Step (Maybe i) (Either String o)) a
    -> m (Either (OpenRecord i) (ClosedRecord i, a))
initialise = \case
    CMap f con -> fmap (fmap f) <$> initialise con
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
            (Right (_, a), _) -> pure $ Right (ClosedLeaf (FinalEvents Nothing), a)
            (_, Right (_, a)) -> pure $ Right (ClosedLeaf (FinalEvents Nothing), a)
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
    CStep con -> do
        con' <- runStepWriter con Nothing
        case con' of
            Nothing -> pure $ Left $ OpenLeaf Nothing
            Just a  -> pure $ Right (ClosedLeaf (FinalEvents Nothing), a)
    CJSONCheckpoint con -> do
        r <- initialise con
        case r of
            Left _       -> pure r
            Right (_, a) -> pure $ Right (jsonLeaf a, a)

checkpoint :: (Aeson.FromJSON a, Aeson.ToJSON a) => Resumable f a -> Resumable f a
checkpoint = CJSONCheckpoint

step :: f a -> Resumable f a
step = CStep

pretty :: Resumable f a -> String
pretty = \case
    CMap _ c -> "cmap (" ++ pretty c ++ ")"
    CAp l r -> "cap (" ++ pretty l ++ ") (" ++ pretty r ++ ")"
    CBind l _ -> "cbind (" ++ pretty l ++  ") f"
    CStep _ -> "ccontract"
    CAlt l r -> "calt (" ++ pretty l ++ ") (" ++ pretty r ++ ")"
    CEmpty -> "cempty"
    CJSONCheckpoint j -> "json(" ++ pretty j ++ ")"

instance Functor (Resumable f) where
    fmap = CMap

instance Applicative f => Applicative (Resumable f) where
    pure = CStep . pure
    (<*>) = CAp

instance Applicative f => Alternative (Resumable f) where
    empty = CEmpty
    (<|>) = CAlt

instance Applicative f => Monad (Resumable f) where
    (>>=) = CBind

-- | Interpret a 'Resumable' program in some other monad.
lowerM
    :: (Monad m, Alternative m)
    -- ^ What to do with map, ap, bind
    => (forall a'. (Aeson.FromJSON a', Aeson.ToJSON a') => m a' -> m a')
    -- ^ What to do with JSON checkpoints
    -> (forall a'. f a' -> m a')
    -- ^ What to do with the steps
    -> Resumable f a
    -> m a
lowerM fj fc = \case
    CMap f c' -> f <$> lowerM fj fc c'
    CAp l r -> lowerM fj fc l <*> lowerM fj fc r
    CBind c' f -> lowerM fj fc c' >>= fmap (lowerM fj fc) f
    CAlt l r -> lowerM fj fc l <|> lowerM fj fc r
    CEmpty -> empty
    CStep c' -> fc c'
    CJSONCheckpoint c' -> fj (lowerM fj fc c')

-- | Run a resumable program on a closed record to obtain the final result.
--   Note that unlike 'runOpen', 'runClosed' does not have a 'MonadWriter'
--   constraint. This reflects the fact that a finished program is not waiting
--   for any inputs.
runClosed
    :: ( MonadError ResumableError m )
    => Resumable (Step (Maybe i) (Either String o)) a
    -> ClosedRecord i
    -> m a
runClosed con rc =
    case con of
        CMap f c' -> fmap f (runClosed c' rc)
        _ -> case rc of
                ClosedLeaf (FinalEvents evt) ->
                    case con of
                        CStep con' -> do
                            let r = runStep con' evt
                            case r of
                                Left (Left err) ->
                                    throwAesonError err
                                Left (Right _) ->
                                    throwRecordmismatchError "ClosedLeaf, contract not finished"
                                Right a  -> pure a
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
                        CAp l' r'   -> runClosed l' l <*> runClosed r' l
                        CBind l' f  -> runClosed l' l >>= flip runClosed r . f
                        o           -> throwRecordmismatchError ("ClosedBin with wrong contract type: " ++ pretty o)

-- | Run an unfinished resumable program on an open record. Returns the updated
--   record.
runOpen
    :: ( MonadWriter o m
       , MonadError ResumableError m)
    => Resumable (Step (Maybe i) (Either String o)) a
    -> OpenRecord i
    -> m (Either (OpenRecord i) (ClosedRecord i, a))
runOpen con opr =
    case (con, opr) of
        (CMap f con', _) -> (fmap .fmap $ fmap f) (runOpen con' opr)
        (CAp l r, OpenLeft opr' cr) -> do
            lr <- runOpen l opr'
            rr <- runClosed r cr
            case lr of
                Left opr''     -> pure (Left (OpenLeft opr'' cr))
                Right (cr', a) -> pure (Right (ClosedBin cr' cr, a rr))
        (CAp l r, OpenRight cr opr') -> do
            lr <- runClosed l cr
            rr <- runOpen r opr'
            case rr of
                Left opr''     -> pure (Left (OpenRight cr opr''))
                Right (cr', a) -> pure (Right (ClosedBin cr cr', lr a))
        (CAp l r, OpenBoth orL orR) -> do
            lr <- runOpen l orL
            rr <- runOpen r orR
            case (lr, rr) of
                (Right (crL, a), Right (crR, b)) ->
                    pure (Right (ClosedBin crL crR, a b))
                (Right (crL, _), Left oR) ->
                    pure (Left (OpenRight crL oR))
                (Left oL, Right (cR, _)) ->
                    pure (Left (OpenLeft oL cR))
                (Left oL, Left oR) ->
                    pure (Left (OpenBoth oL oR))
        (CAp{}, OpenLeaf _) -> throwRecordmismatchError "CAp OpenLeaf"

        (CAlt l r, OpenBoth orL orR) -> do
            -- If one of the two branches is done then we need to
            -- discard the requests of the other branch. So we evaluate
            -- both of them in 'runWriterT'.
            (lr, wl) <- runWriterT (runOpen l orL)
            (rr, wr) <- runWriterT (runOpen r orR)
            case (lr, rr) of
                (Right (crL, a), _) -> pure (Right (ClosedAlt (Left crL), a))
                (_, Right (crR, a)) -> pure (Right (ClosedAlt (Right crR), a))
                (Left oL, Left oR)  -> writer (Left (OpenBoth oL oR), wl <> wr)
        (CAlt{}, OpenLeaf _) -> throwRecordmismatchError "CAlt OpenLeaf"

        (CBind c f, OpenBind bnd) -> do
            lr <- runOpen c bnd
            case lr of
                Left orL' -> pure (Left $ OpenBind orL')
                Right (crL, a) -> do
                    let con' = f a
                    orR' <- initialise con'
                    case orR' of
                        Right (crrrr, a') -> pure (Right (ClosedBin crL crrrr, a'))
                        Left orrrr        -> pure (Left (OpenRight crL orrrr))

        (CBind c f, OpenRight cr opr') -> do
            lr <- runClosed c cr
            rr <- runOpen (f lr) opr'
            case rr of
                Left opr''     -> pure (Left (OpenRight cr opr''))
                Right (cr', a) -> pure (Right (ClosedBin cr cr', a))
        (CBind{}, _) -> throwRecordmismatchError "CBind"

        (CStep con', OpenLeaf evt) -> do
                r <- runStepWriter con' evt
                case r of
                    Just a  -> pure $ Right (ClosedLeaf (FinalEvents evt), a)
                    Nothing -> pure $ Left (OpenLeaf evt)
        (CStep{}, _) -> throwRecordmismatchError "CStep non leaf "

        (CJSONCheckpoint con', opr') ->
            fmap (\(_, a) -> (jsonLeaf a, a)) <$> runOpen con' opr'
        _ -> throwRecordmismatchError "runOpen"

insertAndUpdate
    :: Monoid o
    => Resumable (Step (Maybe i) (Either String o)) a
    -> Record i
    -> i
    -> Either ResumableError (Record i, o)
insertAndUpdate con rc e = updateRecord con (insert e rc)

updateRecord
    :: Monoid o
    => Resumable (Step (Maybe i) (Either String o)) a
    -> Record i
    -> Either ResumableError (Record i, o)
updateRecord con rc =
    case rc of
        Right cl ->
            fmap (first $ const $ Right cl)
            $ runExcept
            $ runWriterT
            $ runClosed con cl
        Left cl  ->
            fmap (first (fmap fst))
            $ runExcept
            $ runWriterT
            $ runOpen con cl

execResumable :: Monoid o => [i] -> Resumable (Step (Maybe i) (Either String o)) a -> Either ResumableError o
execResumable es = fmap snd . runResumable es

runResumable :: Monoid o => [i] -> Resumable (Step (Maybe i) (Either String o)) a -> Either ResumableError (Either (OpenRecord i) (ClosedRecord i, a), o)
runResumable es con = do
    initial <- runExcept $ runWriterT (initialise con)
    foldM go initial es where
        go r e =
            let r' = insert e (fst <$> fst r)
                result = case r' of
                            Left open -> runExcept $ runWriterT $ runOpen con open
                            Right closed -> fmap (\(a, h) -> (Right (closed, a), h)) $ runExcept $ runWriterT $ runClosed con closed
            in result
