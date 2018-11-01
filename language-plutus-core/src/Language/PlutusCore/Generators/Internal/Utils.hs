-- | Utilities used in modules from the @TestSupport@ folder.

{-# LANGUAGE GADTs      #-}
{-# LANGUAGE RankNTypes #-}

module Language.PlutusCore.Generators.Internal.Utils
    ( liftT
    , hoistSupply
    , choiceDef
    , forAllNoShow
    , forAllNoShowT
    , forAllPretty
    , forAllPrettyT
    , forAllPrettyPlc
    , forAllPrettyPlcT
    , forAllPrettyPlcMaybe
    , forAllPrettyPlcMaybeT
    , runQuoteSampleSucceed
    , errorPlc
    ) where

import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote  (Quote, runQuote)

import           Control.Monad.Morph
import           Control.Monad.Reader
import           Hedgehog                   hiding (Size, Var)
import qualified Hedgehog.Gen               as Gen
import           Hedgehog.Internal.Property (forAllWithT)

-- | @hoist lift@
liftT :: (MFunctor t, MonadTrans s, Monad m) => t m a -> t (s m) a
liftT = hoist lift

-- | Supply an environment to an inner 'ReaderT'.
hoistSupply :: (MFunctor t, Monad m) => r -> t (ReaderT r m) a -> t m a
hoistSupply r = hoist $ flip runReaderT r

-- | Same as 'Gen.choice', but with a default generator to be used
-- when the supplied list of generators is empty.
choiceDef :: Monad m => GenT m a -> [GenT m a] -> GenT m a
choiceDef a [] = a
choiceDef _ as = Gen.choice as

-- | Generate a value, but do not show it in case an error occurs.
forAllNoShow :: Monad m => Gen a -> PropertyT m a
forAllNoShow = forAllWith mempty

-- | Generate a value, but do not show it in case an error occurs.
-- A supplied generator has access to the 'Monad' the whole property has access to.
forAllNoShowT :: Monad m => GenT m a -> PropertyT m a
forAllNoShowT = forAllWithT mempty

-- | Generate a value using the 'Pretty' class for getting its 'String' representation.
forAllPretty :: (Monad m, Pretty a) => Gen a -> PropertyT m a
forAllPretty = forAllWith prettyString

-- | Generate a value using the 'Pretty' class for getting its 'String' representation.
-- A supplied generator has access to the 'Monad' the whole property has access to.
forAllPrettyT :: (Monad m, Pretty a) => GenT m a -> PropertyT m a
forAllPrettyT = forAllWithT prettyString

-- | Generate a value using the 'PrettyPlc' constraint for getting its 'String' representation.
forAllPrettyPlc :: (Monad m, PrettyPlc a) => Gen a -> PropertyT m a
forAllPrettyPlc = forAllWith prettyPlcDefString

-- | Generate a value using the 'PrettyPlc' constraint for getting its 'String' representation.
-- A supplied generator has access to the 'Monad' the whole property has access to.
forAllPrettyPlcT :: (Monad m, PrettyPlc a) => GenT m a -> PropertyT m a
forAllPrettyPlcT = forAllWithT prettyPlcDefString

-- | Generate a value wrapped in 'Maybe' using the 'PrettyPlc' constraint
-- for getting its 'String' representation.
forAllPrettyPlcMaybe :: (Monad m, PrettyPlc a) => Gen (Maybe a) -> PropertyT m (Maybe a)
forAllPrettyPlcMaybe = forAllWith $ maybe "Nothing" prettyPlcDefString

-- | Generate a value wrapped in 'Maybe' using the 'PrettyPlc' constraint
-- for getting its 'String' representation.
-- A supplied generator has access to the 'Monad' the whole property has access to.
forAllPrettyPlcMaybeT :: (Monad m, PrettyPlc a) => GenT m (Maybe a) -> PropertyT m (Maybe a)
forAllPrettyPlcMaybeT = forAllWithT $ maybe "Nothing" prettyPlcDefString

-- | Run a generator until it succeeds with a 'Just'.
runQuoteSampleSucceed :: GenT Quote (Maybe a) -> IO a
runQuoteSampleSucceed = Gen.sample . Gen.just . hoist (pure . runQuote)

-- | Throw a PLC error.
errorPlc :: PrettyPlc err => err -> b
errorPlc = error . docString . prettyPlcCondensedErrorBy debugPrettyConfigPlcClassic
