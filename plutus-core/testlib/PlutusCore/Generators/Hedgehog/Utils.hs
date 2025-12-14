{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

-- | Utilities used in modules from the @TestSupport@ folder.
module PlutusCore.Generators.Hedgehog.Utils
  ( liftT
  , generalizeT
  , hoistSupply
  , choiceDef
  , forAllNoShow
  , forAllNoShowT
  , forAllPretty
  , forAllPrettyT
  , forAllPrettyPlc
  , forAllPrettyPlcT
  , prettyPlcErrorString
  ) where

import PlutusCore.Pretty

import Control.Monad.Morph
import Control.Monad.Reader
import Data.Functor.Identity
import Hedgehog hiding (Size, Var)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Internal.Property (forAllWithT)

-- | @hoist lift@
liftT :: (MFunctor t, MonadTrans s, Monad m) => t m a -> t (s m) a
liftT = hoist lift

-- | @hoist generalize@
generalizeT :: (MFunctor t, Monad m) => t Identity a -> t m a
generalizeT = hoist generalize

-- | Supply an environment to an inner 'ReaderT'.
hoistSupply :: (MFunctor t, Monad m) => r -> t (ReaderT r m) a -> t m a
hoistSupply r = hoist $ flip runReaderT r

{-| Same as 'Gen.choice', but with a default generator to be used
when the supplied list of generators is empty. -}
choiceDef :: Monad m => GenT m a -> [GenT m a] -> GenT m a
choiceDef a [] = a
choiceDef _ as = Gen.choice as

-- | Generate a value, but do not show it in case an error occurs.
forAllNoShow :: Monad m => Gen a -> PropertyT m a
forAllNoShow = forAllWith mempty

{-| Generate a value, but do not show it in case an error occurs.
A supplied generator has access to the 'Monad' the whole property has access to. -}
forAllNoShowT :: Monad m => GenT m a -> PropertyT m a
forAllNoShowT = forAllWithT mempty

-- | Generate a value using the 'Pretty' class for getting its 'String' representation.
forAllPretty :: (Monad m, Pretty a) => Gen a -> PropertyT m a
forAllPretty = forAllWith display

{-| Generate a value using the 'Pretty' class for getting its 'String' representation.
A supplied generator has access to the 'Monad' the whole property has access to. -}
forAllPrettyT :: (Monad m, Pretty a) => GenT m a -> PropertyT m a
forAllPrettyT = forAllWithT display

-- | Generate a value using the 'PrettyPlc' constraint for getting its 'String' representation.
forAllPrettyPlc :: (Monad m, PrettyPlc a) => Gen a -> PropertyT m a
forAllPrettyPlc = forAllWith displayPlc

{-| Generate a value using the 'PrettyPlc' constraint for getting its 'String' representation.
A supplied generator has access to the 'Monad' the whole property has access to. -}
forAllPrettyPlcT :: (Monad m, PrettyPlc a) => GenT m a -> PropertyT m a
forAllPrettyPlcT = forAllWithT displayPlc

-- | Pretty-print a PLC error.
prettyPlcErrorString :: PrettyPlc err => err -> String
prettyPlcErrorString = render . prettyPlcCondensedErrorBy prettyConfigPlcClassicSimple
