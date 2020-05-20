{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}

module Text.PrettyBy.Internal.Core
    ( PrettyBy (..)
    , IgnorePrettyConfig (..)
    , AttachPrettyConfig (..)
    , withAttachPrettyConfig
    , defaultPrettyFunctorBy
    , defaultPrettyBifunctorBy
    , DefaultPrettyBy (..)
    , NonDefaultPrettyBy (..)
    , HasPrettyDefaults
    , DefaultlyPretty (..)
    ) where

import           Data.Bifunctor
import           Data.Functor.Const
import           Data.Coerce
import           Data.Functor.Identity
import           Data.Int
import           Data.List.NonEmpty (NonEmpty (..))
import           Data.Maybe
import           Data.Proxy
import qualified Data.Text                          as Strict
import qualified Data.Text.Lazy                     as Lazy
import           Data.Text.Prettyprint.Doc
import           Data.Void
import           Data.Word
import           GHC.Natural

-- **********
-- ** Core **
-- **********

class PrettyBy config a where
    prettyBy :: config -> a -> Doc ann
    default prettyBy :: Pretty a => config -> a -> Doc ann
    prettyBy _ = pretty

    prettyListBy :: config -> [a] -> Doc ann
    default prettyListBy :: config -> [a] -> Doc ann
    prettyListBy = defaultPrettyFunctorBy

-- Interop with 'Pretty'.

-- | A newtype wrapper around @a@ whose point is to provide a @PrettyBy config@ instance
-- for anything that has a 'Pretty' instance.
newtype IgnorePrettyConfig a = IgnorePrettyConfig
    { unIgnorePrettyConfig :: a
    } deriving newtype (Pretty)
      deriving anyclass (PrettyBy config)

-- | A config together with some value. The point is to provide a 'Pretty' instance
-- for anything that has a @PrettyBy config@ instance.
data AttachPrettyConfig config a = AttachPrettyConfig !config !a

instance PrettyBy config a => Pretty (AttachPrettyConfig config a) where
    pretty (AttachPrettyConfig config x) = prettyBy config x

withAttachPrettyConfig
    :: config -> ((forall a. a -> AttachPrettyConfig config a) -> r) -> r
withAttachPrettyConfig config k = k $ AttachPrettyConfig config

-- **************
-- ** Defaults **
-- **************

defaultPrettyFunctorBy
    :: (Functor f, Pretty (f (AttachPrettyConfig config a)))
    => config -> f a -> Doc ann
defaultPrettyFunctorBy config a =
    pretty $ AttachPrettyConfig config <$> a

defaultPrettyBifunctorBy
    :: (Bifunctor f, Pretty (f (AttachPrettyConfig config a) (AttachPrettyConfig config b)))
    => config -> f a b -> Doc ann
defaultPrettyBifunctorBy config a =
    withAttachPrettyConfig config $ \attach -> pretty $ bimap attach attach a

data AttachDefaultPrettyConfig config a = AttachDefaultPrettyConfig !config !a

instance DefaultPrettyBy config a => Pretty (AttachDefaultPrettyConfig config a) where
    pretty (AttachDefaultPrettyConfig config x) = defaultPrettyBy config x

-- The 'DefaultPrettyBy' class and its instances.

class DefaultPrettyBy config a where
    defaultPrettyBy :: config -> a -> Doc ann
    default defaultPrettyBy :: Pretty a => config -> a -> Doc ann
    defaultPrettyBy _ = pretty

    defaultPrettyListBy :: config -> [a] -> Doc ann
    default defaultPrettyListBy :: config -> [a] -> Doc ann
    defaultPrettyListBy config = pretty . map (AttachDefaultPrettyConfig config)

instance PrettyDefaultsBy config Strict.Text => DefaultPrettyBy config Char where
    defaultPrettyListBy config = prettyBy config . Strict.pack

instance PrettyBy config a => DefaultPrettyBy config (Maybe a) where
    defaultPrettyBy = defaultPrettyFunctorBy
    defaultPrettyListBy config = prettyListBy config . catMaybes

instance PrettyBy config a => DefaultPrettyBy config [a] where
    defaultPrettyBy = prettyListBy

instance PrettyBy config a => DefaultPrettyBy config (NonEmpty a) where
    defaultPrettyBy config (x :| xs) = prettyListBy config (x : xs)

instance DefaultPrettyBy config Void
instance DefaultPrettyBy config ()
instance DefaultPrettyBy config Bool
instance DefaultPrettyBy config Natural
instance DefaultPrettyBy config Integer
instance DefaultPrettyBy config Int
instance DefaultPrettyBy config Int8
instance DefaultPrettyBy config Int16
instance DefaultPrettyBy config Int32
instance DefaultPrettyBy config Int64
instance DefaultPrettyBy config Word
instance DefaultPrettyBy config Word8
instance DefaultPrettyBy config Word16
instance DefaultPrettyBy config Word32
instance DefaultPrettyBy config Word64
instance DefaultPrettyBy config Float
instance DefaultPrettyBy config Double
instance DefaultPrettyBy config Strict.Text
instance DefaultPrettyBy config Lazy.Text

instance PrettyBy config a => DefaultPrettyBy config (Identity a) where
    defaultPrettyBy = defaultPrettyFunctorBy

instance (PrettyBy config a, PrettyBy config b) => DefaultPrettyBy config (a, b) where
    defaultPrettyBy = defaultPrettyBifunctorBy

instance (PrettyBy config a, PrettyBy config b, PrettyBy config c) =>
            DefaultPrettyBy config (a, b, c) where
    defaultPrettyBy config (x, y, z) =
        withAttachPrettyConfig config $ \attach -> pretty (attach x, attach y, attach z)

instance PrettyBy config a => DefaultPrettyBy config (Const a b) where
    defaultPrettyBy config a =
        withAttachPrettyConfig config $ \attach -> pretty $ first attach a

-- The 'NonDefaultPrettyBy' class and its none instances.

class NonDefaultPrettyBy config a where
    nonDefaultPrettyBy :: config -> a -> Doc ann
    default nonDefaultPrettyBy :: DefaultPrettyBy config a => config -> a -> Doc ann
    nonDefaultPrettyBy = defaultPrettyBy

    nonDefaultPrettyListBy :: config -> [a] -> Doc ann
    default nonDefaultPrettyListBy :: DefaultPrettyBy config a => config -> [a] -> Doc ann
    nonDefaultPrettyListBy = defaultPrettyListBy

-- ...

type family HasPrettyDefaults config :: Bool

type instance HasPrettyDefaults () = 'True

class HasPrettyDefaults config ~ b => DispatchDefaultPrettyBy (b :: Bool) config a where
    dispatchDefaultPrettyBy     :: proxy b -> config -> a   -> Doc ann
    dispatchDefaultPrettyListBy :: proxy b -> config -> [a] -> Doc ann

instance (HasPrettyDefaults config ~ 'True, DefaultPrettyBy config a) =>
            DispatchDefaultPrettyBy 'True config a where
    dispatchDefaultPrettyBy     _ = defaultPrettyBy
    dispatchDefaultPrettyListBy _ = defaultPrettyListBy

instance (HasPrettyDefaults config ~ 'False, NonDefaultPrettyBy config a) =>
            DispatchDefaultPrettyBy 'False config a where
    dispatchDefaultPrettyBy     _ = nonDefaultPrettyBy
    dispatchDefaultPrettyListBy _ = nonDefaultPrettyListBy

type PrettyDefaultsBy config = DispatchDefaultPrettyBy (HasPrettyDefaults config) config

newtype DefaultlyPretty a = DefaultlyPretty
    { unDefaultlyPretty :: a
    }

coerceDispatcher :: Coercible a b => (config -> a -> Doc ann) -> config -> b -> Doc ann
coerceDispatcher = coerce

instance PrettyDefaultsBy config a => PrettyBy config (DefaultlyPretty a) where
    prettyBy     = coerceDispatcher @a   $ dispatchDefaultPrettyBy     Proxy
    prettyListBy = coerceDispatcher @[a] $ dispatchDefaultPrettyListBy Proxy

-- 'PrettyBy' instances for types supporting default pretty-printing.

-- |
-- >>> prettyBy () ([] :: [Void])
-- []
deriving via DefaultlyPretty Void
    instance PrettyDefaultsBy config Void => PrettyBy config Void

-- |
-- >>> prettyBy () ()
-- ()
--
-- The argument is not used:
--
-- >>> prettyBy () (error "Strict?" :: ())
-- ()
deriving via DefaultlyPretty ()
    instance PrettyDefaultsBy config () => PrettyBy config ()

-- |
-- >>> prettyBy () True
-- True
deriving via DefaultlyPretty Bool
    instance PrettyDefaultsBy config Bool => PrettyBy config Bool

deriving via DefaultlyPretty Natural
    instance PrettyDefaultsBy config Natural => PrettyBy config Natural
deriving via DefaultlyPretty Integer
    instance PrettyDefaultsBy config Integer => PrettyBy config Integer
deriving via DefaultlyPretty Int
    instance PrettyDefaultsBy config Int => PrettyBy config Int
deriving via DefaultlyPretty Int8
    instance PrettyDefaultsBy config Int8 => PrettyBy config Int8
deriving via DefaultlyPretty Int16
    instance PrettyDefaultsBy config Int16 => PrettyBy config Int16
deriving via DefaultlyPretty Int32
    instance PrettyDefaultsBy config Int32 => PrettyBy config Int32
deriving via DefaultlyPretty Int64
    instance PrettyDefaultsBy config Int64 => PrettyBy config Int64
deriving via DefaultlyPretty Word
    instance PrettyDefaultsBy config Word => PrettyBy config Word
deriving via DefaultlyPretty Word8
    instance PrettyDefaultsBy config Word8 => PrettyBy config Word8
deriving via DefaultlyPretty Word16
    instance PrettyDefaultsBy config Word16 => PrettyBy config Word16
deriving via DefaultlyPretty Word32
    instance PrettyDefaultsBy config Word32 => PrettyBy config Word32
deriving via DefaultlyPretty Word64
    instance PrettyDefaultsBy config Word64 => PrettyBy config Word64
deriving via DefaultlyPretty Float
    instance PrettyDefaultsBy config Float => PrettyBy config Float
deriving via DefaultlyPretty Double
    instance PrettyDefaultsBy config Double => PrettyBy config Double
deriving via DefaultlyPretty Strict.Text
    instance PrettyDefaultsBy config Strict.Text => PrettyBy config Strict.Text
deriving via DefaultlyPretty Lazy.Text
    instance PrettyDefaultsBy config Lazy.Text => PrettyBy config Lazy.Text

-- |
--
-- >>> pretty (Identity True)
-- True
deriving via DefaultlyPretty (Identity a)
    instance PrettyDefaultsBy config (Identity a) => PrettyBy config (Identity a)

-- |
-- >>> pretty (False, "abc")
-- (False, abc)
deriving via DefaultlyPretty (a, b)
    instance PrettyDefaultsBy config (a, b) => PrettyBy config (a, b)

-- |
-- >>> pretty ('a', "bcd", True)
-- (a, bcd, True)
deriving via DefaultlyPretty (a, b, c)
    instance PrettyDefaultsBy config (a, b, c) => PrettyBy config (a, b, c)

-- |
-- >>> pretty (Const 1 :: Const Integer Bool)
-- 1
deriving via DefaultlyPretty (Const a b)
    instance PrettyDefaultsBy config (Const a b) => PrettyBy config (Const a b)

-- | 'prettyBy' for @[a]@ is defined in terms of 'prettyListBy'.
--
-- >>> prettyBy () [True, False]
-- [True, False]
-- >>> prettyBy () "abc"
-- abc
-- >>> prettyBy () [Just False, Nothing, Just True]
-- [False, True]
deriving via DefaultlyPretty [a]
    instance PrettyDefaultsBy config [a] => PrettyBy config [a]

deriving via DefaultlyPretty (NonEmpty a)
    instance PrettyDefaultsBy config (NonEmpty a) => PrettyBy config (NonEmpty a)

-- | By default a 'String' (i.e. @[Char]@) is converted to a @Text@ first and then pretty-printed.
-- So make sure that if you have any non-default pretty-printing for @Char@ or @Text@,
-- they must be in sync.
--
-- >>> prettyBy () 'a'
-- a
-- >>> prettyBy () "abc"
-- abc
deriving via DefaultlyPretty Char
    instance PrettyDefaultsBy config Char => PrettyBy config Char

-- | By default a @[Maybe a]@ is converted to @[a]@ first and only then pretty-printed.
--
-- >>> braces $ prettyBy () (Just True)
-- {True}
-- >>> braces $ prettyBy () (Nothing :: Maybe Bool)
-- {}
-- >>> prettyBy () [Just False, Nothing, Just True]
-- [False, True]
-- >>> prettyBy () [Nothing, Just 'a', Just 'b', Nothing, Just 'c']
-- abc
deriving via DefaultlyPretty (Maybe a)
    instance PrettyDefaultsBy config (Maybe a) => PrettyBy config (Maybe a)
