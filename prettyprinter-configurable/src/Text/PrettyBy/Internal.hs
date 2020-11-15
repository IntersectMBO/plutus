{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

-- | Internal module defining the core machinery of configurable pretty-printing.
--
-- We introduce an internal module, because most users won't need stuff like 'DefaultPrettyBy', so
-- it doesn't make much sense to export that from the top-level module. But 'DefaultPrettyBy' can
-- still can be useful occasionally and there are some docs explaining details of the implementation
-- (see e.g. 'DispatchPrettyDefaultBy'), hence it's exported from here.
--
-- Versioning is not affected by the fact that the module is called \"Internal\", i.e. we track
-- changes using the usual PVP.

module Text.PrettyBy.Internal
    ( PrettyBy (..)
    , HasPrettyDefaults
    , IgnorePrettyConfig (..)
    , AttachPrettyConfig (..)
    , withAttachPrettyConfig
    , defaultPrettyFunctorBy
    , defaultPrettyBifunctorBy
    , StarsOfHead
    , DispatchDefaultFor (..)
    , DefaultFor (..)
    , AttachDefaultPrettyConfig (..)
    , DefaultPrettyBy (..)
    , NonDefaultPrettyBy (..)
    , PrettyDefaultBy
    , PrettyCommon (..)
    , ThrowOnStuck
    , HasPrettyDefaultsStuckError
    , NonStuckHasPrettyDefaults
    , DispatchPrettyDefaultBy (..)
    , PrettyAny (..)
    ) where

import           Text.Pretty

import           Data.Bifunctor
import           Data.Coerce
import           Data.Functor.Const
import           Data.Functor.Identity
import           Data.Int
import           Data.List.NonEmpty    (NonEmpty (..))
import           Data.Maybe
import qualified Data.Text             as Strict
import qualified Data.Text.Lazy        as Lazy
import           Data.Void
import           Data.Word
import           GHC.Natural
import           GHC.TypeLits

-- ##########################
-- ## The 'PrettyBy' class ##
-- ##########################

-- | A class for pretty-printing values in a configurable manner.
--
-- A basic example:
--
-- >>> data Case = UpperCase | LowerCase
-- >>> data D = D
-- >>> instance PrettyBy Case D where prettyBy UpperCase D = "D"; prettyBy LowerCase D = "d"
-- >>> prettyBy UpperCase D
-- D
-- >>> prettyBy LowerCase D
-- d
--
-- The library provides instances for common types like 'Integer' or 'Bool', so you can't define
-- your own @PrettyBy SomeConfig Integer@ instance. And for the same reason you should not define
-- instances like @PrettyBy SomeAnotherConfig a@ for universally quantified @a@, because such an
-- instance would overlap with the existing ones. Take for example
--
-- >>> data ViaShow = ViaShow
-- >>> instance Show a => PrettyBy ViaShow a where prettyBy ViaShow = pretty . show
--
-- with such an instance @prettyBy ViaShow (1 :: Int)@ throws an error about overlapping instances:
--
-- > • Overlapping instances for PrettyBy ViaShow Int
-- >     arising from a use of ‘prettyBy’
-- >   Matching instances:
-- >     instance PrettyDefaultBy config Int => PrettyBy config Int
-- >     instance [safe] Show a => PrettyBy ViaShow a
--
-- There's a @newtype@ provided specifically for the purpose of defining a 'PrettyBy' instance for
-- any @a@: 'PrettyAny'. Read its docs for details on when you might want to use it.
--
-- The 'PrettyBy' instance for common types is defined in a way that allows to override default
-- pretty-printing behaviour, read the docs of 'HasPrettyDefaults' for details.
class PrettyBy config a where
    -- | Pretty-print a value of type @a@ the way a @config@ specifies it.
    -- The default implementation of 'prettyBy' is in terms of 'pretty', 'defaultPrettyFunctorBy'
    -- or 'defaultPrettyBifunctorBy' depending on the kind of the data type that you're providing
    -- an instance for. For example, the default implementation of 'prettyBy' for a monomorphic type
    -- is going to be "ignore the config and call 'pretty' over the value":
    --
    -- >>> newtype N = N Int deriving newtype (Pretty)
    -- >>> instance PrettyBy () N
    -- >>> prettyBy () (N 42)
    -- 42
    --
    -- The default implementation of 'prettyBy' for a 'Functor' is going to be in terms of
    -- 'defaultPrettyFunctorBy':
    --
    -- >>> newtype N a = N a deriving (Functor) deriving newtype (Pretty)
    -- >>> instance PrettyBy () a => PrettyBy () (N a)
    -- >>> prettyBy () (N (42 :: Int))
    -- 42
    --
    -- It's fine for the data type to have a phantom parameter as long as the data type is still a
    -- 'Functor' (i.e. the parameter has to be of kind @*@). Then 'defaultPrettyFunctorBy' is used
    -- again:
    --
    -- >>> newtype N a = N Int deriving (Functor) deriving newtype (Pretty)
    -- >>> instance PrettyBy () (N b)
    -- >>> prettyBy () (N 42)
    -- 42
    --
    -- If the data type has a single parameter of any other kind, then it's not a functor and so
    -- like in the monomorphic case 'pretty' is used:
    --
    -- >>> newtype N (b :: Bool) = N Int deriving newtype (Pretty)
    -- >>> instance PrettyBy () (N b)
    -- >>> prettyBy () (N 42)
    -- 42
    --
    -- Same applies to a data type with two parameters: if both the parameters are of kind @*@,
    -- then the data type is assumed to be a 'Bifunctor' and hence 'defaultPrettyBifunctorBy' is
    -- used. If the right parameter is of kind @*@ and the left parameter is of any other kind,
    -- then we fallback to assuming the data type is a 'Functor' and defining 'prettyBy' as
    -- 'defaultPrettyFunctorBy'. If both the parameters are not of kind @*@, we fallback to
    -- implementing 'prettyBy' in terms of 'pretty' like in the monomorphic case.
    --
    -- Note that in all those cases a 'Pretty' instance for the data type has to already exist,
    -- so that we can derive a 'PrettyBy' one in terms of it. If it doesn't exist or if your data
    -- type is not supported (for example, if it has three or more parameters of kind @*@), then
    -- you'll need to provide the implementation manually.
    prettyBy :: config -> a -> Doc ann
    default prettyBy :: DefaultFor "prettyBy" config a => config -> a -> Doc ann
    prettyBy = defaultFor @"prettyBy"

    -- Defaulting to 'prettyList' would require the user to either provide a 'Pretty' instance for
    -- each data type implementing 'PrettyBy' or to supply the sensible default implementation as
    -- 'defaultPrettyFunctorBy' manually and both the options are silly.
    -- | 'prettyListBy' is used to define the default 'PrettyBy' instance for @[a]@ and @NonEmpty a@.
    -- In normal circumstances only the 'prettyBy' function is used.
    -- The default implementation of 'prettyListBy' is in terms of 'defaultPrettyFunctorBy'.
    prettyListBy :: config -> [a] -> Doc ann
    default prettyListBy :: config -> [a] -> Doc ann
    prettyListBy = defaultPrettyFunctorBy

-- #########################################
-- ## The 'HasPrettyDefaults' type family ##
-- #########################################

-- | Determines whether a pretty-printing config allows default pretty-printing for types that
-- support it. I.e. it's possible to create a new config and get access to pretty-printing for
-- all types supporting default pretty-printing just by providing the right type instance. Example:
--
-- >>> data DefCfg = DefCfg
-- >>> type instance HasPrettyDefaults DefCfg = 'True
-- >>> prettyBy DefCfg (['a', 'b', 'c'], (1 :: Int), Just True)
-- (abc, 1, True)
--
-- The set of types supporting default pretty-printing is determined by the @prettyprinter@
-- library: whatever __there__ has a 'Pretty' instance also supports default pretty-printing
-- in this library and the behavior of @pretty x@ and @prettyBy config_with_defaults x@ must
-- be identical when @x@ is one of such types.
--
-- It is possible to override default pretty-printing. For this you need to specify that
-- 'HasPrettyDefaults' is @'False@ for your config and then define a @NonDefaultPrettyBy config@
-- instance for each of the types supporting default pretty-printing that you want to pretty-print
-- values of. Note that once 'HasPrettyDefaults' is specified to be @'False@,
-- __all defaults are lost__ for your config, so you can't override default pretty-printing for one
-- type and keep the defaults for all the others. I.e. if you have
--
-- >>> data NonDefCfg = NonDefCfg
-- >>> type instance HasPrettyDefaults NonDefCfg = 'False
--
-- then you have no defaults available and an attempt to pretty-print a value of a type supporting
-- default pretty-printing
--
-- > prettyBy NonDefCfg True
--
-- results in a type error:
--
-- > • No instance for (NonDefaultPrettyBy NonDef Bool)
-- >      arising from a use of ‘prettyBy’
--
-- As the error suggests you need to provide a 'NonDefaultPrettyBy' instance explicitly:
--
-- >>> instance NonDefaultPrettyBy NonDefCfg Bool where nonDefaultPrettyBy _ b = if b then "t" else "f"
-- >>> prettyBy NonDefCfg True
-- t
--
-- It is also possible not to provide any implementation for 'nonDefaultPrettyBy', in which case
-- it defaults to being the default pretty-printing for the given type. This can be useful to
-- recover default pretty-printing for types pretty-printing of which you don't want to override:
--
-- >>> instance NonDefaultPrettyBy NonDefCfg Int
-- >>> prettyBy NonDefCfg (42 :: Int)
-- 42
--
-- Look into @test/NonDefault.hs@ for an extended example.
--
-- We could give the user more fine-grained control over what defaults to override instead of
-- requiring to explicitly provide all the instances whenever there's a need to override any
-- default behavior, but that would complicate the library even more, so we opted for not doing
-- that at the moment.
--
-- Note that you can always override default behavior by wrapping a type in @newtype@ and
-- providing a @PrettyBy config_name@ instance for that @newtype@.
--
-- Also note that if you want to extend the set of types supporting default pretty-printing
-- it's not enough to provide a 'Pretty' instance for your type (such logic is hardly expressible
-- in present day Haskell). Read the docs of 'DefaultPrettyBy' for how to extend the set of types
-- supporting default pretty-printing.
type family HasPrettyDefaults config :: Bool

-- | @prettyBy ()@ works like @pretty@ for types supporting default pretty-printing.
type instance HasPrettyDefaults () = 'True

-- ###########################
-- ## Interop with 'Pretty' ##
-- ###########################

-- | A newtype wrapper around @a@ whose point is to provide a @PrettyBy config@ instance
-- for anything that has a 'Pretty' instance.
newtype IgnorePrettyConfig a = IgnorePrettyConfig
    { unIgnorePrettyConfig :: a
    }

-- |
-- >>> data Cfg = Cfg
-- >>> data D = D
-- >>> instance Pretty D where pretty D = "D"
-- >>> prettyBy Cfg $ IgnorePrettyConfig D
-- D
instance Pretty a => PrettyBy config (IgnorePrettyConfig a) where
    prettyBy _ = pretty . unIgnorePrettyConfig

-- | A config together with some value. The point is to provide a 'Pretty' instance
-- for anything that has a @PrettyBy config@ instance.
data AttachPrettyConfig config a = AttachPrettyConfig !config !a

-- |
-- >>> data Cfg = Cfg
-- >>> data D = D
-- >>> instance PrettyBy Cfg D where prettyBy Cfg D = "D"
-- >>> pretty $ AttachPrettyConfig Cfg D
-- D
instance PrettyBy config a => Pretty (AttachPrettyConfig config a) where
    pretty (AttachPrettyConfig config x) = prettyBy config x

-- | Pass @AttachPrettyConfig config@ to the continuation.
withAttachPrettyConfig
    :: config -> ((forall a. a -> AttachPrettyConfig config a) -> r) -> r
withAttachPrettyConfig config k = k $ AttachPrettyConfig config

-- | Default configurable pretty-printing for a 'Functor' in terms of 'Pretty'.
-- Attaches the config to each value in the functor and calls 'pretty' over the result,
-- i.e. the spine of the functor is pretty-printed the way the 'Pretty' class specifies it,
-- while the elements are printed by 'prettyBy'.
defaultPrettyFunctorBy
    :: (Functor f, Pretty (f (AttachPrettyConfig config a)))
    => config -> f a -> Doc ann
defaultPrettyFunctorBy config a =
    pretty $ AttachPrettyConfig config <$> a

-- | Default configurable pretty-printing for a 'Bifunctor' in terms of 'Pretty'
-- Attaches the config to each value in the bifunctor and calls 'pretty' over the result,
-- i.e. the spine of the bifunctor is pretty-printed the way the 'Pretty' class specifies it,
-- while the elements are printed by 'prettyBy'.
defaultPrettyBifunctorBy
    :: (Bifunctor f, Pretty (f (AttachPrettyConfig config a) (AttachPrettyConfig config b)))
    => config -> f a b -> Doc ann
defaultPrettyBifunctorBy config a =
    withAttachPrettyConfig config $ \attach -> pretty $ bimap attach attach a

-- ##################################################################################
-- ## Dispatching between default implementations for 'prettyBy'/'defaultPrettyBy' ##
-- ##################################################################################

-- | Return the longest sequence of @*@ in the kind (right-to-left) of the head of an application.
-- (but no longer than @* -> * -> *@, because we can't support longer ones in 'DispatchDefaultFor').
type family StarsOfHead (target :: Symbol) (a :: *) :: * where
    StarsOfHead target ((f :: * -> * -> * -> *) a b c) = TypeError
        (     'Text "Automatic derivation of ‘"':<>: 'Text target ':<>: 'Text "’"
        ':$$: 'Text "is not possible for data types that receive three and more arguments of kind ‘*’"
        )
    StarsOfHead _      ((f :: k -> * -> * -> *) a b c) = * -> * -> *
    StarsOfHead _      ((f :: * -> * -> *)      a b  ) = * -> * -> *
    StarsOfHead _      ((f :: k -> * -> *)      a b  ) = * -> *
    StarsOfHead _      ((f :: * -> *)           a    ) = * -> *
    StarsOfHead _      ((f :: k -> *)           a    ) = *
    StarsOfHead _      a                               = *

-- | This allows us to have different default implementations for 'prettyBy' and 'defaultPrettyBy'
-- depending on whether @a@ is a monomorphic type or a 'Functor' or a 'Bifunctor'. Read the docs of
-- 'prettyBy' for details.
class StarsOfHead target a ~ k => DispatchDefaultFor target k config a where
    dispatchDefaultFor :: config -> a -> Doc ann

instance (StarsOfHead target a ~ *, Pretty a) => DispatchDefaultFor target * config a where
    dispatchDefaultFor _ = pretty

instance ( StarsOfHead target fa ~ (k -> *), fa ~ f a
         , Functor f, Pretty (f (AttachPrettyConfig config a))
         ) => DispatchDefaultFor target (k -> *) config fa where
    dispatchDefaultFor = defaultPrettyFunctorBy

instance ( StarsOfHead target fab ~ (k1 -> k2 -> *), fab ~ f a b
         , Bifunctor f, Pretty (f (AttachPrettyConfig config a) (AttachPrettyConfig config b))
         ) => DispatchDefaultFor target (k1 -> k2 -> *) config fab where
    dispatchDefaultFor = defaultPrettyBifunctorBy

-- | Introducing a class just for the nice name of the method and in case the defaulting machinery
-- somehow blows up in the user's face.
class DispatchDefaultFor target (StarsOfHead target a) config a =>
            DefaultFor target config a where
    defaultFor :: config -> a -> Doc ann

instance DispatchDefaultFor target (StarsOfHead target a) config a =>
            DefaultFor target config a where
    defaultFor = dispatchDefaultFor @target

-- ###################################################
-- ## The 'DefaultPrettyBy' class and its instances ##
-- ###################################################

-- | Same as 'AttachPrettyConfig', but for providing a 'Pretty' instance for anything that has
-- a 'DefaultPrettyBy' instance. Needed for the default implementation of 'defaultPrettyListBy'.
data AttachDefaultPrettyConfig config a = AttachDefaultPrettyConfig !config !a

instance DefaultPrettyBy config a => Pretty (AttachDefaultPrettyConfig config a) where
    pretty (AttachDefaultPrettyConfig config x) = defaultPrettyBy config x

-- | A class for pretty-printing values is some default manner. Basic example:
--
-- >>> data D = D
-- >>> instance PrettyBy () D where prettyBy () D = "D"
-- >>> defaultPrettyBy () (Just D)
-- D
--
-- 'DefaultPrettyBy' and 'PrettyBy' are mutually recursive in a sense: 'PrettyBy' delegates
-- to 'DefaultPrettyBy' (provided the config supports defaults) when given a value of a type
-- supporting default pretty-printing and 'DefaultPrettyBy' delegates back to 'PrettyBy' for
-- elements of a polymorphic container.
--
-- It is possible to extend the set of types supporting default pretty-printing. If you have a
-- @newtype@ wrapping a type that already supports default pretty-printing, then "registering"
-- that @newtype@ amounts to making a standalone newtype-deriving declaration:
--
-- >>> newtype AlsoInt = AlsoInt Int
-- >>> deriving newtype instance PrettyDefaultBy config Int => PrettyBy config AlsoInt
-- >>> prettyBy () (AlsoInt 42)
-- 42
--
-- Note that you have to use standalone deriving as
--
-- > newtype AlsoInt = AlsoInt Int deriving newtype (PrettyBy config)
--
-- doesn't please GHC.
--
-- It's also good practice to preserve coherence of 'Pretty' and 'PrettyBy', so I'd also add
-- @deriving newtype (Pretty)@ to the definition of @AlsoInt@, even though it's not necessary.
--
-- When you want to extend the set of types supporting default pretty-printing with a data type
-- that is a @data@ rather than a @newtype@, you can directly implement 'DefaultPrettyBy' and
-- and via-derive 'PrettyBy':
--
-- >>> data D = D
-- >>> instance DefaultPrettyBy config D where defaultPrettyBy _ D = "D"
-- >>> deriving via PrettyCommon D instance PrettyDefaultBy config D => PrettyBy config D
-- >>> prettyBy () D
-- D
--
-- But since it's best to preserve coherence of 'Pretty' and 'PrettyBy' for types supporting
-- default pretty-printing, it's recommended (not mandatory) to define a 'Pretty' instance and
-- anyclass-derive 'DefaultPrettyBy' in terms of it:
--
-- >>> data D = D
-- >>> instance Pretty D where pretty D = "D"
-- >>> instance DefaultPrettyBy config D
-- >>> deriving via PrettyCommon D instance PrettyDefaultBy config D => PrettyBy config D
-- >>> prettyBy () [D, D, D]
-- [D, D, D]
--
-- Note that 'DefaultPrettyBy' is specifically designed to handle __all__ configs in its instances,
-- i.e. you only specify a data type in a 'DefaultPrettyBy' instance and leave @config@ universally
-- quantified. This is because default pretty-printing behavior should be the same for all configs
-- supporting default pretty-printing (it's the default after all). If you want to override the
-- defaults, read the docs of 'HasPrettyDefaults'.
--
-- Since @config@ in a 'DefaultPrettyBy' instance is meant to be universally quantified,
-- 'defaultPrettyBy' (the main method of 'DefaultPrettyBy') has to ignore the config in the
-- monomorphic case as it can't use it in any way anyway, i.e. in the monomorphic case
-- 'defaultPrettyBy' has the exact same info as simple 'pretty', which is another reason to
-- anyclass-derive 'DefaultPrettyBy' in terms of 'Pretty'.
--
-- Like in the case of 'prettyBy', the default implementation of 'defaultPrettyBy' for a 'Functor'
-- is 'defaultPrettyFunctorBy' (and for a 'Bifunctor' -- 'defaultPrettyBifunctorBy'):
--
-- >>> data Twice a = Twice a a deriving (Functor)
-- >>> instance Pretty a => Pretty (Twice a) where pretty (Twice x y) = pretty x <+> "&" <+> pretty y
-- >>> instance PrettyBy config a => DefaultPrettyBy config (Twice a)
-- >>> deriving via PrettyCommon (Twice a) instance PrettyDefaultBy config (Twice a) => PrettyBy config (Twice a)
-- >>> prettyBy () (Twice True False)
-- True & False
--
-- Since preserving coherence of 'Pretty' and 'PrettyBy' is only a good practice and not
-- mandatory, it's fine not to provide an instance for 'Pretty'. Then a 'DefaultPrettyBy' can be
-- implemented directly:
--
-- >>> data Twice a = Twice a a
-- >>> instance PrettyBy config a => DefaultPrettyBy config (Twice a) where defaultPrettyBy config (Twice x y) = prettyBy config x <+> "&" <+> prettyBy config y
-- >>> deriving via PrettyCommon (Twice a) instance PrettyDefaultBy config (Twice a) => PrettyBy config (Twice a)
-- >>> prettyBy () (Twice True False)
-- True & False
--
-- But make sure that if both a 'Pretty' and a 'DefaultPrettyBy' instances exist, then they're in
-- sync.
class DefaultPrettyBy config a where
    -- | Pretty-print a value of type @a@ in some default manner.
    -- The default implementation works equally to the one of 'prettyBy'.
    defaultPrettyBy :: config -> a -> Doc ann
    default defaultPrettyBy :: DefaultFor "defaultPrettyBy" config a => config -> a -> Doc ann
    defaultPrettyBy = defaultFor @"defaultPrettyBy"

    -- | 'defaultPrettyListBy' to 'prettyListBy' is what 'defaultPrettyBy' to 'prettyBy'.
    -- The default implementation is \"pretty-print the spine of a list the way 'pretty' does that
    -- and pretty-print the elements using 'defaultPrettyBy'\".
    defaultPrettyListBy :: config -> [a] -> Doc ann
    default defaultPrettyListBy :: config -> [a] -> Doc ann
    defaultPrettyListBy config = pretty . map (AttachDefaultPrettyConfig config)

-- Monomorphic instances.

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

-- Straightforward polymorphic instances.

instance PrettyBy config a => DefaultPrettyBy config (Identity a)
instance PrettyBy config a => DefaultPrettyBy config (Const a (b :: *))
instance (PrettyBy config a, PrettyBy config b) => DefaultPrettyBy config (a, b)

-- We don't have @Trifunctor@ in base, unfortunately, hence writing things out manually. Could we
-- do that via generics? I feel like that would amount to implementing n-ary 'Functor' anyway.
instance (PrettyBy config a, PrettyBy config b, PrettyBy config c) =>
            DefaultPrettyBy config (a, b, c) where
    defaultPrettyBy config (x, y, z) =
        withAttachPrettyConfig config $ \attach -> pretty (attach x, attach y, attach z)

-- Peculiar instances.

instance PrettyBy config Strict.Text => DefaultPrettyBy config Char where
    defaultPrettyListBy config = prettyBy config . Strict.pack

instance PrettyBy config a => DefaultPrettyBy config (Maybe a) where
    defaultPrettyListBy config = prettyListBy config . catMaybes

instance PrettyBy config a => DefaultPrettyBy config [a] where
    defaultPrettyBy = prettyListBy

instance PrettyBy config a => DefaultPrettyBy config (NonEmpty a) where
    defaultPrettyBy config (x :| xs) = prettyListBy config (x : xs)

-- ###########################################################
-- ## The 'NonDefaultPrettyBy' class and its none instances ##
-- ###########################################################

-- | A class for overriding default pretty-printing behavior for types having it.
-- Read the docs of 'HasPrettyDefaults' for how to use the class.
class NonDefaultPrettyBy config a where
    -- | Pretty-print a value of a type supporting default pretty-printing in a possibly
    -- non-default way. The "possibly" is due to 'nonDefaultPrettyBy' having a default
    -- implementation as 'defaultPrettyBy'. See docs for 'HasPrettyDefaults' for details.
    nonDefaultPrettyBy :: config -> a -> Doc ann
    default nonDefaultPrettyBy :: DefaultPrettyBy config a => config -> a -> Doc ann
    nonDefaultPrettyBy = defaultPrettyBy

    -- | 'nonDefaultPrettyListBy' to 'prettyListBy' is what 'nonDefaultPrettyBy' to 'prettyBy'.
    -- Analogously, the default implementation is 'defaultPrettyListBy'.
    nonDefaultPrettyListBy :: config -> [a] -> Doc ann
    default nonDefaultPrettyListBy :: DefaultPrettyBy config a => config -> [a] -> Doc ann
    nonDefaultPrettyListBy = defaultPrettyListBy

-- ####################################################################
-- ## Dispatching between 'DefaultPrettyBy' and 'NonDefaultPrettyBy' ##
-- ####################################################################

-- | 'DispatchPrettyDefaultBy' is a class for dispatching on @HasPrettyDefaults config@:
-- if it's @'True@, then 'dispatchPrettyDefaultBy' is instantiated as 'defaultPrettyBy',
-- otherwise as 'nonDefaultPrettyBy' (and similarly for 'dispatchPrettyDefaultListBy').
-- I.e. depending on whether a config allows to pretty-print values using default
-- pretty-printing, either the default or non-default pretty-printing strategy is used.
class HasPrettyDefaults config ~ b => DispatchPrettyDefaultBy (b :: Bool) config a where
    dispatchPrettyDefaultBy     :: config -> a   -> Doc ann
    dispatchPrettyDefaultListBy :: config -> [a] -> Doc ann

instance (HasPrettyDefaults config ~ 'True, DefaultPrettyBy config a) =>
            DispatchPrettyDefaultBy 'True config a where
    dispatchPrettyDefaultBy     = defaultPrettyBy
    dispatchPrettyDefaultListBy = defaultPrettyListBy

instance (HasPrettyDefaults config ~ 'False, NonDefaultPrettyBy config a) =>
            DispatchPrettyDefaultBy 'False config a where
    dispatchPrettyDefaultBy     = nonDefaultPrettyBy
    dispatchPrettyDefaultListBy = nonDefaultPrettyListBy

{- Note [Definition of PrettyDefaultBy]
A class alias throws "this makes type inference for inner bindings fragile" warnings
in user code, so we opt for a type alias in the definition of 'PrettyDefaultBy'.

I also tried the following representation

    class PrettyDefaultBy config a where
        type HasPrettyDefaults config :: Bool
        prettyDefaultsBy :: config -> a -> Doc ann
        prettyDefaultsListBy :: config -> [a] -> Doc ann

with both the methods having default implementations in terms of methods of the
'DispatchPrettyDefaultBy' class, so that 'PrettyDefaultBy' does not unwind to a creepy
type in errors, but then the user has to write things like

    instance DefaultPrettyBy () a => PrettyDefaultBy () a where
        type HasPrettyDefaults () = 'True

which is wordy and leaks 'DefaultPrettyBy' to the user, which is something that the user
does not see otherwise.

Instead, we fix the problem of 'PrettyDefaultBy' unwinding to a creepy type by using a custom
type error, 'HasPrettyDefaultsStuckError', which is thrown whenever @HasPrettyDefaults config@
is stuck. This way the user's code either type checks or gives a nice error and so the whole
'DispatchPrettyDefaultBy' thing does not leak to the user.

See https://kcsongor.github.io/report-stuck-families for how detection of a stuck type family
application is implemented.
-}

-- | Throw @err@ when @b@ is stuck.
type family ThrowOnStuck err (b :: Bool) :: Bool where
    ThrowOnStuck _   'True  = 'True
    ThrowOnStuck _   'False = 'False
    ThrowOnStuck err _      = err

-- We have to use a type family here rather than a type alias, because otherwise it evaluates too early.
-- | The error thrown when @HasPrettyDefaults config@ is stuck.
type family HasPrettyDefaultsStuckError config :: Bool where
    HasPrettyDefaultsStuckError config = TypeError
        (     'Text "No ’HasPrettyDefaults’ is specified for " ':<>: 'ShowType config
        ':$$: 'Text "Either you're trying to derive an instance, in which case you have to use"
        ':$$: 'Text "  standalone deriving and need to explicitly put a ‘PrettyDefaultBy config’"
        ':$$: 'Text "  constraint in the instance context for each type in your data type"
        ':$$: 'Text "  that supports default pretty-printing"
        ':$$: 'Text "Or you're trying to pretty-print a value of a type supporting default"
        ':$$: 'Text "  pretty-printing using a config, for which ‘HasPrettyDefaults’ is not specified."
        ':$$: 'Text "  If the config is a bound type variable, then you need to add"
        ':$$: 'Text "    ‘HasPrettyDefaults <config_variable_name> ~ 'True’"
        ':$$: 'Text "  to the context."
        ':$$: 'Text "  If the config is a data type, then you need to add"
        ':$$: 'Text "    ‘type instance HasPrettyDefaults <config_name> = 'True’"
        ':$$: 'Text "  at the top level."
        )

-- | A version of 'HasPrettyDefaults' that is never stuck: it either immediately evaluates
-- to a 'Bool' or fails with a 'TypeError'.
type NonStuckHasPrettyDefaults config =
    ThrowOnStuck (HasPrettyDefaultsStuckError config) (HasPrettyDefaults config)

-- See Note [Definition of PrettyDefaultBy].
-- | @PrettyDefaultBy config a@ is the same thing as @PrettyBy config a@, when @a@ supports
-- default pretty-printing. Thus @PrettyDefaultBy config a@ and @PrettyBy config a@ are
-- interchangeable constraints for such types, but the latter throws an annoying
-- \"this makes type inference for inner bindings fragile\" warning, unlike the former.
-- @PrettyDefaultBy config a@ reads as \"@a@ supports default pretty-printing and can be
-- pretty-printed via @config@ in either default or non-default manner depending on whether
-- @config@ supports default pretty-printing\".
type PrettyDefaultBy config = DispatchPrettyDefaultBy (NonStuckHasPrettyDefaults config) config

-- | A newtype wrapper defined for its 'PrettyBy' instance that allows to via-derive a 'PrettyBy'
-- instance for a type supporting default pretty-printing.
newtype PrettyCommon a = PrettyCommon
    { unPrettyCommon :: a
    }

coerceDispatchPrettyDefaults :: Coercible a b => (config -> a -> Doc ann) -> config -> b -> Doc ann
coerceDispatchPrettyDefaults = coerce

instance PrettyDefaultBy config a => PrettyBy config (PrettyCommon a) where
    prettyBy     = coerceDispatchPrettyDefaults @a   dispatchPrettyDefaultBy
    prettyListBy = coerceDispatchPrettyDefaults @[a] dispatchPrettyDefaultListBy

-- #######################################################################
-- ## 'PrettyBy' instances for types supporting default pretty-printing ##
-- #######################################################################

-- |
-- >>> prettyBy () ([] :: [Void])
-- []
deriving via PrettyCommon Void
    instance PrettyDefaultBy config Void => PrettyBy config Void

-- |
-- >>> prettyBy () ()
-- ()
--
-- The argument is not used:
--
-- >>> prettyBy () (error "Strict?" :: ())
-- ()
deriving via PrettyCommon ()
    instance PrettyDefaultBy config () => PrettyBy config ()

-- |
-- >>> prettyBy () True
-- True
deriving via PrettyCommon Bool
    instance PrettyDefaultBy config Bool => PrettyBy config Bool

-- |
-- >>> prettyBy () (123 :: Natural)
-- 123
deriving via PrettyCommon Natural
    instance PrettyDefaultBy config Natural => PrettyBy config Natural

-- |
-- >>> prettyBy () (2^(123 :: Int) :: Integer)
-- 10633823966279326983230456482242756608
deriving via PrettyCommon Integer
    instance PrettyDefaultBy config Integer => PrettyBy config Integer

-- |
-- >>> prettyBy () (123 :: Int)
-- 123
deriving via PrettyCommon Int
    instance PrettyDefaultBy config Int => PrettyBy config Int
deriving via PrettyCommon Int8
    instance PrettyDefaultBy config Int8 => PrettyBy config Int8
deriving via PrettyCommon Int16
    instance PrettyDefaultBy config Int16 => PrettyBy config Int16
deriving via PrettyCommon Int32
    instance PrettyDefaultBy config Int32 => PrettyBy config Int32
deriving via PrettyCommon Int64
    instance PrettyDefaultBy config Int64 => PrettyBy config Int64
deriving via PrettyCommon Word
    instance PrettyDefaultBy config Word => PrettyBy config Word
deriving via PrettyCommon Word8
    instance PrettyDefaultBy config Word8 => PrettyBy config Word8
deriving via PrettyCommon Word16
    instance PrettyDefaultBy config Word16 => PrettyBy config Word16
deriving via PrettyCommon Word32
    instance PrettyDefaultBy config Word32 => PrettyBy config Word32
deriving via PrettyCommon Word64
    instance PrettyDefaultBy config Word64 => PrettyBy config Word64

-- |
-- >>> prettyBy () (pi :: Float)
-- 3.1415927
deriving via PrettyCommon Float
    instance PrettyDefaultBy config Float => PrettyBy config Float

-- |
-- >>> prettyBy () (pi :: Double)
-- 3.141592653589793
deriving via PrettyCommon Double
    instance PrettyDefaultBy config Double => PrettyBy config Double

-- | Automatically converts all newlines to @line@.
--
-- >>> prettyBy () ("hello\nworld" :: Strict.Text)
-- hello
-- world
deriving via PrettyCommon Strict.Text
    instance PrettyDefaultBy config Strict.Text => PrettyBy config Strict.Text

-- | An instance for lazy @Text@. Identitical to the strict one.
deriving via PrettyCommon Lazy.Text
    instance PrettyDefaultBy config Lazy.Text => PrettyBy config Lazy.Text

-- |
-- >>> prettyBy () (Identity True)
-- True
deriving via PrettyCommon (Identity a)
    instance PrettyDefaultBy config (Identity a) => PrettyBy config (Identity a)

-- |
-- >>> prettyBy () (False, "abc")
-- (False, abc)
deriving via PrettyCommon (a, b)
    instance PrettyDefaultBy config (a, b) => PrettyBy config (a, b)

-- |
-- >>> prettyBy () ('a', "bcd", True)
-- (a, bcd, True)
deriving via PrettyCommon (a, b, c)
    instance PrettyDefaultBy config (a, b, c) => PrettyBy config (a, b, c)

-- | Non-polykinded, because @Pretty (Const a b)@ is not polykinded either.
--
-- >>> prettyBy () (Const 1 :: Const Integer Bool)
-- 1
deriving via PrettyCommon (Const a b)
    instance PrettyDefaultBy config (Const a b) => PrettyBy config (Const a b)

-- | 'prettyBy' for @[a]@ is defined in terms of 'prettyListBy' by default.
--
-- >>> prettyBy () [True, False]
-- [True, False]
-- >>> prettyBy () "abc"
-- abc
-- >>> prettyBy () [Just False, Nothing, Just True]
-- [False, True]
deriving via PrettyCommon [a]
    instance PrettyDefaultBy config [a] => PrettyBy config [a]

-- | 'prettyBy' for @NonEmpty a@ is defined in terms of 'prettyListBy' by default.
--
-- >>> prettyBy () (True :| [False])
-- [True, False]
-- >>> prettyBy () ('a' :| "bc")
-- abc
-- >>> prettyBy () (Just False :| [Nothing, Just True])
-- [False, True]
deriving via PrettyCommon (NonEmpty a)
    instance PrettyDefaultBy config (NonEmpty a) => PrettyBy config (NonEmpty a)

-- | By default a 'String' (i.e. @[Char]@) is converted to a @Text@ first and then pretty-printed.
-- So make sure that if you have any non-default pretty-printing for @Char@ or @Text@,
-- they're in sync.
--
-- >>> prettyBy () 'a'
-- a
-- >>> prettyBy () "abc"
-- abc
deriving via PrettyCommon Char
    instance PrettyDefaultBy config Char => PrettyBy config Char

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
deriving via PrettyCommon (Maybe a)
    instance PrettyDefaultBy config (Maybe a) => PrettyBy config (Maybe a)

-- #############################
-- ## The 'PrettyAny' newtype ##
-- #############################

-- | A @newtype@ wrapper around @a@ provided for the purporse of defining 'PrettyBy' instances
-- handling any @a@. For example you can wrap values with the @PrettyAny@ constructor directly
-- like in this last line of
--
-- >>> data ViaShow = ViaShow
-- >>> instance Show a => PrettyBy ViaShow (PrettyAny a) where prettyBy ViaShow = pretty . show . unPrettyAny
-- >>> prettyBy ViaShow $ PrettyAny True
-- True
--
-- or you can use the type to via-derive instances:
--
-- >>> data D = D deriving (Show)
-- >>> deriving via PrettyAny D instance PrettyBy ViaShow D
-- >>> prettyBy ViaShow D
-- D
--
-- One important use case is handling sum-type configs. For example having two configs you can
-- define their sum and derive 'PrettyBy' for the unified config in terms of its components:
--
-- >>> data UpperCase = UpperCase
-- >>> data LowerCase = LowerCase
-- >>> data Case = CaseUpperCase UpperCase | CaseLowerCase LowerCase
-- >>> instance (PrettyBy UpperCase a, PrettyBy LowerCase a) => PrettyBy Case (PrettyAny a) where prettyBy (CaseUpperCase upper) = prettyBy upper . unPrettyAny; prettyBy (CaseLowerCase lower) = prettyBy lower . unPrettyAny
--
-- Then having a data type implementing both @PrettyBy UpperCase@ and @PrettyBy LowerCase@ you can
-- derive @PrettyBy Case@ for that data type:
--
-- >>> data D = D
-- >>> instance PrettyBy UpperCase D where prettyBy UpperCase D = "D"
-- >>> instance PrettyBy LowerCase D where prettyBy LowerCase D = "d"
-- >>> deriving via PrettyAny D instance PrettyBy Case D
-- >>> prettyBy UpperCase D
-- D
-- >>> prettyBy LowerCase D
-- d
--
-- Look into @test/Universal.hs@ for an extended example.
newtype PrettyAny a = PrettyAny
    { unPrettyAny :: a
    }

-- $setup
--
-- (Definitions for the doctests)
--
-- >>> :set -XDataKinds
-- >>> :set -XDeriveFunctor
-- >>> :set -XDerivingVia
-- >>> :set -XFlexibleContexts
-- >>> :set -XFlexibleInstances
-- >>> :set -XGeneralizedNewtypeDeriving
-- >>> :set -XMultiParamTypeClasses
-- >>> :set -XOverloadedStrings
-- >>> :set -XStandaloneDeriving
-- >>> :set -XTypeFamilies
-- >>> :set -XUndecidableInstances
