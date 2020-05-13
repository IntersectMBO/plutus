{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}

module Language.PlutusCore.Pretty.PrettyM where
--     ( Sole (..)
--     , HasPrettyConfig (..)
-- --     , CompoundPrettyM (..)
--     , PrettyM (..)
--     , prettyBy
--     , IgnorePrettyConfig (..)
--     , AttachPrettyConfig (..)
--     ) where

import           Control.Lens
import           Control.Monad.Reader
import           Data.Bifunctor
import           Data.List.NonEmpty
import           Data.Proxy
import qualified Data.Text                               as Strict (Text)
import qualified Data.Text.Lazy                          as Lazy (Text)
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.String (renderString)
import           Data.Text.Prettyprint.Doc.Render.Text   (renderLazy, renderStrict)

class HasPrettyConfig env config | env -> config where
    prettyConfig :: Lens' env config

newtype Sole a = Sole
    { unSole :: a
    }

instance HasPrettyConfig (Sole config) config where
    prettyConfig = coerced

class PrettyM config a where
    {-# MINIMAL prettyM | prettyBy #-}

    prettyM :: (MonadReader env m, HasPrettyConfig env config) => a -> m (Doc ann)
    prettyM x = flip prettyBy x <$> view prettyConfig

    prettyBy :: config -> a -> Doc ann
    prettyBy = flip prettyM . Sole

-- **************************
-- ** Convenience functions *
-- **************************

layoutDef :: Doc ann -> SimpleDocStream ann
layoutDef = layoutSmart defaultLayoutOptions

class RenderDef str where
    renderDef :: Doc ann -> str

instance RenderDef String where
    renderDef = renderString . layoutDef

instance RenderDef Strict.Text where
    renderDef = renderStrict . layoutDef

instance RenderDef Lazy.Text where
    renderDef = renderLazy . layoutDef

-- | Pretty-print a value as a string type.
prettyDef :: forall str a. (Pretty a, RenderDef str) => a -> str
prettyDef = renderDef . pretty

-- | Render a value as 'String'.
prettyDefBy :: forall str a config. (PrettyM config a, RenderDef str) => config -> a -> str
prettyDefBy config = renderDef . prettyBy config

-- | Render a value as 'String'.
prettyDefM
    :: forall str a m env config.
       (PrettyM config a, MonadReader env m, HasPrettyConfig env config, RenderDef str)
    => a -> m str
prettyDefM = fmap renderDef . prettyM

-- *************
-- ** Interop **
-- *************

-- | A newtype wrapper around @a@ whose point is to provide a @PrettyM config@ instance
-- for anything that has a 'Pretty' instance.
newtype IgnorePrettyConfig a = IgnorePrettyConfig
    { unIgnorePrettyConfig :: a
    }

instance Pretty a => PrettyM config (IgnorePrettyConfig a) where
    prettyM = pure . pretty . unIgnorePrettyConfig

-- | A config together with some value. The point is to provide a 'Pretty' instance
-- for anything that has a @PrettyM config@ instance.
data AttachPrettyConfig config a = AttachPrettyConfig !config !a

instance PrettyM config a => Pretty (AttachPrettyConfig config a) where
    pretty (AttachPrettyConfig config x) = prettyBy config x

withAttachPrettyConfig
    :: (MonadReader env m, HasPrettyConfig env config)
    => ((forall a. a -> AttachPrettyConfig config a) -> c) -> m c
withAttachPrettyConfig k =
    view prettyConfig <&> \config -> k $ AttachPrettyConfig config

-- data NoPrettyConfig = NoPrettyConfig

-- instance Pretty a => PrettyM NoPrettyConfig a where
--     prettyM = pure . pretty

-- ******************************************
-- ** Default instances for compound types **
-- ******************************************

-- Here we're building on top of existing 'Pretty' instances.

newtype WithPrettyDefaults a = WithPrettyDefaults
    { unWithPrettyDefaults :: a
    }

newtype WithoutPrettyDefaults a = WithoutPrettyDefaults
    { unWithoutPrettyDefaults :: a
    }

instance PrettyM config (WithPrettyDefaults Integer) where
    prettyBy _ = pretty . unWithPrettyDefaults

type family HasPrettyDefaults config :: Bool

class HasPrettyDefaults config ~ b => PrettyDispatchDefaultsM (b :: Bool) config a where
    prettyDispatchDefaultsBy :: proxy b -> config -> a -> Doc ann

instance (HasPrettyDefaults config ~ 'True, PrettyM config (WithPrettyDefaults a)) =>
            PrettyDispatchDefaultsM 'True config a where
    prettyDispatchDefaultsBy _ config = prettyBy config . WithPrettyDefaults

instance (HasPrettyDefaults config ~ 'False, PrettyM config (WithoutPrettyDefaults a)) =>
            PrettyDispatchDefaultsM 'False config a where
    prettyDispatchDefaultsBy _ config = prettyBy config . WithoutPrettyDefaults

type PrettyDefaultsM config = PrettyDispatchDefaultsM (HasPrettyDefaults config) config

instance PrettyDefaultsM config Integer => PrettyM config Integer where
    prettyBy = prettyDispatchDefaultsBy Proxy

data WithoutPrettyDefaultsConfig = WithoutPrettyDefaultsConfig
type instance HasPrettyDefaults WithoutPrettyDefaultsConfig = 'False
instance PrettyM WithoutPrettyDefaultsConfig (WithoutPrettyDefaults Integer) where
    prettyBy _ _ = pretty "0"

-- >>> prettyBy WithoutPrettyDefaultsConfig (1 :: Integer)

data WithPrettyDefaultsConfig = WithPrettyDefaultsConfig
type instance HasPrettyDefaults WithPrettyDefaultsConfig = 'True

-- >>> prettyBy WithPrettyDefaultsConfig (1 :: Integer)
-- 1


defaultPrettyFunctorM
    :: ( MonadReader env m, HasPrettyConfig env config, Functor f
       , Pretty (f (AttachPrettyConfig config a))
       )
    => f a -> m (Doc ann)
defaultPrettyFunctorM a = withAttachPrettyConfig $ \attach -> pretty $ attach <$> a

defaultPrettyBifunctorM
    :: ( MonadReader env m, HasPrettyConfig env config, Bifunctor f
       , Pretty (f (AttachPrettyConfig config a) (AttachPrettyConfig config b))
       )
    => f a b -> m (Doc ann)
defaultPrettyBifunctorM a = withAttachPrettyConfig $ \attach -> pretty $ bimap attach attach a

instance PrettyM config a => PrettyM config [a]          where prettyM = defaultPrettyFunctorM
instance PrettyM config a => PrettyM config (Maybe a)    where prettyM = defaultPrettyFunctorM
instance PrettyM config a => PrettyM config (NonEmpty a) where prettyM = defaultPrettyFunctorM
instance PrettyM config a => PrettyM config (Identity a) where prettyM = defaultPrettyFunctorM

instance (PrettyM config a, PrettyM config b) => PrettyM config (a, b) where
    prettyM = defaultPrettyBifunctorM

instance (PrettyM config a, PrettyM config b, PrettyM config c) => PrettyM config (a, b, c) where
    prettyM (x, y, z) = withAttachPrettyConfig $ \attach -> pretty (attach x, attach y, attach z)

instance PrettyM config a => PrettyM config (Const a b) where
    prettyM a = withAttachPrettyConfig $ \attach -> pretty $ first attach a

-- ********************************************
-- ** Default instances via compound configs **
-- ********************************************


newtype CompoundlyPretty a = CompoundlyPretty
    { unCompoundlyPretty :: a
    } deriving (Show, Eq, Functor, Foldable, Traversable)

-- class CompoundPrettyM config a where
--     compoundPrettyM :: (MonadReader env m, HasPrettyConfig env config) => a -> m (Doc ann)

-- instance CompoundPrettyM config a => PrettyM (CompoundConfig config) a where
--     prettyM =



-- It's not necessary to deal with associativity, see: https://stackoverflow.com/a/43639618
-- But I find it easier and nicer than changing precedence on the fly.
-- | Associativity of an expression.
data Associativity
    = LeftAssociative
    | RightAssociative
    | NonAssociative
    deriving (Eq)

-- | Fixity of an expression.
data Fixity = Fixity
    { _fixityPrecedence    :: !Double
    , _fixityAssociativity :: !Associativity
    }

-- | Determines whether we're going to the right of an operator or to the left.
data Direction
    = Forward   -- ^ To the right.
    | Backward  -- ^ To the left.
    deriving (Eq)

-- | A context that an expression is being rendered in.
data RenderContext = RenderContext
    { _rcDirection :: !Direction
    , _rcFixity    :: !Fixity
    }

-- | Enclose a 'Doc' in parens if required or leave it as is.
-- The need for enclosing is determined from an outer 'RenderContext' and the 'Doc's fixity.
encloseIn
    :: RenderContext  -- ^ An outer context.
    -> Fixity         -- ^ An inner fixity.
    -> Doc ann
    -> Doc ann
encloseIn (RenderContext dir (Fixity precOut assocOut)) (Fixity precIn assocIn) =
    case precOut `compare` precIn of
        LT -> id                      -- If the outer precedence is lower than the inner, then
                                      -- do not add parens. E.g. in @Add x (Mul y z)@ the precedence
                                      -- of @Add@ is lower than the one of @Mul@, hence there is
                                      -- no need for parens in @x + y * z@.
        GT -> parens                  -- If the outer precedence is greater than the inner, then
                                      -- do add parens. E.g. in @Mul x (Add y z)@ the precedence
                                      -- of @Mul@ is greater than the one of @Add@, hence
                                      -- parens are needed in @x * (y + z)@.
        EQ ->                         -- If precedences are equal, then judge from associativity.
            case (assocOut, dir) of
                _ | assocOut /= assocIn     -> parens  -- Associativities differ => parens are needed.
                (LeftAssociative, Backward) -> id      -- No need for parens in @Add (Add x y) z@
                                                       -- which is rendered as @x + y + z@.
                (RightAssociative, Forward) -> id      -- No need for parens in @Concat xs (Concat xs zs)@
                                                       -- which is rendered as @xs ++ ys ++ zs@.
                _                           -> parens  -- Every other case requires parens.

class HasRenderContext config where
    renderContext :: Lens' config RenderContext

encloseM
    :: (MonadReader env m, HasPrettyConfig env config, HasRenderContext config)
    => Fixity -> Doc ann -> m (Doc ann)
encloseM fixity doc =
    view (prettyConfig . renderContext) <&> \context ->
        encloseIn context fixity doc

-- -- | Adjust a 'PrettyConfigReadable' by setting new 'Fixity' and 'Direction' and call 'prettyBy'.
-- prettyInBy
--     :: PrettyReadableBy configName a
--     => PrettyConfigReadable configName -> Direction -> Fixity -> a -> Doc ann
-- prettyInBy config dir app = prettyBy $ setRenderContext (RenderContext dir app) config

-- prettyInContextM
--     :: (MonadReader env m, HasPrettyConfig env config, HasRenderContext config, PrettyM config a)
--     => Direction -> Fixity -> a -> m (Doc ann)
-- prettyInContextM dir fixity =
--     locally (prettyConfig . renderContext) (\_ -> RenderContext dir fixity) . prettyM

-- -- | Pretty-print in 'botFixity'.
-- prettyInBotM
--     :: (MonadReader env m, HasPrettyConfig env config, HasRenderContext config, PrettyM config a)
--     => a -> m (Doc ann)
-- prettyInBotM = prettyInContextM Forward botFixity

withPrettyAt
    :: (MonadReader env m, HasPrettyConfig env config, HasRenderContext config)
    => Direction -> Fixity -> ((forall a. PrettyM config a => a -> Doc ann) -> m r) -> m r
withPrettyAt dir fixity cont = do
    config <- view prettyConfig
    cont $ prettyBy $ config & renderContext .~ RenderContext dir fixity

withPrettyIn
    :: (MonadReader env m, HasPrettyConfig env config, HasRenderContext config)
    => ((forall a. PrettyM config a => Direction -> Fixity -> a -> Doc ann) -> m r) -> m r
withPrettyIn cont = do
    config <- view prettyConfig
    cont $ \dir fixity -> prettyBy $ config & renderContext .~ RenderContext dir fixity

type AnyToDoc config ann = forall a. PrettyM config a => a -> Doc ann

compoundDoc
    :: (MonadReader env m, HasPrettyConfig env config, HasRenderContext config)
    => Fixity
    -> ((forall a. PrettyM config a => Direction -> Fixity -> a -> Doc ann) -> Doc ann)
    -> m (Doc ann)
compoundDoc fixity k = withPrettyIn $ \prettyIn -> encloseM fixity $ k prettyIn

sequenceDoc
    :: (MonadReader env m, HasPrettyConfig env config, HasRenderContext config)
    => Fixity
    -> (AnyToDoc config ann -> Doc ann)
    -> m (Doc ann)
sequenceDoc fixity k = compoundDoc fixity $ \prettyIn -> k (prettyIn Forward fixity)

-- | Instantiate a supplied continuation with two pretty-printers (one is going in the 'Backward'
-- direction, the other is in the 'Forward' direction) specialized to the supplied 'Fixity'
-- and apply 'enclose', specialized to the same 'Fixity', to the result.
-- The idea is that to the outside an expression has the same inner fixity as
-- it has the outer fixity to inner subexpressions.
infixDoc
    :: (MonadReader env m, HasPrettyConfig env config, HasRenderContext config)
    => Fixity
    -> (AnyToDoc config ann -> AnyToDoc config ann -> Doc ann)
    -> m (Doc ann)
infixDoc fixity k =
    compoundDoc fixity $ \prettyIn ->
        k (prettyIn Backward fixity) (prettyIn Forward fixity)





-- | A fixity with the lowest precedence.
-- When used as a part of an outer context, never causes addition of parens.
botFixity :: Fixity
botFixity = Fixity 0 NonAssociative

-- encloseInBot :: Doc ann -> Doc ann
-- encloseInBot = encloseIn Forward botFixity


-- -- | This class is used in order to provide default implementations of 'PrettyM' for
-- -- particular @config@s. Whenever a @Config@ is a sum type of @Subconfig1@, @Subconfig2@, etc,
-- -- we can define a single 'DefaultPrettyM' instance and then derive @PrettyM Config a@ for each
-- -- @a@ provided the @a@ implements the @PrettyM Subconfig1@, @PrettyM Subconfig2@, etc instances.
-- --
-- -- Example:
-- --
-- -- > data Config = Subconfig1 Subconfig1 | Subconfig2 Subconfig2
-- -- >
-- -- > instance (PrettyM Subconfig1 a, PrettyM Subconfig2 a) => DefaultPrettyM Config a where
-- -- >     defaultPrettyM (Subconfig1 subconfig1) = prettyBy subconfig1
-- -- >     defaultPrettyM (Subconfig2 subconfig2) = prettyBy subconfig2
-- --
-- -- Now having in scope  @PrettyM Subconfig1 A@ and @PrettyM Subconfig2 A@
-- -- and the same instances for @B@ we can write
-- --
-- -- > instance PrettyM Config A
-- -- > instance PrettyM Config B
-- --
-- -- and the instances will be derived for us.
-- class DefaultPrettyM config a where
--     defaultPrettyM :: config -> a -> Doc ann

-- -- | Overloaded configurable conversion to 'Doc'. I.e. like 'Pretty', but parameterized by a @config@.
-- -- This class is interoperable with the 'Pretty' class via 'PrettyConfigIgnore' and 'PrettyConfigAttatch'.
-- class PrettyM config a where
--     prettyBy :: config -> a -> Doc ann
--     default prettyBy :: DefaultPrettyM config a => config -> a -> Doc ann
--     prettyBy = defaultPrettyM

-- -- | A newtype wrapper around @a@ whose point is to provide a 'PrettyM config' instance
-- -- for anything that has a 'Pretty' instance.
-- newtype PrettyConfigIgnore a = PrettyConfigIgnore
--     { unPrettyConfigIgnore :: a
--     }

-- -- | A config together with some value. The point is to provide a 'Pretty' instance
-- -- for anything that has a 'PrettyM config' instance.
-- data PrettyConfigAttach config a = PrettyConfigAttach config a

-- -- delete these instances on extraction as library
-- instance PrettyM config a => PrettyM config [a] where
--     prettyBy config = list . fmap (prettyBy config)

-- instance (PrettyM config a, PrettyM config b) => PrettyM config (Either a b) where
--     prettyBy config (Left a)  = parens ("Left" <+> prettyBy config a)
--     prettyBy config (Right b) = parens ("Right" <+> prettyBy config b)

-- instance (PrettyM config a, PrettyM config b) => PrettyM config (a, b) where
--     prettyBy config (a, b) = parens (prettyBy config a <> line <> "," <+> prettyBy config b)

-- instance PrettyM config Integer where
--     prettyBy _ = pretty
-- -- delete until here

-- instance Pretty a => PrettyM config (PrettyConfigIgnore a) where
--     prettyBy _ (PrettyConfigIgnore x) = pretty x

-- instance PrettyM config a => Pretty (PrettyConfigAttach config a) where
--     pretty (PrettyConfigAttach config x) = prettyBy config x

-- -- | Render a value as 'String'.
-- prettyStringBy :: PrettyM config a => config -> a -> String
-- prettyStringBy config = docString . prettyBy config

-- -- | Render a value as strict 'Text'.
-- prettyTextBy :: PrettyM config a => config -> a -> T.Text
-- prettyTextBy config = docText . prettyBy config
