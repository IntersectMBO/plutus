{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}

module PrettyM
    ( Sole (..)
    , HasPrettyConfig (..)
    , DefaultPrettyM (..)
    , PrettyM (..)
    , prettyBy
    , PrettyConfigIgnore (..)
    , PrettyConfigAttach (..)
    ) where

import           Control.Lens
import           Control.Monad.Reader
import           Data.Text.Prettyprint.Doc

newtype Sole config = Sole
    { unSole :: config
    }

class HasPrettyConfig env config | env -> config where
    prettyConfig :: Lens' env config

instance HasPrettyConfig (Sole config) config where
    prettyConfig = undefined

class DefaultPrettyM config a where
    defaultPrettyM :: (MonadReader env m, HasPrettyConfig env config) => a -> m (Doc ann)

class PrettyM config a where
    prettyM :: (MonadReader env m, HasPrettyConfig env config) => a -> m (Doc ann)
    default prettyM
        :: (MonadReader env m, HasPrettyConfig env config, DefaultPrettyM config a)
        => a -> m (Doc ann)
    prettyM = defaultPrettyM

prettyBy :: PrettyM config a => config -> a -> Doc ann
prettyBy = flip prettyM . Sole

-- | A newtype wrapper around @a@ whose point is to provide a @PrettyM config@ instance
-- for anything that has a 'Pretty' instance.
newtype PrettyConfigIgnore a = PrettyConfigIgnore
    { unPrettyConfigIgnore :: a
    }

data NoPrettyConfig = NoPrettyConfig

newtype InNoPrettyConfig a = InNoPrettyConfig
    { unInNoPrettyConfig :: a
    }

-- | A config together with some value. The point is to provide a 'Pretty' instance
-- for anything that has a @PrettyM config@ instance.
data PrettyConfigAttach config a = PrettyConfigAttach config a

instance Pretty a => PrettyM config (PrettyConfigIgnore a) where
    prettyM = pure . pretty . unPrettyConfigIgnore

instance PrettyM NoPrettyConfig a => Pretty (InNoPrettyConfig a) where
    pretty = prettyBy NoPrettyConfig . unInNoPrettyConfig

instance PrettyM config a => Pretty (PrettyConfigAttach config a) where
    pretty (PrettyConfigAttach config x) = prettyBy config x

withPrettyConfig
    :: (MonadReader env m, HasPrettyConfig env config)
    => (config -> c) -> m c
withPrettyConfig k = asks $ k . view prettyConfig

withPrettyAttach
    :: (MonadReader env m, HasPrettyConfig env config)
    => ((forall a. a -> PrettyConfigAttach config a) -> c) -> m c
withPrettyAttach k = withPrettyConfig $ \config -> k $ PrettyConfigAttach config

prettyFunctorM
    :: ( MonadReader env m, HasPrettyConfig env config
       , Functor f, forall b. Pretty b => Pretty (f b), PrettyM config a
       )
    => f a -> m (Doc ann)
prettyFunctorM a = withPrettyAttach $ \attach -> pretty $ attach <$> a

instance PrettyM config a => PrettyM config [a] where
    prettyM = prettyFunctorM

instance PrettyM config a => PrettyM config (Maybe a) where
    prettyM = prettyFunctorM



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
    { _fixityPrecedence    :: Double
    , _fixityAssociativity :: Associativity
    }

-- | Determines whether we're going to the right of an operator or to the left.
data Direction
    = Forward   -- ^ To the right.
    | Backward  -- ^ To the left.
    deriving (Eq)

-- | A context that an expression is being rendered in.
data RenderContext = RenderContext
    { _rcDirection :: Direction
    , _rcFixity    :: Fixity
    }

-- | A fixity with the lowest precedence.
-- When used as a part of an outer context, never causes addition of parens.
botFixity :: Fixity
botFixity = Fixity 0 NonAssociative

-- | The fixity of a binder.
binderFixity :: Fixity
binderFixity = Fixity 1 RightAssociative

-- | The fixity of @(->)@.
arrowFixity :: Fixity
arrowFixity = Fixity 2 RightAssociative

-- | The fixity of juxtaposition.
juxtFixity :: Fixity
juxtFixity = Fixity 10 LeftAssociative

-- | The fixity of a unitary expression which is safe to render
-- without parens in any context.
unitFixity :: Fixity
unitFixity = Fixity 11 NonAssociative

-- | A fixity with the highest precedence.
-- When used as a part of an outer context, always causes addition of parens.
topFixity :: Fixity
topFixity = Fixity 12 NonAssociative

-- | Enclose a 'Doc' in parens if required or leave it as is.
-- The need for enclosing is determined from an outer 'RenderContext' and the 'Doc's fixity.
encloseInContext
    :: RenderContext  -- ^ An outer context.
    -> Fixity         -- ^ An inner fixity.
    -> Doc ann
    -> Doc ann
encloseInContext (RenderContext dir (Fixity precOut assocOut)) (Fixity precIn assocIn) =
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

-- -- | The "readably pretty-printable" constraint.
-- type PrettyReadableBy configName = PrettyBy (PrettyConfigReadable configName)

-- type PrettyReadable = PrettyReadableBy PrettyConfigName

-- type AnyToDocBy configName ann = forall a. PrettyReadableBy configName a => a -> Doc ann

-- -- | Adjust a 'PrettyConfigReadable' by setting new 'Fixity' and 'Direction' and call 'prettyBy'.
-- prettyInBy
--     :: PrettyReadableBy configName a
--     => PrettyConfigReadable configName -> Direction -> Fixity -> a -> Doc ann
-- prettyInBy config dir app = prettyBy $ setRenderContext (RenderContext dir app) config


class HasRenderContext config render | config -> render where
    renderContext :: Lens' config render


prettyInM
    :: (MonadReader env m, HasPrettyConfig env config, HasRenderContext config render)
    => Direction -> Fixity -> a -> m (Doc ann)
prettyInM = undefined

-- | Pretty-print in 'botFixity'.
prettyInBotM
    :: (MonadReader env m, HasPrettyConfig env config, HasRenderContext config render)
    => a -> m (Doc ann)
prettyInBotM = prettyInM Forward botFixity

-- -- | Call 'encloseInContext' on 'unitFixity'.
-- unitaryDoc :: PrettyConfigReadable configName -> Doc ann -> Doc ann
-- unitaryDoc config = encloseInContext (_pcrRenderContext config) unitFixity

type AnyToDocM config m ann = forall a. PrettyM config a => a -> m (Doc ann)

encloseInContextM
    :: (MonadReader env m, HasPrettyConfig env config, HasRenderContext config render)
    => Fixity -> Doc ann -> m (Doc ann)
encloseInContextM = undefined

-- | Instantiate a supplied continuation with two pretty-printers (one is going in the 'Backward'
-- direction, the other is in the 'Forward' direction) specialized to the supplied 'Fixity'
-- and apply 'encloseInContext', specialized to the same 'Fixity', to the result.
-- The idea is that to the outside an expression has the same inner fixity as
-- it has the outer fixity to inner subexpressions.
compoundDoc
    :: (MonadReader env m, HasPrettyConfig env config, HasRenderContext config render)
    => Fixity
    -> (AnyToDocM config m ann -> AnyToDocM config m ann -> m (Doc ann))
    -> m (Doc ann)
compoundDoc fixity k =
    k (prettyInM Backward fixity) (prettyInM Forward fixity) >>= encloseInContextM fixity
