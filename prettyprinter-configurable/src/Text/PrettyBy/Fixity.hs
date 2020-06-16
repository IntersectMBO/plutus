{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}

-- | Configurable precedence-aware pretty-printing.
--
-- Look into @test/Expr.hs@ for an extended example.

module Text.PrettyBy.Fixity
    ( module Export
    , module Text.PrettyBy.Fixity
    ) where

import           Text.Fixity                  as Export
import           Text.Pretty
import           Text.PrettyBy.Internal
import           Text.PrettyBy.Internal.Utils
import           Text.PrettyBy.Monad          as Export

import           Control.Monad.Reader
import           Data.String
import           Lens.Micro

-- | A constraint for \"'RenderContext' is a part of @config@\".
class HasRenderContext config where
    renderContext :: Lens' config RenderContext

instance HasRenderContext RenderContext where
    renderContext = id

-- | A constraint for \"@m@ is a 'Monad' supporting configurable precedence-aware pretty-printing\".
type MonadPrettyContext config env m = (MonadPretty config env m, HasRenderContext config)

-- | A @newtype@ wrapper around @a@ introduced for its 'HasPrettyConfig' instance.
newtype Sole a = Sole
    { unSole :: a
    }

-- | It's not possible to have @HasPrettyConfig config config@, because that would mean that every
-- environment is a pretty-printing config on its own, which doesn't make sense. We could have an
-- OVERLAPPABLE instance, but I'd rather not.
instance HasPrettyConfig (Sole config) config where
    prettyConfig f (Sole x) = Sole <$> f x

-- | A monad for precedence-aware pretty-printing.
newtype InContextM config a = InContextM
    { unInContextM :: Reader (Sole config) a
    } deriving newtype (Functor, Applicative, Monad, MonadReader (Sole config))

-- | Run 'InContextM' by supplying a @config@.
runInContextM :: config -> InContextM config a -> a
runInContextM config (InContextM a) = runReader a $ Sole config

-- | Takes a monadic pretty-printer and turns it into one that receives a @config@ explicitly.
-- Useful for defining instances of 'PrettyBy' monadically when writing precedence-aware
-- pretty-printing code (and since all functions below are monadic, it's currenty the only option).
inContextM :: (a -> InContextM config (Doc ann)) -> config -> a -> Doc ann
inContextM pM config = runInContextM config . pM

-- | A string written in the 'InContextM' monad gets enclosed with 'unitDocM' automatically.
instance (HasRenderContext config, doc ~ Doc ann) => IsString (InContextM config doc) where
    fromString = unitDocM . fromString

-- TODO: when writing a precedence-aware pretty-printer we basically always want to specify a
-- fixity in each clause. Would be nice to enforce that in types.
-- | Enclose a 'Doc' in parentheses if required or leave it as is. The need for enclosing is
-- determined from an outer 'RenderContext' (stored in the environment of the monad) and the inner
-- fixity provided as an argument.
encloseM :: MonadPrettyContext config env m => Fixity -> Doc ann -> m (Doc ann)
encloseM fixity doc =
    view (prettyConfig . renderContext) <&> \context ->
        encloseIn parens context fixity doc

-- | The type of a general @config@-based pretty-printer.
type AnyToDoc config ann = forall a. PrettyBy config a => a -> Doc ann

-- | Instantiate a supplied continuation with a precedence-aware pretty-printer.
withPrettyIn
    :: MonadPrettyContext config env m
    => ((forall a. PrettyBy config a => Direction -> Fixity -> a -> Doc ann) -> m r) -> m r
withPrettyIn cont = do
    config <- view prettyConfig
    cont $ \dir fixity -> prettyBy $ config & renderContext .~ RenderContext dir fixity

-- | Instantiate a supplied continuation with a pretty-printer specialized to supplied
-- 'Fixity' and 'Direction'.
withPrettyAt
    :: MonadPrettyContext config env m
    => Direction -> Fixity -> (AnyToDoc config ann -> m r) -> m r
withPrettyAt dir fixity cont = withPrettyIn $ \prettyIn -> cont $ prettyIn dir fixity

-- | Call 'encloseM' on 'unitFixity'.
unitDocM :: MonadPrettyContext config env m => Doc ann -> m (Doc ann)
unitDocM = encloseM unitFixity

-- | Instantiate a supplied continuation with a pretty-printer and apply 'encloseM',
-- specialized to supplied 'Fixity', to the result.
compoundDocM
    :: MonadPrettyContext config env m
    => Fixity
    -> ((forall a. PrettyBy config a => Direction -> Fixity -> a -> Doc ann) -> Doc ann)
    -> m (Doc ann)
compoundDocM fixity k = withPrettyIn $ \prettyIn -> encloseM fixity $ k prettyIn

-- | Instantiate a supplied continuation with a pretty-printer specialized to supplied
-- 'Fixity' and 'Direction' and apply 'encloseM' specialized to the provided fixity to the result.
-- This can be useful for pretty-printing a sequence of values (possibly consisting of a single
-- value).
sequenceDocM
    :: MonadPrettyContext config env m
    => Direction -> Fixity -> (AnyToDoc config ann -> Doc ann) -> m (Doc ann)
sequenceDocM dir fixity k = compoundDocM fixity $ \prettyIn -> k $ prettyIn dir fixity

-- | Instantiate a supplied continuation with two pretty-printers (one is going in the 'ToTheLeft'
-- direction, the other is in the 'ToTheRight' direction) specialized to supplied 'Fixity'
-- and apply 'encloseM', specialized to the same fixity, to the result.
-- The idea is that to the outside an infix operator has the same inner fixity as
-- it has the outer fixity to inner subexpressions.
infixDocM
    :: MonadPrettyContext config env m
    => Fixity
    -> (AnyToDoc config ann -> AnyToDoc config ann -> Doc ann)
    -> m (Doc ann)
infixDocM fixity k =
    compoundDocM fixity $ \prettyIn ->
        k (prettyIn ToTheLeft fixity) (prettyIn ToTheRight fixity)

-- | Pretty-print two things with a space between them. The fixity of the context in which the
-- arguments get pretty-printed is set to 'juxtFixity'.
juxtPrettyM
    :: (MonadPrettyContext config env m, PrettyBy config a, PrettyBy config b)
    => a -> b -> m (Doc ann)
juxtPrettyM fun arg =
    infixDocM juxtFixity $ \prettyL prettyR -> prettyL fun <+> prettyR arg
