{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}

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

class HasRenderContext config where
    renderContext :: Lens' config RenderContext

instance HasRenderContext RenderContext where
    renderContext = id

type MonadPrettyContext config env m = (MonadPretty config env m, HasRenderContext config)

newtype InContextM config a = InContextM
    { unInContextM :: Reader (Sole config) a
    } deriving newtype (Functor, Applicative, Monad, MonadReader (Sole config))

runInContextM :: config -> InContextM config a -> a
runInContextM config (InContextM a) = runReader a $ Sole config

inContextM :: (a -> InContextM config (Doc ann)) -> config -> a -> Doc ann
inContextM pM config = runInContextM config . pM

instance (HasRenderContext config, doc ~ Doc ann) => IsString (InContextM config doc) where
    fromString = unitDocM . fromString

-- TODO: try a type-changing version.
encloseM
    :: MonadPrettyContext config env m
    => Fixity -> Doc ann -> m (Doc ann)
encloseM fixity doc =
    view (prettyConfig . renderContext) <&> \context ->
        encloseIn parens context fixity doc

withPrettyIn
    :: MonadPrettyContext config env m
    => ((forall a. PrettyBy config a => Direction -> Fixity -> a -> Doc ann) -> m r) -> m r
withPrettyIn cont = do
    config <- view prettyConfig
    cont $ \dir fixity -> prettyBy $ config & renderContext .~ RenderContext dir fixity

withPrettyAt
    :: MonadPrettyContext config env m
    => Direction -> Fixity -> ((forall a. PrettyBy config a => a -> Doc ann) -> m r) -> m r
withPrettyAt dir fixity cont = withPrettyIn $ \prettyIn -> cont $ prettyIn dir fixity

type AnyToDoc config ann = forall a. PrettyBy config a => a -> Doc ann

-- | Call 'encloseM' on 'unitFixity'.
unitDocM :: MonadPrettyContext config env m => Doc ann -> m (Doc ann)
unitDocM = encloseM unitFixity

compoundDocM
    :: MonadPrettyContext config env m
    => Fixity
    -> ((forall a. PrettyBy config a => Direction -> Fixity -> a -> Doc ann) -> Doc ann)
    -> m (Doc ann)
compoundDocM fixity k = withPrettyIn $ \prettyIn -> encloseM fixity $ k prettyIn

sequenceDocM
    :: MonadPrettyContext config env m
    => Direction
    -> Fixity
    -> (AnyToDoc config ann -> Doc ann)
    -> m (Doc ann)
sequenceDocM dir fixity k = compoundDocM fixity $ \prettyIn -> k (prettyIn dir fixity)

-- | Instantiate a supplied continuation with two pretty-printers (one is going in the 'ToTheLeft'
-- direction, the other is in the 'ToTheRight' direction) specialized to the supplied 'Fixity'
-- and apply 'enclose', specialized to the same 'Fixity', to the result.
-- The idea is that to the outside an expression has the same inner fixity as
-- it has the outer fixity to inner subexpressions.
infixDocM
    :: MonadPrettyContext config env m
    => Fixity
    -> (AnyToDoc config ann -> AnyToDoc config ann -> Doc ann)
    -> m (Doc ann)
infixDocM fixity k =
    compoundDocM fixity $ \prettyIn ->
        k (prettyIn ToTheLeft fixity) (prettyIn ToTheRight fixity)

juxtPrettyM
    :: (MonadPrettyContext config env m, PrettyBy config a, PrettyBy config b)
    => a -> b -> m (Doc ann)
juxtPrettyM fun arg =
    infixDocM juxtFixity $ \prettyL prettyR -> prettyL fun <+> prettyR arg
