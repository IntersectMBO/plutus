{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE UndecidableInstances   #-}

module Text.PrettyBy.Fixity where

import           Text.PrettyBy.Internal.Core
import           Text.PrettyBy.Monad

import           Data.Text.Prettyprint.Doc
import           Lens.Micro

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
    { _renderContextDirection :: !Direction
    , _renderContextFixity    :: !Fixity
    }

class HasRenderContext config where
    renderContext :: Lens' config RenderContext

type MonadPrettyContext config env m = (MonadPretty config env m, HasRenderContext config)

-- | A fixity with the lowest precedence.
-- When used as a part of an outer context, never causes addition of parens.
botFixity :: Fixity
botFixity = Fixity 0 NonAssociative

-- | The fixity of juxtaposition.
juxtFixity :: Fixity
juxtFixity = Fixity 100 LeftAssociative

-- | The fixity of a unitary expression which is safe to render
-- without parens in any context.
unitFixity :: Fixity
unitFixity = Fixity 110 NonAssociative

-- | A fixity with the highest precedence.
-- When used as a part of an outer context, always causes addition of parens.
topFixity :: Fixity
topFixity = Fixity 120 NonAssociative

botRenderContext :: RenderContext
botRenderContext = RenderContext Forward botFixity

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

encloseM
    :: MonadPrettyContext config env m
    => Fixity -> Doc ann -> m (Doc ann)
encloseM fixity doc =
    view (prettyConfig . renderContext) <&> \context ->
        encloseIn context fixity doc

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
    => Fixity
    -> (AnyToDoc config ann -> Doc ann)
    -> m (Doc ann)
sequenceDocM fixity k = compoundDocM fixity $ \prettyIn -> k (prettyIn Forward fixity)

-- | Instantiate a supplied continuation with two pretty-printers (one is going in the 'Backward'
-- direction, the other is in the 'Forward' direction) specialized to the supplied 'Fixity'
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
        k (prettyIn Backward fixity) (prettyIn Forward fixity)

juxtPrettyM
    :: (MonadPrettyContext config env m, PrettyBy config a, PrettyBy config b)
    => a -> b -> m (Doc ann)
juxtPrettyM fun arg =
    infixDocM juxtFixity $ \prettyL prettyR -> prettyL fun <+> prettyR arg




-- encloseInBot :: Doc ann -> Doc ann
-- encloseInBot = encloseIn Forward botFixity

-- -- | Adjust a 'PrettyConfigReadable' by setting new 'Fixity' and 'Direction' and call 'prettyBy'.
-- prettyInBy
--     :: PrettyReadableBy configName a
--     => PrettyConfigReadable configName -> Direction -> Fixity -> a -> Doc ann
-- prettyInBy config dir app = prettyBy $ setRenderContext (RenderContext dir app) config

-- prettyInContextM
--     :: (MonadPrettyContext config env m, PrettyBy config a)
--     => Direction -> Fixity -> a -> m (Doc ann)
-- prettyInContextM dir fixity =
--     locally (prettyConfig . renderContext) (\_ -> RenderContext dir fixity) . prettyM

-- -- | Pretty-print in 'botFixity'.
-- prettyInBotM
--     :: (MonadPrettyContext config env m, PrettyBy config a)
--     => a -> m (Doc ann)
-- prettyInBotM = prettyInContextM Forward botFixity
