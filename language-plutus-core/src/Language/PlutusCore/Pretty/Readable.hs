-- | A "readable" Agda-like way to pretty-print PLC entities.

{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

module Language.PlutusCore.Pretty.Readable where
--     ( Associativity (..)
--     , Fixity (..)
--     , Direction (..)
--     , RenderContext (..)
--     , ShowKinds (..)
--     , PrettyConfigReadable (..)
--     , PrettyReadableBy
--     , PrettyReadable
--     , botFixity
--     , binderFixity
--     , arrowFixity
--     , juxtFixity
--     , unitFixity
--     , topFixity
--     , topPrettyConfigReadable
--     , botPrettyConfigReadable
--     , setRenderContext
--     , encloseInContext
--     , AnyToDocBy
--     , prettyInBy
--     , prettyInBotBy
--     , unitaryDoc
--     , rayDoc
--     , binderDoc
--     , compoundDoc
--     , applicationDoc
--     , arrowDoc
--     ) where

import           PlutusPrelude

import           Language.PlutusCore.Pretty.ConfigName
import           Language.PlutusCore.Pretty.PrettyM

import           Control.Lens
import           Control.Monad.Reader

data ShowKinds
    = ShowKindsYes
    | ShowKindsNo
    deriving (Show, Eq)

-- | Configuration for the readable pretty-printing.
data PrettyConfigReadable configName = PrettyConfigReadable
    { _pcrConfigName    :: configName
    , _pcrRenderContext :: RenderContext
    , _pcrShowKinds     :: ShowKinds
    }

-- | The "readably pretty-printable" constraint.
type PrettyReadableBy configName = PrettyM (PrettyConfigReadable configName)

type PrettyReadable = PrettyReadableBy PrettyConfigName

type HasPrettyConfigReadable env configName =
    HasPrettyConfig env (PrettyConfigReadable configName)

makeLenses ''PrettyConfigReadable

instance configName ~ PrettyConfigName => HasPrettyConfigName (PrettyConfigReadable configName) where
    toPrettyConfigName = _pcrConfigName

instance HasRenderContext (PrettyConfigReadable configName) where
    renderContext = pcrRenderContext

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

-- | A 'PrettyConfigReadable' with the fixity specified to 'topFixity'.
topPrettyConfigReadable :: configName -> ShowKinds -> PrettyConfigReadable configName
topPrettyConfigReadable configName = PrettyConfigReadable configName $ RenderContext Forward topFixity

-- | A 'PrettyConfigReadable' with the fixity specified to 'botFixity'.
botPrettyConfigReadable :: configName -> ShowKinds -> PrettyConfigReadable configName
botPrettyConfigReadable configName = PrettyConfigReadable configName $ RenderContext Forward botFixity

-- -- | Adjust a 'PrettyConfigReadable' by setting new 'Fixity' and 'Direction' and call 'prettyBy'.
-- prettyInBy
--     :: PrettyReadableBy configName a
--     => PrettyConfigReadable configName -> Direction -> Fixity -> a -> Doc ann
-- prettyInBy config dir app = prettyBy $ setRenderContext (RenderContext dir app) config

-- -- | Pretty-print in 'botFixity'.
-- prettyInBotBy :: PrettyReadableBy configName a => PrettyConfigReadable configName -> a -> Doc ann
-- prettyInBotBy config = prettyInBy config Forward botFixity

-- -- | Call 'encloseInContext' on 'unitFixity'.
-- unitaryDoc :: PrettyConfigReadable configName -> Doc ann -> Doc ann
-- unitaryDoc config = encloseInContext (_pcrRenderContext config) unitFixity

-- -- This perhaps makes less sense than 'compoundDoc', because to the outside binders
-- -- can look differently than how they look to the inside, but whatever.
-- -- | Instantiate a supplied continuation with a pretty-printer specialized to the supplied
-- -- 'Fixity' and apply 'encloseInContext', specialized to the same 'Fixity', to the result.
-- rayDoc
--     :: (MonadReader env m, HasPrettyConfig env config, HasRenderContext config)
--     => Direction
--     -> Fixity
--     -> (AnyToDoc config ann -> Doc ann)
--     -> m (Doc ann)
-- rayDoc dir fixity k = withPrettyIn $ \prettyIn -> encloseM fixity $ k (prettyIn dir fixity)

-- -- | 'rayDoc' specialized to 'binderFixity'.
-- binderDoc
--     :: (MonadReader env m, HasPrettyConfig env config, HasRenderContext config)
--     => (AnyToDoc config ann -> Doc ann)
--     -> m (Doc ann)
-- binderDoc = rayDoc Forward binderFixity

-- | Call 'encloseM' on 'unitFixity'.
unitaryDoc
    :: (MonadReader env m, HasPrettyConfig env config, HasRenderContext config)
    => Doc ann -> m (Doc ann)
unitaryDoc = encloseM unitFixity

-- unitaryP
--     :: ( MonadReader env m, HasPrettyConfig env config, HasRenderContext config
--        , Pretty a
--        )
--     => a -> m (Doc ann)
-- unitaryP = unitaryDoc . pretty

-- unitaryPM
--     :: ( MonadReader env m, HasPrettyConfig env config, HasRenderContext config
--        , PrettyM config a
--        )
--     => a -> m (Doc ann)
-- unitaryPM = prettyM >=> unitaryDoc
