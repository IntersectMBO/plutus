{-# LANGUAGE PatternSynonyms #-}

module Text.Fixity
    ( Precedence
    , Associativity (..)
    , Fixity
    , pattern Fixity
    , Direction (..)
    , RenderContext
    , pattern RenderContext
    , Internal.encloseIn
    , botFixity
    , juxtFixity
    , unitFixity
    , topFixity
    , botRenderContext
    , topRenderContext
    ) where

import           Text.Fixity.Internal (Associativity (..), Direction (..), pattern Fixity, pattern RenderContext)
import qualified Text.Fixity.Internal as Internal

type Precedence = Double

type Fixity = Internal.Fixity Precedence

type RenderContext = Internal.RenderContext Precedence

-- | A fixity with the lowest precedence.
-- When used as a part of an outer context, never causes addition of parens.
botFixity :: Fixity
botFixity = Fixity NonAssociative (-20)

-- | The fixity of juxtaposition.
juxtFixity :: Fixity
juxtFixity = Fixity LeftAssociative 100

-- | The fixity of a unitary expression which is safe to render
-- without parens in any context.
unitFixity :: Fixity
unitFixity = Fixity NonAssociative 110

-- | A fixity with the highest precedence.
-- When used as a part of an outer context, always causes addition of parens.
topFixity :: Fixity
topFixity = Fixity NonAssociative 120

botRenderContext :: RenderContext
botRenderContext = RenderContext ToTheRight botFixity

topRenderContext :: RenderContext
topRenderContext = RenderContext ToTheRight topFixity
