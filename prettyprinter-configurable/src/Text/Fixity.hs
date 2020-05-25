{-# LANGUAGE PatternSynonyms #-}

module Text.Fixity
    ( Precedence
    , Associativity (..)
    , Arity
    , Fixity
    , Direction (..)
    , RenderContext
    , pattern RenderContext
    , nullary
    , unary
    , prefix
    , postfix
    , binary
    , Internal.encloseIn
    , botFixity
    , juxtFixity
    , unitFixity
    , topFixity
    , botRenderContext
    , topRenderContext
    ) where

import           Text.Fixity.Internal (Associativity (..), Direction (..), pattern RenderContext, binary, nullary,
                                       postfix, prefix, unary)
import qualified Text.Fixity.Internal as Internal

type Precedence = Double

type Arity = Internal.Arity Precedence

type Fixity = Internal.Fixity Precedence

type RenderContext = Internal.RenderContext Precedence

-- | A fixity with the lowest precedence.
-- When used as a part of an outer context, never causes addition of parens.
botFixity :: Fixity
botFixity = nullary NonAssociative (-20)

-- | The fixity of juxtaposition.
juxtFixity :: Fixity
juxtFixity = binary LeftAssociative 100

-- | The fixity of a unitary expression which is safe to render
-- without parens in any context.
unitFixity :: Fixity
unitFixity = nullary NonAssociative 110

-- | A fixity with the highest precedence.
-- When used as a part of an outer context, always causes addition of parens.
topFixity :: Fixity
topFixity = nullary NonAssociative 120

botRenderContext :: RenderContext
botRenderContext = RenderContext ToTheRight botFixity

topRenderContext :: RenderContext
topRenderContext = RenderContext ToTheRight topFixity
