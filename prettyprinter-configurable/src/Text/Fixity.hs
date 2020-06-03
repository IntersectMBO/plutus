module Text.Fixity
    ( Precedence
    , Associativity (..)
    , FixityOver (..)
    , Fixity
    , Direction (..)
    , RenderContextOver (..)
    , RenderContext
    , encloseIn
    , botFixity
    , juxtFixity
    , unitFixity
    , topFixity
    , botRenderContext
    , topRenderContext
    ) where

import           Text.Fixity.Internal

-- | Fractional precedence, so that it's always possible to squeeze an operator precedence between
-- two existing precedences. Ranges over @[-20, 120]@. A normal operator should have a precedence
-- within @[0, 100)@. It might be useful to have a negative precedence if you're trying to model
-- some already existing system, for example in Haskell @($)@ has precedence @0@, but clearly
-- @if b then y else f $ x@ should be rendered without any parens, hence the precedence of
-- @if_then_else_@ is less than 0, i.e. negative.
--
-- The precedence of juxtaposition is @100@. Normally you want juxtaposition to have the highest
-- precedence, but some languages have operators that bind tighter than juxtaposition, e.g.
-- Haskell's postfix @_{_}@: @f z { x = y }@ means @f (z {x = y})@.
type Precedence = Double

-- | 'FixityOver' instantiated at 'Precedence'.
type Fixity = FixityOver Precedence

-- | 'FixityOver' instantiated at 'Precedence'.
type RenderContext = RenderContextOver Precedence

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

-- | An initial 'RenderContext'.
-- An expression printed in this context never gets enclosed in parens.
botRenderContext :: RenderContext
botRenderContext = RenderContext ToTheRight botFixity

-- | An initial 'RenderContext'.
-- An expression printed in this context always gets enclosed in parens.
topRenderContext :: RenderContext
topRenderContext = RenderContext ToTheRight topFixity
