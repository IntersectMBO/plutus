{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

{-|
Call site inlining machinery. For now there's only one part: inlining of fully applied functions.
We inline fully applied functions if the cost and size are acceptable. (See
import PlutusIR.Transform.Inline.acceptable and
note [Inlining of fully applied/saturated functions])
We check whether a function is fully applied by counting, for both types and terms,
the numbers of lambdas and arguments applied. See note
[Determining whether a function is fully applied].
-}

module PlutusIR.Transform.CallSiteInline where

import PlutusIR
import PlutusIR.Analysis.Dependencies qualified as Deps
import PlutusIR.Analysis.Usages qualified as Usages
import PlutusIR.MkPir (mkLet)
import PlutusIR.Purity (isPure)
import PlutusIR.Transform.Inline
import PlutusIR.Transform.Rename ()
import PlutusPrelude

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.InlineUtils
import PlutusCore.Name
import PlutusCore.Quote
import PlutusCore.Rename (Dupable, dupable, liftDupable)
import PlutusCore.Subst (typeSubstTyNamesM)

import Control.Lens hiding (Strict)
import Control.Monad.Reader
import Control.Monad.State

import Algebra.Graph qualified as G
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as Map
import Data.Semigroup.Generic (GenericSemigroupMonoid (..))
import Witherable (Witherable (wither))

{- Note [Inlining of fully applied/saturated functions]

What is happening:

In this inline pass we check for a binding with RHS that has a
lambda abstraction for terms or types (`LamAbs` or `TyAbs`). E.g.

let v = rhs in body

We pattern match the _rhs_ with `LamAbs` or `TyAbs`, and count the number of lambdas.
Then, in the _body_, we check for term or type application (`Apply` or `TyInst`)of _v_.
If _v_ is fully applied, we inline _v_, i.e., replace its occurrence with _rhs_. E.g.,



 -}

{- Note [Determining whether a function is fully applied]

How do we determine whether a function is fully applied. Let's focus with terms only,
the same applies to types.

The notion of arity:

Arity is relevant when we talk about a fully applied function.
A fully applied function has arity of 0.
The arity of a function is the number of arguments it takes, e.g.,

\x.\y.x+y has an arity of 2

What about function application?

(\x.\y.x+y) 4

With beta-reduction, it becomes

\y.4+y and it has an arity of 1.

Optimization:
Beta-reduction of rhs is run first. This will catch more functions.

 -}
