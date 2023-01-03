{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeFamilies     #-}

{-|
Call site inlining machinery. For now there's only one part: inlining of fully applied functions.
We inline fully applied functions if the cost and size are acceptable.
-}

module PlutusIR.Transform.Inline.CallSiteInline where

import PlutusIR
import PlutusIR.Transform.Rename ()
import PlutusPrelude

-- | Count the number of type and term lambdas in the RHS of a binding
countLam ::
    Term tyname name uni fun a -- ^ the RHS
    -> (Natural, Natural) -- ^ Number of type lambdas, number of term lambdas
countLam = countLamInner 0 0
    where
      countLamInner ::
        Natural -- ^ Number of type lambdas of the function.
        -> Natural -- ^ Number of term lambdas of the function.
        -> Term tyname name uni fun a -- ^ The rhs term that is being counted.
        -> (Natural, Natural)
      countLamInner typeLambdas termLambdas (LamAbs _a _n _ty body) =
        -- If the term is a term lambda abstraction, increase the count of the number of
        -- term lambdas by one. Keep on examining the body.
        countLamInner typeLambdas (termLambdas + 1) body
      countLamInner typeLambdas termLambdas (TyAbs _a _n _kind body) =
        -- If the term is a type lambda abstraction, increase the count of the number of
        -- type lambdas by one. Keep on examining the body.
        countLamInner (typeLambdas + 1) termLambdas body
      countLamInner typeLambdas termLambdas _ =
        -- whenever we encounter a body that is not a lambda abstraction, we are done counting
        (typeLambdas, termLambdas)
