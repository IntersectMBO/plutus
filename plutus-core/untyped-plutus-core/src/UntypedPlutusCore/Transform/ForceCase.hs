{-# LANGUAGE BangPatterns   #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE NamedFieldPuns #-}

{- | We want to push 'Force' applied at the top of 'Case' terms into the 'Case' branches.
This transformation is unsound in general, but it can be done for the particular case when
the term matches:

@
force
    ( case
        (constr i [v1 ... vn])
        [ \x11 ... x1n -> delay body1
        , \x21 ... x2n -> delay body2
        ...
        , \xm1 ... xmn -> delay bodym
        ]
    )
@

The optimised term will therefore be:
@
case
    (constr i [v1 ... vn])
    [ \x11 ... x1n -> force (delay body1)
    , \x21 ... x2n -> force (delay body2)
    ...
    , \xm1 ... xmn -> force (delay bodym)
    ]
@

This transformation will allow the "ForceDelay" optimisation to apply to the resulting term.

The following shows that the optimised and unoptimised terms reduce to the same term,
making this particular transformation sound.

@
force
    ( case
        (constr i [v1 ... vn])
        [ \x11 ... x1n -> delay body1
        , \x21 ... x2n -> delay body2
        ...
        , \xm1 ... xmn -> delay bodym
        ]
    )
=>
force ((\xi1 ... xin -> delay bodyi) [v1 ... vn])
=>
force ((delay bodyi)[V/X]) <--equiv--> force (delay bodyi[V/X])
=>
bodyi[V/X]

------

force
    ( case
        (constr i [v1 ... vn])
        [ \x11 ... x1n -> delay body1
        , \x21 ... x2n -> delay body2
        ...
        , \xm1 ... xmn -> delay bodym
        ]
    )
--optim-->
case
    (constr i [v1 ... vn])
    [ \x11 ... x1n -> force (delay body1)
    , \x21 ... x2n -> force (delay body2)
    ...
    , \xm1 ... xmn -> force (delay bodym)
    ]
=> (\xi1 ... xin -> force (delay bodyi)) [v1 ... vn]
=> (force (delay bodyi))[V/X] <--equiv--> force (delay bodyi[V/X])
=> bodyi[V/X]
@

The above doesn't hold if the constructor contains a number of values less than
the number of abstractions at the top of the term:

@
force ((\xi1 ... xin -> delay bodyi) [v1 ... v(n-1)])
=>
force ((xin -> (delay bodyi)[V'/X])) <--equiv--> force (xin -> delay (bodyi[V'/X]))

------

(\xi1 ... xin -> force (delay bodyi)) [v1 ... v(n-1)]
=>
(\xin -> force (delay bodyi))[V'/X] <--equiv--> (\xin -> force (delay bodyi[V'/X]))
=>
(\xin -> bodyi[V'/X])
@

The two terms are not equivalent.


What happens if there are more values?

@
force ((\xi1 ... xin -> delay bodyi) [v1 ... vn v(n+1)])
=>
force (((delay bodyi)[V/X]) v(n+1)) <--equiv--> force ((delay (bodyi[V/X])) v(n+1))

------

(\xi1 ... xin -> force (delay bodyi)) [v1 ... vn v(n+1)]
=>
(force (delay bodyi))[V/X] v(n+1) <--equiv--> (force (delay bodyi[V/X])) v(n+1)
=>
bodyi[V/X] v(n+1)
@

Again, the two terms are not equivalent, so we can only apply the optimisation in the case
where the number of values is equal to the number of abstractions at the top.
-}
module UntypedPlutusCore.Transform.ForceCase (
    forceCase,
) where

import UntypedPlutusCore.Core

import Control.Lens (transformOf)
import Control.Monad (guard)
import Data.List (foldl')
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (mapMaybe)

{- | Traverses the term, potentially applying the force-case optimisation
 as described in the module's documentation.
-}
forceCase :: Term name uni fun a -> Term name uni fun a
forceCase = transformOf termSubterms processTerm

-- | Checks whether the preconditions apply and processes the term accordingly.
processTerm :: Term name uni fun a -> Term name uni fun a
processTerm original =
    case original of
        (Force annForce (Case annCase (Constr annConstr i terms) branches)) ->
            let
                optimisedBranches =
                    mapMaybe (optimiseBranch (length terms) annForce) branches
                allBranchesAreOptimised =
                    length optimisedBranches == length branches
             in
                if allBranchesAreOptimised
                    then Case annCase (Constr annConstr i terms) optimisedBranches
                    else original
        _ -> original

{- | An internalised representation of a term with multiple lambda abstractions
 at the top.
-}
data MultiLamAbs name uni fun ann = MultiLamAbs
    { vars :: NonEmpty (ann, name)
    -- ^ the bound variables in the multiple lambda abstraction
    , rhs  :: Term name uni fun ann
    -- ^ the right hand side of the multiple lambda abstraction
    }

{- | Traverse the 'Term' top down and accumulate all the top-level, consecutive
 lambda abstractions, forming a 'MultiLamAbs' where the 'rhs' is the remaining subterm.
-}
toMultiLamAbs
    :: Term name uni fun ann
    -> Maybe (MultiLamAbs name uni fun ann)
toMultiLamAbs = \case
    LamAbs ann name subTerm ->
        Just $ run (NonEmpty.singleton (ann, name)) subTerm
    _ -> Nothing
  where
    run
        :: NonEmpty (ann, name)
        -> Term name uni fun ann
        -> MultiLamAbs name uni fun ann
    run !ne (LamAbs ann' name' subTerm') =
        run (NonEmpty.cons (ann', name') ne) subTerm'
    run ne term = MultiLamAbs ne term

-- | Rebuild the 'Term' by applying the lambda abstractions in order.
fromMultiLamAbs
    :: MultiLamAbs name uni fun ann
    -> Term name uni fun ann
fromMultiLamAbs MultiLamAbs { vars, rhs } =
    foldl' toLamAbs rhs vars
  where
    toLamAbs t (ann, name) = LamAbs ann name t

-- | Returns the number of lambda abstractions in the 'MultiLamAbs'.
multiLamAbsArity :: MultiLamAbs name uni fun ann -> Int
multiLamAbsArity MultiLamAbs { vars } = NonEmpty.length vars

-- | Helper function for adding a 'Force' on top of the 'rhs'.
pushForce :: ann -> MultiLamAbs name uni fun ann -> MultiLamAbs name uni fun ann
pushForce ann multiLamAbs = multiLamAbs { rhs = Force ann (rhs multiLamAbs) }

-- | Potentially optimises a branch as long as the preconditions are satisfied.
optimiseBranch :: Int -> ann -> Term name uni fun ann -> Maybe (Term name uni fun ann)
optimiseBranch numberOfApplications ann branch = do
    branch' <- toMultiLamAbs branch
    guard (multiLamAbsArity branch' == numberOfApplications)
    pure (fromMultiLamAbs . pushForce ann $ branch')
