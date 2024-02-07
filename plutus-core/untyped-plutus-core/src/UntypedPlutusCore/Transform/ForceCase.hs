{-# LANGUAGE LambdaCase #-}

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

) where

import UntypedPlutusCore.Core

import Control.Lens (transformOf)


forceCase :: Term name uni fun a -> Term name uni fun a
forceCase = transformOf termSubterms processTerm

processTerm :: Term name uni fun a -> Term name uni fun a
processTerm = \case
    (Delay _ (Case _ (Constr _ i values) branches)) -> undefined
