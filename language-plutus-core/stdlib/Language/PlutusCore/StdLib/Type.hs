-- | This module defines Haskell data types that simplify construction of PLC types and terms.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeFamilies      #-}

module Language.PlutusCore.StdLib.Type
    ( RecursiveType (..)
    , makeRecursiveType
    ) where

import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type
import           PlutusPrelude

{- Note [Arity of patterns functors]
The arity of a pattern functor is the number of arguments the pattern functor receives in addition
to the first argument representing the recursive case. So
@f :: * -> *@                           has arity 0
@f :: (k -> *) -> k -> *@               has arity 1
@f :: (k1 -> k2 -> *) -> k1 -> k2 -> *@ has arity 2
etc
-}

{- Note [InterList]
This data type is much like the 'list' data type, but it receives two types arguments rather than one
and "interleaves" them (see 'example_InterList').

    data InterList a b
        = InterNil
        | InterCons a b (InterList b a)

    example_InterList :: InterList Char Int
    example_InterList = InterCons 'a' 1 . InterCons 2 'b' . InterCons 'c' 3 $ InterNil

The data type is interesting, because we need some way of getting

    fix2 :: ((k1 -> k2 -> *) -> k1 -> k2 -> *) -> k1 -> k2 -> *

in order to encode it directly, so we use this data type in examples in order to show admissibility
of 'fix2' which is an instance of the more generic

    fix :: (k -> k) -> k

I.e. we show how the more generic 'fix' can be encoded for any particular 'k' by taking
@k ~ (k1 -> k2 -> *)@ as example and constructing 'fix2'.
-}

{- Note [Natural representation]
Having @fix :: (* -> *) -> *@ we can easily define the @list@ data type as a fixed point of
an appropriate pattern functor:

    listF = \(a :: *) (list :: *) -> all (r :: *). r -> (a -> list -> r) -> r
    list  = \(a :: *) -> fix (listF a) a

There are a few problems with this definition however:

1. In @listF@ there is no indication that @list@ is supposed to contain elements of type @a@.
So @listF@ binds both @a@ and @list@, but does not specify there is a relation between these two
things. The burden of connecting @a@ and @list@ together is on the caller, which is not a big deal,
because the only callers are @fix@, in terms of which the data type is defined, and @wrap@ that
allows to define the constructors of the data type, but still, this way the code looks strangely
structured.

2. Related to 1: such encoding diverges from what one would write having a data construction
machinery. A standard Haskell definition would be

    data List a
        = Nil
        | Cons a (List a)

In this definition we explicitly apply @List@ to @a@ in the @Cons@ case. Thus, the encoding looks
somewhat unnatural.

3. @wrap@ constructing a @list@ must carry @listF a@ in the same way @fix@ carries it. This makes
it very hard to construct terms using the AST directly as shown in
@plutus/language-plutus-core/docs/Holed types.md@.

4. There are data types that can't be defined this way. See Note [InterList] for one example.

There is however an approach that allows to encode data types in a "natural" way, does not cause
any trouble while constructing data types and can handle much more data types than what is shown
above. Here is how the @list@ example looks like with it:

    listF = \(list :: * -> *) (a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r
    list  = \(a :: *) -> fix listF a

I.e. instead of tying the knot over @list :: *@ we tie the knot over @list :: * -> *@. This simple
trick solves all the problems described avove.

But the code is actually ill-kinded. The reason for this is that @fix :: (* -> *) -> *@ is no longer
enough, because we're taking a fixed point of a pattern functor of kind @(* -> *) -> * -> *@
rather than just @* -> *@. Hence we need a more permissive fixed-point operator.

Read next: Note [The kind of fix].
-}

{- Note [The kind of fix]
In Note [Natural representation] we concluded that @fix :: (* -> *) -> *@ is not enough to encode
@list@ in a satisfying way. In that particular case it would be enough to have

    fix :: ((* -> *) -> * -> *) -> * -> *

but what about other cases? The example from Note [InterList] requires

    fix :: ((* -> * -> *) -> * -> * -> *) -> * -> * -> *

and of course we still need

    fix :: (* -> *) -> *

occasionally. This suggests to change the kind signature of @fix@ to

    fix :: (k -> k) -> k

which covers all those cases. However,

1. It also can be instantiated as @fix :: (size -> size) -> size@ which doesn't make sense.
2. It's not clear how to implement such @fix@. See <TODO_add_link> for details.

But it turns out that

    ifix :: ((k -> *) -> k -> *) -> k -> *

is enough for all cases.

Read next: Note [Packing n-ary pattern functors semantically].
-}

{- Note [Packing n-ary pattern functors semantically]
An n-ary pattern functor has the following generic signature:

    patN :: k -> k

where @k@ is of the @k1 -> k2 -> ... -> *@ form. We need to encode 'patN' as an equivalent 1-ary
pattern functor with this signature:

    pat1 :: ((k' -> *) -> k' -> *

because that's what 'ifix' accepts.

@plutus/docs/fomega/mutual-type-level-recursion/IFixIsEnough.agda@ describes the encoding trick
at great detail, but let's look at an example here. The pattern functor of 'InterList'
(see Note [InterList]) is defined as

    interlistF =
        \(interlist :: * -> * -> *) (a :: *) (b :: *) ->
            all (r :: *). r -> (a -> b -> interlist b a -> r) -> r

We can't pass the pattern functor to 'ifix', because it's of kind

    ((* -> * -> *) -> * -> * -> *) -> * -> * -> *

So we're going to "pack" the pattern functor to make it a 1-ary one. The idea is simple:
instead of passing two arguments to the recursive case, we pass a single continuation that applies
a function it receives to those two arguments. Morever, we can define the packed version of
'interlistF' in terms of 'interlistF' itself. It looks like this:

    withSpine =
        \(rec :: ((* -> * -> *) -> *) -> *) ->
            \(a :: *) (b :: *) -> rec (\(interlist :: * -> * -> *) -> interlist a b)

    interlistF' =
        \(rec :: ((* -> * -> *) -> *) -> *) (spine :: (* -> * -> *) -> *) ->
            spine (\(a :: *) (b :: *) -> interlistF (withSpine rec) a b)

Here 'spine' encapsulates 'a' and 'b' as arguments passed to a function 'spine' receives.
This even can be guessed from its signature:

    spine :: (* -> * -> *) -> *

which can be read as "give me a function of two arguments and I'll provide those arguments and
return the result".

'withSpine' on the other hand receives

1. a function that expects a CPS-transformed spine
2. two arguments, 'a' and 'b', which together form a spine that is not CPS-trasformed

and then 'withSpine' applies said function to the spine by CPSing it first.

So nothing interesting happens here: we just pack/unpack spines using continuations.

If we eta-contract @interlistF'@, we'll get

    interlistF' =
        \(rec :: ((* -> * -> *) -> *) -> *) (spine :: (* -> * -> *) -> *) ->
            spine (interlistF (withSpine rec))

And this can be generalized to arbitrary n-ary pattern functors:

    pat1 =
        \(withSpine :: ((k -> *) -> *) -> k) (patN :: k -> k) ->
            \(rec :: (k -> *) -> *) (spine :: k -> *) ->
                spine (pat (withSpine rec))

which reads like this: having 'withSpine' constructed for a particular 'k' and an n-ary pattern
functor of kind @k -> k@ we can get a 1-ary pattern functor of kind

    ((k -> *) -> *) -> (k -> *) -> *

We derive various 'withSpine's automatically on the Haskell side from 'k' itself.

Read next: Note [Denormalization].
-}

{- Note [Denormalization]
Originally, we were binding 'withSpine' and 'patN' (taken from the end of
Note [Packing n-ary functors]) on the Plutus Core side and this resulted in huge unreadable types
being produced. Now we bind 'withSpine', 'patN' and what 'withSpine' receives on the Haskell side,
i.e. we use Haskell lambdas to bind variables and regular function application to eliminate those
lambdas which allows us to defer type reduction business to Haskell.
Here is how the definition of 'list' looks like:

    \(a :: *) -> ifix
        (\(rec :: ((* -> *) -> *) -> *) -> \(spine :: (* -> *) -> *) ->
            spine
                ( (\(list :: * -> *) -> \(a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r)
                  (\(a :: *) -> rec (\(dat :: * -> *) -> dat a))
                )
        )
        (\(dat :: * -> *) -> dat a)

This is pretty readable (once you know how to read it) and doesn't contain any 'withSpine' or 'patN'
variables, but looking closely at:

    (\(list :: * -> *) -> \(a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r)
    (\(a :: *) -> rec (\(dat :: * -> *) -> dat a))

we see an applied lambda abstraction that essentially says that in the pattern functor of 'list'

    \(a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r

'list' is defined as

    \(a :: *) -> rec (\(dat :: * -> *) -> dat a)

This all is fine, that's how our encoding trick works, but note that we produced a type that is not
in normal form. This is a bit worrying: the user writes something that looks like it's normalized,
but in the end types are not normalized due to how the encoding works.

If we normalize the definition of 'list', we'll get

    \(a :: *) -> ifix
        (\(rec :: ((* -> *) -> *) -> *) -> \(spine :: (* -> *) -> *) ->
            spine (\(a :: *) -> all (r :: *). r -> (a -> rec (\(dat :: * -> *) -> dat a) -> r) -> r))
        (\(dat :: * -> *) -> dat a)

But we can't just normalize everything, because the user might write a non-normalized type and it's
desirable to preserve redexes in the type.

Then the question is whether it's possible to preserve redexes in user-written types and not to
produce new ones while encoding the types. And the answer is "yes".

But read Note [Spines] first.
-}

{- Note [Spines]
Encoding of n-ary pattern functors into 1-ary pattern functors is hidden behind an API that pretends
our types are in head-spine form. See @plutus/docs/fomega/deep-isorecursive/alternatives.md@ for
details and discussion about the head-spine form approach.

The reasons for providing such API are

1. it's simple
2. it hides all the gory details in such a way that we can change the representation of types and
not change the API. For example, we can encode pattern functors in different ways (and we, in fact,
do this) or we even can have the head-spine form in the AST and that wouldn't affect the API

We could have an API like this: the user provides an n-ary pattern functor and we manipulate the AST
directly which may or may not involve deconstruction of the AST depending on how we perform encoding.
However the user might provide something that is not a pattern functor, but computes to a pattern
functor and everything becomes more complicated. Instead, we require that the user provides the name
of the data type being defined, a list of type variables (the ones that the pattern functor binds)
along with their kinds and the body of the pattern functor separately. Having this information is
enought to perform whatever encoding we want. Here is how it looks on the 'interlist' example:

the n-ary pattern functor of 'interlist' is

    \(interlist :: * -> * -> *) (a :: *) (b :: *) ->
        all (r :: *). r -> (a -> b -> interlist b a -> r) -> r

and we require the user (where "the user" means someone generating Plutus Core or writing it directly,
i.e. either someone writing a compiler to Plutus Core or one of the creators of the language) to split
this type into three components

1. "interlist"         -- the name of the data type
2. @[a :: *, b :: *]@  -- other type variables the pattern functors binds along with their kinds
3. @all (r :: *). r -> (a -> b -> interlist b a -> r) -> r@  -- the body of the pattern functor

and pass them to the 'makeRecursiveType' function (which also receives an annotation as its first
argument just so that we have something to place in the AST when needed). Note that we do not require
to provide the kind of 'interlist', because we can compute it from the kinds of other type variables.

The code constructing the data type itself:

    -- Introduce names in scope.
    [a, b, interlist, r] <- traverse (freshTyName ()) ["a", "b", "interlist", "r"]

    -- Define some aliases.
    let interlistBA = mkIterTyApp () (TyVar () interlist) [TyVar () b, TyVar () a]
        nilElimTy   = TyVar () r
        consElimTy  = mkIterTyFun () [TyVar () a, TyVar () b, interlistBA] $ TyVar () r)

    -- Construct the actual data type.
    makeRecursiveType () interlist [TyVarDecl () a $ Type (), TyVarDecl () b $ Type ()]
        . TyForall () r (Type ())  -- all (r :: *).
        . TyFun () nilElimTy       --     r ->
        . TyFun () consElimTy      --         (a -> b -> interlist b a -> r) ->
        $ TyVar () r               --             r

So for the user the interface this module provides is rather simple considering how much stuff is
hidden behind it.

Read next: Note [Packing n-ary pattern functors syntactically]
-}

{- Note [Packing n-ary pattern functors syntactically]
-}

-- | A recursive type packaged along with a specified 'Wrap' that allows to construct elements
-- of this type.
data RecursiveType ann = RecursiveType
    { _recursiveType :: Type TyName ann
      -- ^ This is not supposed to have duplicate names.
      -- TODO: check this.
    , _recursiveWrap :: [Type TyName ann] -> Term TyName Name ann -> Term TyName Name ann
      -- ^ This produces terms with duplicate names.
    }

data IndicesLengthsMismatchError = IndicesLengthsMismatchError
    { _indicesLengthsMismatchErrorExpected :: Int
    , _indicesLengthsMismatchErrorActual   :: Int
    , _indicesLengthsMismatchErrorTyName   :: TyName ()
    } deriving (Typeable)

instance Show IndicesLengthsMismatchError where
    show (IndicesLengthsMismatchError expected actual tyName) = concat
        [ "Wrong number of elements\n"
        , "expected: ", show expected, " , actual: ", show actual, "\n"
        , "while constructing a ", prettyPlcDefString tyName
        ]

instance Exception IndicesLengthsMismatchError

-- |
--
-- > FixN : ∀ {K} -> (((K -> Set) -> Set) -> K) -> (K -> K) -> K
-- > FixN {K} withSpine Pat =
-- >     withSpine (IFix patternFunctor) spine where
-- >         patternFunctor = λ (B : (K -> Set) -> Set) (P : K -> Set) -> P (Pat (withSpine B))
-- > \(withSpine :: ((k -> *) -> *) -> k) (patF :: k -> k) ->
-- >     \(rec :: (k -> *) -> *) (spine :: k -> *) -> spine (patF (withSpine rec))

-- | > argKindsToDataKindN _ [k1, k2 ... kn] = k1 -> k2 -> ... -> kn -> *
argKindsToDataKindN :: ann -> [Kind ann] -> Kind ann
argKindsToDataKindN ann argKinds = mkIterKindArrow ann argKinds $ Type ann

dataKindToSpineKind :: ann -> Kind ann -> Kind ann
dataKindToSpineKind ann dataKind = KindArrow ann dataKind $ Type ann

spineKindToRecKind :: ann -> Kind ann -> Kind ann
spineKindToRecKind ann spineKind = KindArrow ann spineKind $ Type ann

getToSpine :: ann -> Quote ([TyDecl TyName ann] -> Type TyName ann)
getToSpine ann = do
    dat <- freshTyName ann "dat"

    return $ \args ->
          TyLam ann dat (argKindsToDataKindN ann $ map tyDeclKind args)
        . mkIterTyApp ann (TyVar ann dat)
        $ map tyDeclType args

-- |
--
-- > getSpine _ [a1 :: k1, a2 :: k2 ... an :: kn] =
-- >     \(R :: k1 -> k2 -> ... kn -> *) -> R a1 a2 ... an
--
-- For example,
--
-- > getSpine _ [a1 :: k1, a2 :: k2] =
-- >     \(R :: k1 -> k2 -> *) -> R a1 a2
getSpine :: ann -> [TyDecl TyName ann] -> Quote (Type TyName ann)
getSpine ann args = ($ args) <$> getToSpine ann

-- |
--
-- > getWithSpine [v1 :: k1, v2 :: k2 ... vn :: kn] =
-- >     \(K :: (((k1 -> k2 -> ... -> kn -> *) -> *) -> *)
-- >      (v1 :: k1) (v2 :: k2) ... (vn :: kn) ->
-- >          K \(R :: k1 -> k2 -> ... kn -> *) -> R v1 v2 ... vn
--
-- For example,
--
-- > getWithSpine [a1 :: k1, a2 :: k2] =
-- >     \(K : ((k1 -> k2 -> *) -> *) -> *) (a1 :: k1) (a2 :: k2) ->
-- >          K \(R :: k1 -> k2 -> *) -> R a1 a2
getWithSpine
    :: ann
    -> [TyVarDecl TyName ann]
    -> Quote ((Type TyName ann -> Type TyName ann) -> Type TyName ann)
getWithSpine ann argVars = do
    spine <- getSpine ann $ map tyDeclVar argVars
    return $ \k -> mkIterTyLam ann argVars $ k spine

-- See Note [Spines].
type WithData ann a
    =  ann                     -- ^ An annotation placed everywhere we do not have annotations.
    -> TyName ann              -- ^ The name of the data type being defined.
    -> [TyVarDecl TyName ann]  -- ^ A list of @n@ type variables bound in a pattern functor.
    -> Type TyName ann         -- ^ The body of the n-ary pattern functor.
    -> Quote a

semPackPatternBodyN :: WithData ann (Type TyName ann)
semPackPatternBodyN ann0 dataName argVars patBodyN = do
    withSpine <- getWithSpine ann0 argVars

    rec   <- freshTyName ann0 "rec"
    spine <- freshTyName ann0 "spine"

    let dataKind  = argKindsToDataKindN ann0 $ map tyVarDeclKind argVars
        spineKind = dataKindToSpineKind ann0 dataKind
        recKind   = spineKindToRecKind  ann0 spineKind
        vR   = TyVarDecl ann0 dataName dataKind
        pat1 = mkIterTyLam ann0 (vR : argVars) patBodyN

    return
        . TyLam ann0 rec recKind
        . TyLam ann0 spine spineKind
        . TyApp ann0 (TyVar ann0 spine)
        . TyApp ann0 pat1
        . withSpine
        . TyApp ann0
        $ TyVar ann0 rec

synPackPatternBodyN :: WithData ann (Type TyName ann)
synPackPatternBodyN ann0 dataName argVars patBodyN = do
    rec   <- freshTyName ann0 "rec"
    spine <- freshTyName ann0 "spine"

    let dataKind  = argKindsToDataKindN ann0 $ map tyVarDeclKind argVars
        spineKind = dataKindToSpineKind ann0 dataKind
        recKind   = spineKindToRecKind  ann0 spineKind

        pack = go argVars return

        go vars elimCon var@(TyVar ann name)        = if name == dataName
            then do
                nameFr <- freshenTyName name
                fun    <- elimCon $ TyVar ann nameFr
                return
                    . mkIterTyLam ann vars
                    . TyApp ann (TyVar ann rec)
                    . TyLam ann nameFr dataKind
                    . mkIterTyApp ann fun
                    $ map (mkTyVar ann) vars
            else elimCon var
        go vars elimCon (TyApp ann fun arg)         =
            go (drop 1 vars) (\fun' -> pack arg >>= elimCon . TyApp ann fun') fun
        go _    _       (TyFun ann tyIn tyOut)      = TyFun ann <$> pack tyIn <*> pack tyOut
        go _    _       (TyIFix ann pat arg)        = TyIFix ann <$> pack pat <*> pack arg
        go _    _       (TyForall ann name kind ty) = TyForall ann name kind <$> pack ty
        go _    elimCon bi@TyBuiltin{}              = elimCon bi
        go _    _       size@TyInt{}                = return $ size
        go _    elimCon (TyLam ann name kind ty)    = pack ty >>= elimCon . TyLam ann name kind

    patBody1 <- pack patBodyN
    return
        . TyLam ann0 rec recKind
        . TyLam ann0 spine spineKind
        . TyApp ann0 (TyVar ann0 spine)
        . mkIterTyLam ann0 argVars
        $ patBody1

packPatternBodyN :: WithData ann (Type TyName ann)
packPatternBodyN = const semPackPatternBodyN synPackPatternBodyN

getTyFix :: WithData ann (Type TyName ann)
getTyFix ann name argVars patBodyN = do
    withSpine <- getWithSpine ann argVars
    withSpine . TyIFix ann <$> packPatternBodyN ann name argVars patBodyN

getWrap :: WithData ann ([Type TyName ann] -> Term TyName Name ann -> Term TyName Name ann)
getWrap ann name argVars patBody = do
    pat1 <- packPatternBodyN ann name argVars patBody
    toSpine <- getToSpine ann
    let instVar var ty = TyDecl ann ty $ tyVarDeclKind var
    return $ \args ->
        let argVarsLen = length argVars
            argsLen = length args
            in if argVarsLen == argsLen
                then IWrap ann pat1 . toSpine $ zipWith instVar argVars args
                else throw . IndicesLengthsMismatchError argVarsLen argsLen $ void name

makeRecursiveType
    :: ann
    -> TyName ann
    -> [TyVarDecl TyName ann]
    -> Type TyName ann
    -> Quote (RecursiveType ann)
makeRecursiveType ann name argVars patBody =
    RecursiveType <$> getTyFix ann name argVars patBody <*> getWrap ann name argVars patBody
