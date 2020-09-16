-- | This module defines Haskell data types that simplify construction of PLC types and terms.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types        #-}

module Language.PlutusCore.StdLib.Type
    ( RecursiveType (..)
    , makeRecursiveType
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote

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
@plutus/plutus-core/docs/Holed types.md@.

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

which covers all those cases. However, it's not clear how to implement such @fix@.
See @docs/fomega/deep-isorecursive/README.md@ for details.

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

    toPat1 =
        \(withSpine :: ((k -> *) -> *) -> k) (patN :: k -> k) ->
            \(rec :: (k -> *) -> *) (spine :: k -> *) ->
                spine (pat (withSpine rec))

which reads like this: having 'withSpine' constructed for a particular 'k' and an n-ary pattern
functor of kind @k -> k@ we can get a 1-ary pattern functor of kind

    ((k -> *) -> *) -> (k -> *) -> *

We derive various 'withSpine's automatically on the Haskell side from 'k' itself.

Read next: Note [Generic fix].
-}

{- Note [Generic fix]
Now that we know how to pack n-ary functors into 1-ary ones
(see [Packing n-ary pattern functors semantically]), only a few tiny steps remain to get the generic

    fix :: (k -> k) -> k

from just

    ifix :: ((i -> *) -> i -> *) -> i -> *

Having @pat :: k -> k@ we can pack it as

    toPat1 withSpine patN :: ((k -> *) -> *) -> (k -> *) -> *

(where 'withSpine' is constructed automatically from 'k' on the Haskell side) and we can apply
'ifix' to this 1-ary pattern functor and get

    ifix (toPat1 withSpine patN) :: (k -> *) -> *

It only remains to turn something of kind @(k -> *) -> *@ into something of kind @*@, i.e. to define
a type function of kind @((k -> *) -> *) -> k@. But we already have such a function: 'withSpine',
so the final encoding is

    fix = \(patN :: k -> k) -> withSpine (ifix (toPat1 withSpine patN))

The meaning of 'withSpine' here is the same as we've seen before: we use it to pack @n@ type
arguments as a single CPS-encoded spine and pass it to some function.

Summarizing, 'fix' receives an n-ary pattern functor and @n@ type arguments, the pattern functor
gets packed as a 1-ary one, the type arguments get packed into a single CPS-encoded spine and
'ifix' gets applied to the 1-ary pattern functor and the spine.

Read next: Note [Encoded InterList].
-}

{- Note [Encoded InterList]
Let's now look at an example.

Recall that the pattern functor of 'interlist' is

    interlistF =
        \(interlist :: * -> * -> *) (a :: *) (b :: *) ->
            all (r :: *). r -> (a -> b -> interlist b a -> r) -> r

We can apply generic 'fix' (see Note [Generic fix]) to this pattern functor directly:

    fix interlistF :: * -> *

which after eta-expansion and some reductions becomes

    \(a :: *) -> withSpine (ifix (toPat1 withSpine interlistF)) a

(as per Note [Generic fix]) which after some more reductions becomes

    -- Two type arguments that the data type receives and the 'ifix' primitive.
    \(a :: *) (b -> *) -> ifix
        -- The variable responsible for recursion and the variable representing a CPS-encoded spine
        -- of two elements. Note that the kind of the argument that the variable responsible for
        -- recursion receives is the same as the kind of 'spine', i.e. we always instantiate
        -- recursion at some spine.
        (\(rec :: ((* -> * -> *) -> *) -> *) -> \(spine :: (* -> * -> *) -> *) ->
            -- 'spine' unpacks a CPS-encoded spine and passes all its elements to a continuation.
            spine
              -- The 'interlistF' pattern functor given above applied to a function that receives
              -- two type arguments, packs them as a CPS-encoded spine and passes the spine to the
              -- variable responsible for recursion.
              (interlistF (\(a :: *) (b :: *) -> rec (\(dat :: * -> * -> *) -> dat a b)))
        )
        -- The two type arguments packed as a CPS-encoded spine.
        (\(dat :: * -> * -> *) -> dat a b)

We've elaborated the encoding on example, but there is a problem to consider here.
Read next: Note [Denormalization]
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
            spine (listF (\(a :: *) -> rec (\(dat :: * -> *) -> dat a)))
        )
        (\(dat :: * -> *) -> dat a)

This is pretty readable (once you know how to read it, see Note [Encoded InterList] for a similar
example) and doesn't contain any 'withSpine' or 'patN' variables, but if we inline 'listF', we'll get

    (\(list :: * -> *) -> \(a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r)
    (\(a :: *) -> rec (\(dat :: * -> *) -> dat a))

which is an applied lambda abstraction. This essentially means that in the pattern functor of 'list'

    \(a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r

'list' is defined as

    \(a :: *) -> rec (\(dat :: * -> *) -> dat a)

This all is fine, that's how our encoding trick works, but note that we produced a type that is not
in normal form. This is a bit worrying: the user writes something that looks like it's normalized,
but in the end types are not normalized due to how the encoding works. In Plutus Core we have two
modes for type checking:

1. off-chain, type normalization is allowed
2. on-chain, type normalization is not allowed and types must already be normalized

Thus, we do care about whether types are normalized or not. In the compilation pipeline we just
explicitly normalize types whenever normalized types are required, but since this module belongs
to a library it better be general and not rely on particular details of downstream code.

Preserving properties of user-written code is generally a good idea while transforming it,
so we also do not want to remove redexes from user-written code and thus we can't just normalize
everything in sight to overcome the denormalization problem.

Then the question is whether it's possible to preserve redexes in user-written types and not to
produce new ones while encoding the types. And the answer is "yes, but it's too costly".

But read Note [Spiney API] first.
-}

{- Note [Spiney API]
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
    [a, b, interlist, r] <- traverse freshTyName ["a", "b", "interlist", "r"]

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
Now that we know how the API looks like (see Note [Spiney API]), we can discuss a solution to
the denormalization problem (see Note [Denormalization]).

Recall (or see Note [Packing n-ary pattern functors semantically]) that if we pack the pattern
functor of 'list'

    listF = \(list :: * -> *) (a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r

semantically and normalize the result, we'll get

    semListF =
        \(rec :: ((* -> *) -> *) -> *) -> \(spine :: (* -> *) -> *) ->
            spine (\(a :: *) -> all (r :: *). r -> (a -> rec (\(dat :: * -> *) -> dat a) -> r) -> r)

The question is how to get the same without full-scale normalization.

In this particular case it's easy: since we receive the body of 'listF' separately from the variables
the leading lambdas bind, we can simply enclose the body of 'listF' like this:

    \(rec :: ((* -> *) -> *) -> *) -> \(spine :: (* -> *) -> *) ->
                spine (\(a :: *) -> <body_of_listF>)

and replace each occurrence of @list a@ by

    rec (\(dat :: * -> *) -> dat a)

and that's all.

The slightly tricky part is how exactly we perform the replacement: we need to traverse each sequence
of consecutive function applications in the pattern functor, remember all encountered arguments and
if the head of consecutive applications is 'list' then rename it to 'dat' (and freshen the unique of
the variable, because it's easy and it's nice not to break the global uniqueness condition, but this
is not too important), apply 'dat' to all the remembered arguments and enclose the result by

    rec (\(dat :: * -> *) -> _)

But that doesn't work in the general case. The user might write

    app = \(f :: * -> *) (a :: *) -> f a
    listF = \(list :: * -> *) (a :: *) -> all (r :: *). r -> (a -> app list a -> r) -> r

i.e. a type containing a non-saturated 'list' and the outlined algorithm can't handle this case,
because it always just restores all the arguments in a sequence of applications (which we have none
in this example) while we need to generate the following:

    semAppListF =
        \(rec :: ((* -> *) -> *) -> *) -> \(spine :: (* -> *) -> *) ->
            let list = \(a :: *) -> rec (\(dat :: * -> *) -> dat a)
                in spine (\(a :: *) -> all (r :: *). r -> (a -> app list a -> r) -> r)

(where @let list = ... in ...@ is pseudosyntax introduced for readability)
So if a recursive case is not saturated, we have to generate as many lambdas as there are missing
arguments and prepend the lambdas to the encoding of the recursive case.

This way we can preserve the user's redexes and not introduce additional ones.

Read next: Note [Comparing approaches to pattern functor packing]
-}

{- Note [Comparing approaches to pattern functor packing]
Packing n-ary pattern functors semantically (see Note [Packing n-ary pattern functors semantically]):
Pros:
    1. easy to get right. Kinds match? You're all set
    2. does not require manual manipulations with syntax (which would be very error-prone)
    3. does not evaluate redexes written by the user
    4. pattern functors with more than one recursive case are smaller being encoded this way than
       when everything is fully inlined (in the latter case the overhead is O(n) where 'n' is the
       number of recursive occurrences in a pattern functor)
Cons:
    1. resulting types contain additional redexes. I.e. we can turn normalized types into
       non-normalized ones
    2. pattern functors with one recursive case are slightly bigger being encoded this way than
       when everything is fully inlined

Packing n-ary pattern functors syntactically (see Note [Packing n-ary pattern functors syntactically]):
Pros:
    1. neither introduces new redexes nor evaluates ones written by the user
Cons:
    1. super easy to get wrong. While implementing this approach, I got it wrong three times.
       I'm still not sure it's sound
    2. requires testing against the other way to encode n-ary pattern functors
    3. requires manipulations with uniques which always look fine until you get an incomprehensible
       error message after 82 generated test cases pass
    4. pattern functors with more than one recursive case are bigger being encoded this way than
       with the other approach (the overhead here is O(n) where 'n' is the number of recursive
       occurrences in a pattern functor)
    5. someone who generates Plutus Core does not care much about whether types are normalized,
       because it's a pain and if you want normalized types, just normalize what you generated
       in the end.

Therefore, the costs of encoding n-ary pattern functors as 1-ary pattern functors in normal form
are rather high while the benefits are minor, and thus we go with the semantic packing approach.
-}

-- | A recursive type packaged along with a specified 'Wrap' that allows to construct elements
-- of this type.
data RecursiveType uni fun ann = RecursiveType
    { _recursiveType :: Type TyName uni ann
    , _recursiveWrap :: forall term . TermLike term TyName Name uni fun
                     => [Type TyName uni ann] -> term ann -> term ann
    }

-- | This exception is thrown when @_recursiveWrap@ is applied to a spine the length of which
-- is not equal to the length of the spine that @_recursiveType@ contains.
-- This can only happen if someone writing/generating Plutus Core made a mistake.
data IndicesLengthsMismatchException = IndicesLengthsMismatchException
    { _indicesLengthsMismatchExceptionExpected :: Int
    , _indicesLengthsMismatchExceptionActual   :: Int
    , _indicesLengthsMismatchExceptionTyName   :: TyName
    } deriving (Typeable)

instance Show IndicesLengthsMismatchException where
    show (IndicesLengthsMismatchException expected actual tyName) = concat
        [ "Wrong number of elements\n"
        , "expected: ", show expected, " , actual: ", show actual, "\n"
        , "while constructing a ", displayPlcDef tyName
        ]

instance Exception IndicesLengthsMismatchException

-- | Get the kind of a data type having the kinds of its arguments.
--
-- > argKindsToDataKindN _ [k1, k2 ... kn] = k1 -> k2 -> ... -> kn -> *
argKindsToDataKindN :: ann -> [Kind ann] -> Kind ann
argKindsToDataKindN ann argKinds = mkIterKindArrow ann argKinds $ Type ann

-- | Get the kind of @spine@ having the kind of a data type.
--
-- > dataKindToSpineKind _ dataKind = dataKind -> *
dataKindToSpineKind :: ann -> Kind ann -> Kind ann
dataKindToSpineKind ann dataKind = KindArrow ann dataKind $ Type ann

-- | Get the kind of @rec@ having the kind of @spine@.
--
-- > spineKindToRecKind _ spineKind = spineKind -> *
spineKindToRecKind :: ann -> Kind ann -> Kind ann
spineKindToRecKind ann spineKind = KindArrow ann spineKind $ Type ann

-- | Make a function that packs a list of 'TyDecl's as a spine using the CPS trick.
--
-- > getToSpine _ =
-- >     \[a1 :: k1, a2 :: k2 ... an :: kn] -> (dat :: k1 -> k2 -> ... kn -> *) -> dat a1 a2 ... an
--
-- For example,
--
-- > getToSpine _ =
-- >     \[a1 :: k1, a2 :: k2] -> (dat :: k1 -> k2 -> *) -> dat a1 a2
getToSpine :: ann -> Quote ([TyDecl TyName uni ann] -> Type TyName uni ann)
getToSpine ann = do
    dat <- freshTyName "dat"

    return $ \args ->
          TyLam ann dat (argKindsToDataKindN ann $ map tyDeclKind args)
        . mkIterTyApp ann (TyVar ann dat)
        $ map tyDeclType args

-- | Pack a list of 'TyDecl's as a spine using the CPS trick.
--
-- > getSpine _ [a1 :: k1, a2 :: k2 ... an :: kn] =
-- >     \(dat :: k1 -> k2 -> ... kn -> *) -> dat a1 a2 ... an
--
-- For example,
--
-- > getSpine _ [a1 :: k1, a2 :: k2] =
-- >     \(dat :: k1 -> k2 -> *) -> dat a1 a2
getSpine :: ann -> [TyDecl TyName uni ann] -> Quote (Type TyName uni ann)
getSpine ann args = ($ args) <$> getToSpine ann

-- See Note [Packing n-ary pattern functors semantically].
-- | Having a list of type variables along with their kinds, make a function that receives
--
-- 1. a function expecting a spine in CPS form
-- 2. a sequence of types
--
-- packs the types into a CPS-encoded spine and passes the spine to the function.
--
-- > getWithSpine _ [v1 :: k1, v2 :: k2 ... vn :: kn] =
-- >     \(cont :: ((k1 -> k2 -> ... -> kn -> *) -> *) -> *)
-- >      (v1 :: k1) (v2 :: k2) ... (vn :: kn) ->
-- >          cont \(dat :: k1 -> k2 -> ... kn -> *) -> dat v1 v2 ... vn
--
-- For example,
--
-- > getWithSpine _ [v1 :: k1, v2 :: k2] =
-- >     \(cont : ((k1 -> k2 -> *) -> *) -> *) (v1 :: k1) (v2 :: k2) ->
-- >          cont \(dat :: k1 -> k2 -> *) -> dat v1 v2
getWithSpine
    :: ann
    -> [TyVarDecl TyName ann]
    -> Quote ((Type TyName uni ann -> Type TyName uni ann) -> Type TyName uni ann)
getWithSpine ann argVars = do
    spine <- getSpine ann $ map tyDeclVar argVars
    return $ \k -> mkIterTyLam argVars $ k spine

-- See Note [Spiney API].
type FromDataPieces uni ann a
    =  ann                     -- ^ An annotation placed everywhere we do not have annotations.
    -> TyName                  -- ^ The name of the data type being defined.
    -> [TyVarDecl TyName ann]  -- ^ A list of @n@ type variables bound in a pattern functor.
    -> Type TyName uni ann     -- ^ The body of the n-ary pattern functor.
    -> Quote a

-- See Note [Packing n-ary pattern functors semantically].
-- | Pack the body of an n-ary pattern functor and make the corresponding 1-ary pattern functor.
--
-- > packPatternFunctorBodyN _ dataName [v1 :: k1, v2 :: k2 ... vn :: kn] patBodyN =
-- >     let patN = \(dataName :: k1 -> k2 -> ... -> kn -> *) (v1 :: k1) (v2 :: k2) ... (vn :: kn) ->
-- >                     patBodyN
-- >         in \(rec :: ((k1 -> k2 -> ... kn -> *) -> *) -> *)
-- >             (spine :: (k1 -> k2 -> ... -> kn -> *) -> *) ->
-- >                 spine (patN (withSpine rec))
--
-- For example,
--
-- > packPatternFunctorBodyN _ dataName [v1 :: k1, v2 :: k2] patBodyN =
-- >     let patN = \(dataName :: k1 -> k2 -> *) (v1 :: k1) (v2 :: k2) ->
-- >                     patBodyN
-- >         in \(rec :: ((k1 -> k2 -> *) -> *) -> *)
-- >             (spine :: (k1 -> k2 -> *) -> *) ->
-- >                 spine (patN (withSpine rec))
packPatternFunctorBodyN :: FromDataPieces uni ann (Type TyName uni ann)
packPatternFunctorBodyN ann dataName argVars patBodyN = do
    let dataKind  = argKindsToDataKindN ann $ map tyVarDeclKind argVars
        spineKind = dataKindToSpineKind ann dataKind
        recKind   = spineKindToRecKind  ann spineKind
        vDat = TyVarDecl ann dataName dataKind
        patN = mkIterTyLam (vDat : argVars) patBodyN

    withSpine <- getWithSpine ann argVars

    rec   <- freshTyName "rec"
    spine <- freshTyName "spine"

    return
        . TyLam ann rec recKind
        . TyLam ann spine spineKind
        . TyApp ann (TyVar ann spine)
        . TyApp ann patN
        . withSpine
        . TyApp ann
        $ TyVar ann rec

-- | Construct a data type out of pieces.
getPackedType :: FromDataPieces uni ann (Type TyName uni ann)
getPackedType ann dataName argVars patBodyN = do
    withSpine <- getWithSpine ann argVars
    withSpine . TyIFix ann <$> packPatternFunctorBodyN ann dataName argVars patBodyN

-- | An auxiliary type for returning a polymorphic @wrap@. Haskell's support for impredicative
-- polymorphism isn't good enough to do without this.
newtype PolyWrap uni fun ann = PolyWrap
    (forall term. TermLike term TyName Name uni fun => [Type TyName uni ann] -> term ann -> term ann)

-- | Make a generic @wrap@ that takes a spine of type arguments and the rest of a term, packs
-- the spine using the CPS trick and passes the spine and the term to 'IWrap' along with a 1-ary
-- pattern functor constructed from pieces of a data type passed as arguments to 'getWrap'.
getPackedWrap :: FromDataPieces uni ann (PolyWrap uni fun ann)
getPackedWrap ann dataName argVars patBodyN = do
    pat1 <- packPatternFunctorBodyN ann dataName argVars patBodyN
    toSpine <- getToSpine ann
    let instVar v ty = TyDecl ann ty $ tyVarDeclKind v
    return $ PolyWrap $ \args ->
        let argVarsLen = length argVars
            argsLen = length args
            in if argVarsLen == argsLen
                then iWrap ann pat1 . toSpine $ zipWith instVar argVars args
                else throw . IndicesLengthsMismatchException argVarsLen argsLen $ dataName

{- Note [Special cases]
The notes above describe how the general case is compiled, however for the 0-ary and 1-ary cases
there are more efficient compilation schemes.

Compiled generally, @fix0 (pat :: * -> *)@ looks like this:

    ifix
        (\(rec :: (* -> *) -> *) (spine :: * -> *) -> spine (pat (rec (\(dat :: *) -> dat))))
        (\(dat :: *) -> dat)

A more efficient compilation scheme is

    ifix
        (\(rec :: (* -> *) -> *) (f :: * -> *) -> f (rec f))
        pat

This is the one that we use in 'makeRecursiveType0'. Note however that 'makeRecursiveType*'
functions always receive the body of a pattern functor and not the pattern functor itself,
so in the 0-ary case we turn the body of the pattern functor into the pattern functor by
prepending a lambda binding a variable with the same name as that of the data type being
defined. Note also that the pattern functor of the resulting 'ifix' is always the same --
it's the index that differs.

Compiled generally, @fix1 (pat :: (k -> *) -> k -> *) (arg :: *)@ looks like this:

    \(v :: k) ->
        ifix
            (\(rec :: (* -> *) -> *) (spine :: * -> *) ->
                spine (pat (\(x :: v) -> rec (\(dat :: k -> *) -> dat v))))
            (\(dat :: k -> *) -> dat v)

But we clearly don't need to represent a single type argument as a CPS-encoded spine,
because the only point of representing things like that is to get a single type argument out of
@n@ type arguments and when @n = 1@ no such tricks are needed.

So the encoding that we use is

    \(v :: k) -> ifix pat v

And as in the 0-ary case we need to turn the body of a pattern functor into a pattern functor,
this time not only by prepending a lambda binding a variable with the same name as that of
the data type being defined, but also by prepending a lambda binding a variable representing the
index.
-}

-- See Note [Special cases].
-- | Construct a 'RecursiveType' by passing a 0-ary pattern functor to 'TyIFix' and 'IWrap'
-- /as an index/.
makeRecursiveType0
    :: ann                  -- ^ An annotation placed everywhere we do not have annotations.
    -> TyName               -- ^ The name of the data type being defined.
    -> Type TyName uni ann  -- ^ The body of the pattern functor.
    -> Quote (RecursiveType uni fun ann)
makeRecursiveType0 ann dataName patBody0 = do
    rec <- freshTyName "rec"
    f   <- freshTyName "f"
    let argKind = KindArrow ann (Type ann) $ Type ann
        recKind = KindArrow ann argKind $ Type ann
        pat1
            = TyLam ann rec recKind
            . TyLam ann f   argKind
            . TyApp ann (TyVar ann f)
            . TyApp ann (TyVar ann rec)
            $ TyVar ann f
        arg = TyLam ann dataName (Type ann) patBody0
        -- recType =
        --     ifix
        --         (\(rec :: (* -> *) -> *) (f :: * -> *) -> f (rec f))
        --         (\(dataName :: *) -> patBody0)
        recType = TyIFix ann pat1 arg
        wrap args = case args of
            [] -> iWrap ann pat1 arg
            _  -> throw . IndicesLengthsMismatchException 0 (length args) $ dataName
    return $ RecursiveType recType wrap

-- See Note [Special cases].
-- | Construct a 'RecursiveType' by passing a 1-ary pattern functor to 'TyIFix' and 'IWrap'.
makeRecursiveType1
    :: ann                   -- ^ An annotation placed everywhere we do not have annotations.
    -> TyName                -- ^ The name of the data type being defined.
    -> TyVarDecl TyName ann  -- ^ The index type variable.
    -> Type TyName uni ann   -- ^ The body of the pattern functor.
    -> Quote (RecursiveType uni fun ann)
makeRecursiveType1 ann dataName argVar patBody1 = do
    let varName = tyVarDeclName argVar
        varKind = tyVarDeclKind argVar
        recKind = KindArrow ann varKind $ Type ann
        pat1 = TyLam ann dataName recKind $ TyLam ann varName varKind patBody1
        -- recType = \(v :: k) -> ifix (\(dataName :: k -> *) (v :: k) -> patBody1) v
        recType = TyLam ann varName varKind . TyIFix ann pat1 $ TyVar ann varName
        wrap args = case args of
            [arg] -> iWrap ann pat1 arg
            _     -> throw . IndicesLengthsMismatchException 1 (length args) $ dataName
    return $ RecursiveType recType wrap

-- See all the Notes above.
-- | Construct a 'RecursiveType' by encoding an n-ary pattern functor as the corresponding 1-ary one
-- and passing it to 'TyIFix' and 'IWrap'. @n@ type arguments get packaged together as a CPS-encoded
-- spine.
makeRecursiveTypeN :: FromDataPieces uni ann (RecursiveType uni fun ann)
makeRecursiveTypeN ann dataName argVars patBodyN = do
    recType <- getPackedType ann dataName argVars patBodyN
    PolyWrap wrap <- getPackedWrap ann dataName argVars patBodyN
    return $ RecursiveType recType wrap

-- | Construct a 'RecursiveType' out of its name, variables bound in its pattern functor
-- and the body of the pattern functor. The 0- and 1-ary pattern functors are special-cased,
-- while in the general case the pattern functor and type arguments get encoded into a 1-ary
-- form first.
makeRecursiveType :: FromDataPieces uni ann (RecursiveType uni fun ann)
makeRecursiveType ann dataName []       = makeRecursiveType0 ann dataName
makeRecursiveType ann dataName [argVar] = makeRecursiveType1 ann dataName argVar
makeRecursiveType ann dataName argVars  = makeRecursiveTypeN ann dataName argVars
