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

-- | A 'Type' that starts with a 'TyIFix' (i.e. a recursive type) packaged along with a
-- specified 'Wrap' that allows to construct elements of this type.
data RecursiveType ann = RecursiveType
    { _recursiveType :: Type TyName ann
      -- ^ This is not supposed to have duplicate names.
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

-- | A type-level function that receives @withSpine@ and a pattern functor that binds
-- @n + 1@ type variables (where @1@ represents the variable responsible for recursion)
-- using type-level lambdas.
type Spiney ann
    =  ann
    -> Kind ann
    -> ((Type TyName ann -> Type TyName ann) -> Type TyName ann)
    -> Type TyName ann
    -> Quote (Type TyName ann)

-- \(rec :: i -> k -> *) (a :: i) (b :: j) ->

-- |
--
-- > \(withSpine :: ((k -> *) -> *) -> k) (pat :: k -> k) ->
-- >     \(b :: (k -> *) -> *) (p :: k -> *) -> p (pat (withSpine b))
getPatternFunctor :: Spiney ann
getPatternFunctor ann k withSpine pat = do
    b <- freshTyName ann "b"
    p <- freshTyName ann "p"
    let star  = Type ann
        (~~>) = KindArrow ann

    return
        . TyLam ann b ((k ~~> star) ~~> star)
        . TyLam ann p (k ~~> star)
        . TyApp ann (TyVar ann p)
        . TyApp ann pat
        . withSpine
        . TyApp ann
        $ TyVar ann b

-- |
--
-- > FixN : ∀ {K} -> (((K -> Set) -> Set) -> K) -> (K -> K) -> K
-- > FixN {K} withSpine Pat =
-- >     withSpine λ (spine : K -> Set) -> IFix patternFunctor spine where
-- >         patternFunctor = λ (B : (K -> Set) -> Set) (P : K -> Set) -> P (Pat (withSpine B))
getTyFixN :: Spiney ann
getTyFixN ann k withSpine pat = do
    patF  <- getPatternFunctor ann k withSpine pat
--     spine <- freshTyName ann "spine"
--     let star  = Type ann
--         (~~>) = KindArrow ann

    return . withSpine $ TyIFix ann patF

-- > Fix₀ : (Set -> Set) -> Set
-- > Fix₀ = FixN withSpine0 where
-- >     withSpine0 =
-- >         λ (K : (Set -> Set) -> Set) ->
-- >             K λ (R : Set) -> R

-- | > toRecKind _ [k1, k2 ... kn] = k1 -> k2 -> ... -> kn -> *
toRecKind :: ann -> [Kind ann] -> Kind ann
toRecKind ann kindArgs = mkIterKindArrow ann kindArgs $ Type ann

getToSpine :: ann -> Quote ([TyDecl TyName ann] -> Type TyName ann)
getToSpine ann = do
    r <- freshTyName ann "r"

    return $ \args ->
          TyLam ann r (toRecKind ann $ map tyDeclKind args)
        . mkIterTyApp ann (TyVar ann r)
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
    -- let argKinds = map tyVarDeclKind argVars
    -- TyLam ann k (KindArrow ann (KindArrow ann (toRecKind ann argKinds) $ Type ann) $ Type ann)

    return $ \k -> mkIterTyLam ann argVars $ k spine

{- Note [InterList]


    data InterList a b
        = InterNil
        | InterCons a b (InterList b a)

    example_InterList :: InterList Char Int
    example_InterList = InterCons 'a' 1 . InterCons 2 'b' . InterCons 'c' 3 $ InterNil


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
Read next: Note [Generic fix].
-}

{- Note [Generic fix]
In Note [Natural representation] we concluded that @fix :: (* -> *) -> *@ is not enough to encode
@list@ in a satisfying way. In that particular case it would be enough to have

    fix :: ((* -> *) -> * -> *) -> * -> *

but what about other cases? The example from Note [InterList] then requires

    fix :: ((* -> * -> *) -> * -> * -> *) -> * -> * -> *

and of course we still need

    fix :: (* -> *) -> *

occasionally. This suggests to change the kind signature of @fix@ to

    fix :: (k -> k) -> k

which covers all those cases. However,

1. It also can be instantiated as @fix :: (size -> size) -> size@ which doesn't make sense.
2. It's not cleat how to implement such @fix@. See <...> for details.
-}


{- Note [Spines]
@ifix@ has the following kind signature:

    ifix :: ((k -> *) -> k -> *) -> k -> *

I.e. @ifix@ receives two arguments: a pattern functor of kind @(k -> *) -> k -> *@ and an index
of kind @k@ and constructs a data type living in @*@.

We can define the @list@ data type as follows using @ifix@:

    listF = \(list :: * -> *) (a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r
    list  = \(a :: *) -> ifix listF a

-- pat  =
--



Consider


-- > fix \(interlist :: * -> * -> *) (a :: *) (b :: *) ->
-- >     all (r :: *). r -> (a -> b -> interlist b a -> r) -> r

    [a, b, interlist, r] <- traverse (freshTyName ()) ["a", "b", "interlist", "r"]
    let interlistBA = mkIterTyApp () (TyVar () interlist) [TyVar () b, TyVar () a]
        nilElimTy   = TyVar () r
        consElimTy  = mkIterTyFun () [TyVar () a, TyVar () b, interlistBA] $ TyVar () r)
    makeRecursiveType () interlist [TyVarDecl () a $ Type (), TyVarDecl () b $ Type ()]
        . TyForall () r (Type ())  -- all (r :: *).
        . TyFun () nilElimTy       --     r ->
        . TyFun () consElimTy      --         (a -> b -> interlist b a -> r) ->
        $ TyVar () r               --             r
-}

{- Note [Denormalization]
The encoding trick we use in this module turns normalized things into non-normalized ones.
Originally, we were binding all variables on the Plutus Core side and this resulted in huge
unreadable types being produced. For example, the @nil@ constructor had the following definition
(the semantics of this is not important here, just the number of symbols):

    /\(a :: *) -> wrap ((\(withSpine :: ((* -> *) -> *) -> *) -> \(pat :: * -> *) -> \(rec :: (* -> *) -> *) -> \(p :: * -> *) -> p (pat (withSpine rec))) (\(k :: (* -> *) -> *) -> k (\(r :: *) -> r)) (\(list :: *) -> (\(a :: *) -> all (r :: *). r -> (a -> list -> r) -> r) a)) (\(r :: *) -> r) (/\(r :: *) -> \(z : r) -> \(f : a -> (\(a :: *) -> (\(withSpine :: ((* -> *) -> *) -> *) -> \(pat :: * -> *) -> withSpine (\(spine :: * -> *) -> ifix ((\(withSpine :: ((* -> *) -> *) -> *) -> \(pat :: * -> *) -> \(rec :: (* -> *) -> *) -> \(p :: * -> *) -> p (pat (withSpine rec))) withSpine pat) spine)) (\(k :: (* -> *) -> *) -> k (\(r :: *) -> r)) (\(list :: *) -> all (r :: *). r -> (a -> list -> r) -> r)) a -> r) -> z)

Now we bind some variables on the Haskell side meaning Haskell performs type reductions for us.
The @nil@ constructor is now (the semantics is still not important):

    /\(a :: *) -> wrap (\(rec :: ((* -> *) -> *) -> *) -> \(p :: (* -> *) -> *) -> p ((\(list :: * -> *) -> \(a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r) (\(a :: *) -> rec (\(r :: * -> *) -> r a)))) (\(r :: * -> *) -> r a) (/\(r :: *) -> \(z : r) -> \(f : a -> (\(a :: *) -> ifix (\(rec :: ((* -> *) -> *) -> *) -> \(p :: (* -> *) -> *) -> p ((\(list :: * -> *) -> \(a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r) (\(a :: *) -> rec (\(r :: * -> *) -> r a)))) (\(r :: * -> *) -> r a)) a -> r) -> z)

This is much better, but types are still not normalized.

-- pat  = \(list :: * -> *)              (a :: *) ->
--                       all (r :: *). r -> (a -> list a            -> r) -> r

-- pat1 = \(rec :: ((* -> *) -> *) -> *) (spine :: (* -> *) -> *) ->
--   spine (\(a :: *) -> all (r :: *). r -> (a -> rec (\on -> on a) -> r) -> r)


-}

packagePatternBodyN
    :: Spiney ann
    -> ann                     -- ^ An annotation placed everywhere we do not have annotations.
    -> TyName ann              -- ^ The name for the @1@ varible responsible for recursion.
    -> [TyVarDecl TyName ann]  -- ^ A list of @n@ type variables.
    -> Type TyName ann         -- ^ The body of a pattern functor
                               -- to which the @n + 1@ type variables will be added via 'TyLam's.
    -> Quote (Type TyName ann)
packagePatternBodyN getFun ann name argVars patBody = do
    withSpine <- getWithSpine ann argVars
    let argKinds = map tyVarDeclKind argVars
        vR  = TyVarDecl ann name $ toRecKind ann argKinds
        pat = mkIterTyLam ann (vR : argVars) patBody
    getFun ann (toRecKind ann argKinds) withSpine pat

getTyFix :: ann -> TyName ann -> [TyVarDecl TyName ann] -> Type TyName ann -> Quote (Type TyName ann)
getTyFix = packagePatternBodyN getTyFixN

getWrap
    :: ann
    -> TyName ann
    -> [TyVarDecl TyName ann]
    -> Type TyName ann
    -> Quote ([Type TyName ann] -> Term TyName Name ann -> Term TyName Name ann)
getWrap ann name argVars patBody = do
    pat1 <- packagePatternBodyN getPatternFunctor ann name argVars patBody
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

    -- makeRecursiveType () treeForest
    --     [TyVarDecl () a star, TyVarDecl () tag $ star ~~> star ~~> star]
    --     body







-- Pat (WithSpine ...)

-- "\(a :: *) -> ifix (\(rec :: ((* -> *) -> *) -> *) -> \(p :: (* -> *) -> *) -> p ((\(list :: * -> *) -> \(a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r) (\(a :: *) -> rec (\(r :: * -> *) -> r a)))) (\(r :: * -> *) -> r a)"





-- "(\(k :: ((* -> * -> *) -> *) -> *) -> \(a :: *) -> \(b :: *) -> k (\(r :: * -> * -> *) -> r a b)) (\(spine :: (* -> * -> *) -> *) -> ifix (\(rec :: ((* -> * -> *) -> *) -> *) -> \(p :: (* -> * -> *) -> *) -> p ((\(interlist :: * -> * -> *) -> \(a :: *) -> \(b :: *) -> all (r :: *). r -> (a -> b -> interlist b a -> r) -> r) ((\(k :: ((* -> * -> *) -> *) -> *) -> \(a :: *) -> \(b :: *) -> k (\(r :: * -> * -> *) -> r a b)) rec))) spine)"

-- "\(a :: *) -> \(b :: *) -> (\(spine :: (* -> * -> *) -> *) -> ifix (\(b :: ((* -> * -> *) -> *) -> *) -> \(p :: (* -> * -> *) -> *) -> p ((\(interlist :: * -> * -> *) -> \(a :: *) -> \(b :: *) -> all (r :: *). r -> (a -> b -> interlist b a -> r) -> r) (\(a :: *) -> \(b :: *) -> b (\(r :: * -> * -> *) -> r a b)))) spine) (\(r :: * -> * -> *) -> r a b)"

-- "\(a :: *) -> \(b :: *) -> ifix (\(rec :: ((* -> * -> *) -> *) -> *) -> \(p :: (* -> * -> *) -> *) -> p ((\(interlist :: * -> * -> *) -> \(a :: *) -> \(b :: *) -> all (r :: *). r -> (a -> b -> interlist b a -> r) -> r) (\(a :: *) -> \(b :: *) -> rec (\(r :: * -> * -> *) -> r a b)))) (\(r :: * -> * -> *) -> r a b)"

-- "\(a :: *) -> \(b :: *) -> ifix (\(rec :: ((* -> * -> *) -> *) -> *) -> \(p :: (* -> * -> *) -> *) -> p (\(a :: *) -> \(b :: *) -> all (r :: *). r -> (a -> b -> rec (\(r :: * -> * -> *) -> r b a)) -> r) -> r) (\(r :: * -> * -> *) -> r a b)"



-- "/\\(a :: *) -> /\\(b :: *) -> wrap (\\(b :: ((* -> * -> *) -> *) -> *) -> \\(p :: (* -> * -> *) -> *) -> p ((\\(interlist :: * -> * -> *) -> \\(a :: *) -> \\(b :: *) -> all (r :: *). r -> (a -> b -> interlist b a -> r) -> r) (\\(a :: *) -> \\(b :: *) -> b (\\(r :: * -> * -> *) -> r a b)))) (\\(r :: * -> * -> *) -> r a b) (/\\(r :: *) -> \\(z : r) -> \\(f : a -> b -> (\\(a :: *) -> \\(b :: *) -> (\\(spine :: (* -> * -> *) -> *) -> ifix (\\(b :: ((* -> * -> *) -> *) -> *) -> \\(p :: (* -> * -> *) -> *) -> p ((\\(interlist :: * -> * -> *) -> \\(a :: *) -> \\(b :: *) -> all (r :: *). r -> (a -> b -> interlist b a -> r) -> r) (\\(a :: *) -> \\(b :: *) -> b (\\(r :: * -> * -> *) -> r a b)))) spine) (\\(r :: * -> * -> *) -> r a b)) b a -> r) -> z)"
--
-- "/\\(a :: *) -> /\\(b :: *) -> wrap (\\(b :: ((* -> * -> *) -> *) -> *) -> \\(p :: (* -> * -> *) -> *) -> p ((\\(interlist :: * -> * -> *) -> \\(a :: *) -> \\(b :: *) -> all (r :: *). r -> (a -> b -> interlist b a -> r) -> r) (\\(a :: *) -> \\(b :: *) -> b (\\(r :: * -> * -> *) -> r a b)))) (\\(r :: * -> * -> *) -> r a b) (/\\(r :: *) -> \\(z : r) -> \\(f : a -> b -> (\\(a :: *) -> \\(b :: *) -> ifix (\\(b :: ((* -> * -> *) -> *) -> *) -> \\(p :: (* -> * -> *) -> *) -> p ((\\(interlist :: * -> * -> *) -> \\(a :: *) -> \\(b :: *) -> all (r :: *). r -> (a -> b -> interlist b a -> r) -> r) (\\(a :: *) -> \\(b :: *) -> b (\\(r :: * -> * -> *) -> r a b)))) (\\(r :: * -> * -> *) -> r a b)) b a -> r) -> z)"
--
--
--
-- "/\\(a :: *) -> /\\(b :: *) -> \\(x : a) -> \\(y : b) -> \\(xs : (\\(a :: *) -> \\(b :: *) -> (\\(spine :: (* -> * -> *) -> *) -> ifix (\\(b :: ((* -> * -> *) -> *) -> *) -> \\(p :: (* -> * -> *) -> *) -> p ((\\(interlist :: * -> * -> *) -> \\(a :: *) -> \\(b :: *) -> all (r :: *). r -> (a -> b -> interlist b a -> r) -> r) (\\(a :: *) -> \\(b :: *) -> b (\\(r :: * -> * -> *) -> r a b)))) spine) (\\(r :: * -> * -> *) -> r a b)) b a) -> wrap (\\(b :: ((* -> * -> *) -> *) -> *) -> \\(p :: (* -> * -> *) -> *) -> p ((\\(interlist :: * -> * -> *) -> \\(a :: *) -> \\(b :: *) -> all (r :: *). r -> (a -> b -> interlist b a -> r) -> r) (\\(a :: *) -> \\(b :: *) -> b (\\(r :: * -> * -> *) -> r a b)))) (\\(r :: * -> * -> *) -> r a b) (/\\(r :: *) -> \\(z : r) -> \\(f : a -> b -> (\\(a :: *) -> \\(b :: *) -> (\\(spine :: (* -> * -> *) -> *) -> ifix (\\(b :: ((* -> * -> *) -> *) -> *) -> \\(p :: (* -> * -> *) -> *) -> p ((\\(interlist :: * -> * -> *) -> \\(a :: *) -> \\(b :: *) -> all (r :: *). r -> (a -> b -> interlist b a -> r) -> r) (\\(a :: *) -> \\(b :: *) -> b (\\(r :: * -> * -> *) -> r a b)))) spine) (\\(r :: * -> * -> *) -> r a b)) b a -> r) -> f x y xs)"
--
-- "/\\(a :: *) -> /\\(b :: *) -> \\(x : a) -> \\(y : b) -> \\(xs : (\\(a :: *) -> \\(b :: *) -> ifix (\\(b :: ((* -> * -> *) -> *) -> *) -> \\(p :: (* -> * -> *) -> *) -> p ((\\(interlist :: * -> * -> *) -> \\(a :: *) -> \\(b :: *) -> all (r :: *). r -> (a -> b -> interlist b a -> r) -> r) (\\(a :: *) -> \\(b :: *) -> b (\\(r :: * -> * -> *) -> r a b)))) (\\(r :: * -> * -> *) -> r a b)) b a) -> wrap (\\(b :: ((* -> * -> *) -> *) -> *) -> \\(p :: (* -> * -> *) -> *) -> p ((\\(interlist :: * -> * -> *) -> \\(a :: *) -> \\(b :: *) -> all (r :: *). r -> (a -> b -> interlist b a -> r) -> r) (\\(a :: *) -> \\(b :: *) -> b (\\(r :: * -> * -> *) -> r a b)))) (\\(r :: * -> * -> *) -> r a b) (/\\(r :: *) -> \\(z : r) -> \\(f : a -> b -> (\\(a :: *) -> \\(b :: *) -> ifix (\\(b :: ((* -> * -> *) -> *) -> *) -> \\(p :: (* -> * -> *) -> *) -> p ((\\(interlist :: * -> * -> *) -> \\(a :: *) -> \\(b :: *) -> all (r :: *). r -> (a -> b -> interlist b a -> r) -> r) (\\(a :: *) -> \\(b :: *) -> b (\\(r :: * -> * -> *) -> r a b)))) (\\(r :: * -> * -> *) -> r a b)) b a -> r) -> f x y xs)"
