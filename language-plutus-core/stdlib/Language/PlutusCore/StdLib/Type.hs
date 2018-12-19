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

-- | > toDataKind _ [k1, k2 ... kn] = k1 -> k2 -> ... -> kn -> *
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

Now we bind some variables on the Haskell side, i.e. we use Haskell lambdas to bind variables and
regular function application to eliminate those lambdas which allows us to defer type reduction
business to Haskell. The @nil@ constructor is now (the semantics is still not important):

    /\(a :: *) -> wrap (\(rec :: ((* -> *) -> *) -> *) -> \(p :: (* -> *) -> *) -> p ((\(list :: * -> *) -> \(a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r) (\(a :: *) -> rec (\(r :: * -> *) -> r a)))) (\(r :: * -> *) -> r a) (/\(r :: *) -> \(z : r) -> \(f : a -> (\(a :: *) -> ifix (\(rec :: ((* -> *) -> *) -> *) -> \(p :: (* -> *) -> *) -> p ((\(list :: * -> *) -> \(a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r) (\(a :: *) -> rec (\(r :: * -> *) -> r a)))) (\(r :: * -> *) -> r a)) a -> r) -> z)

This is much better, but types are still not normalized.

-- pat  = \(list :: * -> *)              (a :: *) ->
--                       all (r :: *). r -> (a -> list a            -> r) -> r

-- pat1 = \(rec :: ((* -> *) -> *) -> *) (spine :: (* -> *) -> *) ->
--   spine (\(a :: *) -> all (r :: *). r -> (a -> rec (\list -> list a) -> r) -> r)
-}

-- pat  = \(list :: * -> *)              (a :: *) ->
--                       all (r :: *). r -> (a -> list a            -> r) -> r

-- pat1 = \(rec :: ((* -> *) -> *) -> *) (spine :: (* -> *) -> *) ->
--   spine (\(a :: *) -> all (r :: *). r -> (a -> rec (\list -> list a) -> r) -> r)

-- pat  = \(list :: * -> *)              (a :: *) ->
--                       all (r :: *). r -> (a -> list $ a            -> r) -> r

-- pat  = \(list :: * -> *)              (a :: *) ->
--                       all (r :: *). r -> (a -> (\a -> rec (\list -> list a) $ a            -> r) -> r


{- Note [Arity of patterns functors]
The arity of a pattern functor is the number of arguments the pattern functor receives in addition
to the first argument representing the recursive case. So
@f :: * -> *@                           has arity 0
@f :: (k -> *) -> k -> *@               has arity 1
@f :: (k1 -> k2 -> *) -> k1 -> k2 -> *@ has arity 2
etc
-}

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
