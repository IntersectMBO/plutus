-- needed to allow the definition of 'typeRep'
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Lift (TypeablePlc (..), LiftPlc (..)) where

import           Language.Plutus.CoreToPLC.Utils

import           Language.PlutusCore
import           Language.PlutusCore.MkPlc

import           Control.Monad

import qualified Data.ByteString.Lazy            as BSL
import           Data.List                       (elemIndex, sortBy)
import           Data.Maybe                      (fromJust)
import           GHC.Generics

-- | Class for types which have a corresponding Plutus Core type.
class TypeablePlc a where
    -- | Get the Plutus Core type corresponding to this type.
    typeRep :: (MonadQuote m) => m (Type TyName ())
    default typeRep :: (MonadQuote m, GTypeablePlc (Rep a)) => m (Type TyName ())
    typeRep = gTypeRep @(Rep a)

-- | Class for types which can be lifted into Plutus Core.
class LiftPlc a where
    -- | Get a Plutus Core term corresponding to the given value.
    lift :: (MonadQuote m) => a -> m (Term TyName Name ())
    default lift :: (MonadQuote m, Generic a, GLiftPlc (Rep a)) => a -> m (Term TyName Name ())
    lift x = gLift (from x)

-- Explicit instances

instance TypeablePlc Int where
    typeRep = pure $ appSize haskellIntSize (TyBuiltin () TyInteger)

instance LiftPlc Int where
    lift i = pure $ Constant () $ BuiltinInt () haskellIntSize $ fromIntegral i

instance TypeablePlc BSL.ByteString where
    typeRep = pure $ appSize haskellBSSize (TyBuiltin () TyByteString)

instance LiftPlc BSL.ByteString where
    lift bs = pure $ Constant () $ BuiltinBS () haskellBSSize bs

-- uses the Generic instance for Bool
instance LiftPlc Bool


-- uses Generic instance for (a, b)
instance (TypeablePlc a, TypeablePlc b) => TypeablePlc (a, b)
instance (TypeablePlc a, TypeablePlc b, LiftPlc a, LiftPlc b) => LiftPlc (a, b)

-- uses Generic instance for `Maybe`
instance (TypeablePlc a) => TypeablePlc (Maybe a)
instance (TypeablePlc a, LiftPlc a) => LiftPlc (Maybe a)

{- Note [Stlib lists]
We should use the stdlib list, but currently that uses lambdas-outside-fixpoints,
whereas the plugin uses fixpoints-outside-lambdas. See CGP-381.
-}

instance TypeablePlc a => TypeablePlc [a] where
    typeRep = do
        argType <- typeRep @a
        list <- liftQuote getBuiltinList
        pure $ TyApp () list argType

instance (TypeablePlc a, LiftPlc a) => LiftPlc [a] where
    lift [] = do
        nil <- liftQuote getBuiltinNil
        argType <- typeRep @a
        pure $ TyInst () nil argType

    lift (x:xs) = do
        cons <- liftQuote getBuiltinCons
        argType <- typeRep @a
        h <- lift x
        t <- lift xs
        pure $ mkIterApp (TyInst () cons argType) [h, t]

-- Tweaked copies of the stdlib functions, see note [Stdlib lists].

-- | @List@ as a type.
--
-- > \(a :: *). fix \(list :: *) -> all (r :: *). r -> (a -> list -> r) -> r
getBuiltinList :: Quote (Type TyName ())
getBuiltinList = do
    a    <- freshTyName () "a"
    list <- freshTyName () "list"
    r    <- freshTyName () "r"
    return
        . TyFix () list
        . TyLam () a (Type ())
        . TyForall () r (Type ())
        . TyFun () (TyVar () r)
        . TyFun () (TyFun () (TyVar () a) . TyFun () (TyApp () (TyVar () list) (TyVar () a)) $ TyVar () r)
        $ TyVar () r

-- |  '[]' as a term.
--
-- >  /\(a :: *) -> wrap /\(r :: *) -> \(z : r) (f : a -> list a -> r) -> z
getBuiltinNil :: Quote (Term TyName Name ())
getBuiltinNil = do
    (TyFix () list listF) <- getBuiltinList
    a <- freshTyName () "a"
    r <- freshTyName () "r"
    z <- freshName () "z"
    f <- freshName () "f"
    return
        . TyAbs () a (Type ())
        . Wrap () list (TyApp () listF (TyVar () a))
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () (TyVar () a) . TyFun () (TyApp () (TyVar () list) (TyVar () a)) $ TyVar () r)
        $ Var () z

-- |  '(:)' as a term.
--
-- > /\(a :: *) -> \(x : a) (xs : list a) ->
-- >     wrap /\(r :: *) -> \(z : r) (f : a -> list a -> r) -> f x xs
--
-- @listA@ appears twice in types in the term,
-- so this is not really a definition with unique names.
getBuiltinCons :: Quote (Term TyName Name ())
getBuiltinCons = do
    list1 <- getBuiltinList
    (TyFix () list listF) <- getBuiltinList
    a  <- freshTyName () "a"
    x  <- freshName () "x"
    xs <- freshName () "xs"
    r  <- freshTyName () "r"
    z  <- freshName () "z"
    f  <- freshName () "f"
    return
        . TyAbs () a (Type ())
        . LamAbs () x (TyVar () a)
        . LamAbs () xs (TyApp () list1 (TyVar () a))
        . Wrap () list (TyApp () listF (TyVar () a))
        . TyAbs () r (Type ())
        . LamAbs () z (TyVar () r)
        . LamAbs () f (TyFun () (TyVar () a) . TyFun () (TyApp () (TyVar () list) (TyVar () a)) $ TyVar () r)
        $ mkIterApp (Var () f)
          [ Var () x
          , Var () xs
          ]

-- Generic classes

class GTypeablePlc (f :: * -> *) where
    gTypeRep :: (MonadQuote m) => m (Type TyName ())

class GLiftPlc f where
    gLift :: (MonadQuote m) => f p -> m (Term TyName Name ())

-- Generic instances

{- Note [Specific generic functions]
We want to define a set of generic functions, but ones which are only valid on certain shapes
of types. However, we still have to define them via typeclasses. So we end up carefully
defining a few different functions so that they will only apply to the correct types.

The top-level generic functions `gTypeRep` and `gLift` are only defined for types which
are metadata-tagged as datatypes. This gives us the root of our function tree. Since we
don't want it to be callable on other sorts of type, we don't use it recursively but instead
define new helpers.

`gGetConstructorTypes` gets the types of each constructor, tagged with the name of the constructor.
Again, we only want to apply this to sums (the ones just inside the datatype declaration), and constructors.
That means we also need `gGetProductTypes` to handle the product cases inside the constructor, which
eventually delegates back to `typeRep` for the base case.

The same general pattern applies for `gGetConstructorArgs`.
-}

-- See Note [Ordering of constructors]
sortConstructors :: String -> String -> [(String, a)] -> [(String, a)]
sortConstructors package name cs =
    let sorted = sortBy (\(n1, _) (n2, _) -> compare n1 n2) cs
    -- we assume that 'Bool' defined in 'ghc-prim' is the real bool
    -- TODO: I don't understand why this is 'ghc-prim' rather than 'base', but that's what it seems to be
    in if package == "ghc-prim" && (name == "Bool" || name == "[]") then reverse sorted else sorted

-- See Note [Specific generic functions]
instance (GGetConstructorTypes f, Datatype d)  => GTypeablePlc (M1 D d f) where
    gTypeRep = do
        -- See note [Ordering of constructors]
        constrs <- sortConstructors (packageName @d undefined) (datatypeName @d undefined) <$> gGetConstructorTypes @f
        r <- liftQuote $ freshTyName () "r"
        let caseTys = fmap (\(_, tys) -> mkIterTyFun tys (TyVar () r)) constrs
        pure $ TyForall () r (Type ()) $ mkIterTyFun caseTys (TyVar () r)

-- See Note [Specific generic functions]
instance (GGetConstructorTypes f, GGetConstructorArgs f, Datatype d)  => GLiftPlc (M1 D d f) where
    gLift a = do
        -- See note [Ordering of constructors]
        constrs <- sortConstructors (packageName @d undefined) (datatypeName @d undefined) <$> gGetConstructorTypes @f
        constr <- gGetConstructorArgs @f (unM1 a)
        -- this is bad, but we have no way to fail gracefully here, and it should never happen
        let index = fromJust $ elemIndex (fst constr) (fmap fst constrs)
        r <- liftQuote $ freshTyName () "r"
        cases <- forM constrs $ \(n, tys) -> do
                arg <- liftQuote $ freshName () (strToBs n)
                let ty = mkIterTyFun tys (TyVar () r)
                pure (arg, ty)

        pure $ TyAbs () r (Type ()) $ mkIterLamAbs cases $ mkIterApp (Var () $ fst $ cases !! index) (snd constr)

-- Auxiliary generic functions

class GGetConstructorTypes (f :: * -> *) where
    gGetConstructorTypes :: (MonadQuote m) => m [(String, [Type TyName ()])]

instance (GGetConstructorTypes f, GGetConstructorTypes g) => GGetConstructorTypes (f :+: g) where
    gGetConstructorTypes = (++) <$> gGetConstructorTypes @f <*> gGetConstructorTypes @g

instance (GGetProductTypes f, Constructor c) => GGetConstructorTypes (M1 C c f) where
    gGetConstructorTypes = do
        tys <- gGetProductTypes @f
        pure [(conName @c undefined, tys)]

class GGetProductTypes (f :: * -> *) where
    gGetProductTypes :: (MonadQuote m) => m [Type TyName ()]

instance (GGetProductTypes f, GGetProductTypes g) => GGetProductTypes (f :*: g) where
    gGetProductTypes = (++) <$> gGetProductTypes @f <*> gGetProductTypes @g

instance GGetProductTypes U1 where
    gGetProductTypes = pure []

instance GGetProductTypes f => GGetProductTypes (M1 t i f) where
    gGetProductTypes = gGetProductTypes @f

instance (TypeablePlc a) => GGetProductTypes (K1 i a) where
    gGetProductTypes = do
        ty <- typeRep @a
        pure [ty]

class GGetConstructorArgs (f :: * -> *) where
    gGetConstructorArgs :: (MonadQuote m) => f p -> m (String, [Term TyName Name ()])

instance (GGetConstructorArgs f, GGetConstructorArgs g) => GGetConstructorArgs (f :+: g) where
    gGetConstructorArgs (L1 x) = gGetConstructorArgs @f x
    gGetConstructorArgs (R1 y) = gGetConstructorArgs @g y

instance (GGetProductArgs f, Constructor c) => GGetConstructorArgs (M1 C c f) where
    gGetConstructorArgs a = do
        args <- gGetProductArgs a
        pure (conName @c undefined, args)

class GGetProductArgs (f :: * -> *) where
    gGetProductArgs :: (MonadQuote m) => f p -> m [Term TyName Name ()]

instance (GGetProductArgs f, GGetProductArgs g) => GGetProductArgs (f :*: g) where
    gGetProductArgs (a :*: b) = (++) <$> gGetProductArgs @f a <*> gGetProductArgs @g b

instance GGetProductArgs U1 where
    gGetProductArgs _ = pure []

instance GGetProductArgs f => GGetProductArgs (M1 t i f) where
    gGetProductArgs a = gGetProductArgs @f (unM1 a)

instance (LiftPlc a) => GGetProductArgs (K1 i a) where
    gGetProductArgs a = do
        arg <- lift (unK1 a)
        pure [arg]
