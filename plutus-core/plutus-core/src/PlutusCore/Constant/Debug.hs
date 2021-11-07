{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE ViewPatterns             #-}

-- | This module helps to visualize and debug the 'TypeScheme' inference machinery from the
-- @Meaning@ module.
module PlutusCore.Constant.Debug where

import PlutusCore.Constant.Meaning
import PlutusCore.Constant.Typed
import PlutusCore.Core
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Name

import Control.Monad.Except
import Data.Functor.Compose
import Data.Kind qualified as GHC (Type)
import Data.Proxy
import Data.SOP.Constraint
import Data.String

type TermDebug = Term TyName Name DefaultUni DefaultFun ()

-- | Instantiate type variables in the type of a value using 'EnumerateFromTo'.
-- This function only performs the enumeration and checks that the result does not have certain
-- constraints, so it's allowed for the type to reference types that are not in the universe.
-- Example usages:
--
-- >>> :t enumerateDebug False
-- enumerateDebug False :: Bool
-- >>> :t enumerateDebug $ Just 'a'
-- enumerateDebug $ Just 'a' :: Maybe Char
-- >>> :t enumerateDebug $ \_ -> ()
-- enumerateDebug $ \_ -> ()
--   :: Opaque
--        (Term TyName Name DefaultUni DefaultFun ())
--        (TyVarRep ('TyNameRep "a" 0))
--      -> ()
-- >>> :t enumerateDebug 42
-- <interactive>:1:16-17: error:
--     • Built-in functions are not allowed to have constraints
--       To fix this error instantiate all constrained type variables
--     • In the first argument of ‘enumerateDebug’, namely ‘42’
--       In the expression: enumerateDebug 42
enumerateDebug :: forall a j. EnumerateFromTo 0 j TermDebug a => a -> a
enumerateDebug = id

-- | Instantiate type variables in the type of a value using 'EnumerateFromTo' and check that it's
-- possibe to construct a 'TypeScheme' out of the resulting type. Example usages:
--
-- >>> :t inferDebug False
-- inferDebug False :: Bool
-- >>> :t inferDebug $ Just 'a'
-- <interactive>:1:1-21: error:
--     • There's no 'KnownType' instance for Maybe Char
--       Did you add a new built-in type and forget to provide a 'KnownType' instance for it?
--     • In the expression: inferDebug $ Just 'a'
-- >>> :t inferDebug $ \_ -> ()
-- inferDebug $ \_ -> ()
--   :: Opaque
--        (Term TyName Name DefaultUni DefaultFun ())
--        (TyVarRep ('TyNameRep "a" 0))
--      -> ()
inferDebug
    :: forall a binds args res j.
       ( args ~ GetArgs a, a ~ FoldArgs args res, binds ~ Merge (ListToBinds args) (ToBinds res)
       , KnownPolytype binds TermDebug args res a, EnumerateFromTo 0 j TermDebug a
       , KnownMonotype TermDebug args res a
       )
    => a -> a
inferDebug = id

{- | 'SomeConstantOf' is a safe version of 'SomeConstantPoly' almost forcing the user to write the
right thing.

A @SomeConstantOf uni f reps@ is a value of existentially instantiated @f@. For instance,
a @SomeConstantOf uni [] reps@ is a list of something (a list of integers or a list of lists
of booleans etc). And a @SomeConstantOf uni (,) reps@ is a tuple of something.

The @reps@ parameter serves two purposes: its main purpose is to specify how the argument
types look on the PLC side (i.e. it's the same thing as with @Opaque term rep@), so that
we can apply the type of built-in lists to a PLC type variable for example. The secondary
purpose is ensuring type safety via indexing: a value of @SomeConstantOf uni f reps@ can be viewed
as a proof that the amount of arguments @f@ expects and the length of @reps@ are the same number
(we could go even further and compute the kind of @f@ from @reps@, but it doesn't seem like
that would give us any more type safety while it certainly would be a more complex thing to do).

The existential Haskell types @f@ is applied to are reified as type tags from @uni@.
Note however that the correspondence between the Haskell types and the PLC ones from @reps@ is
not demanded and this is by design: during evaluation (i.e. on the Haskell side of things)
we always have concrete type tags, but at Plutus compile time an argument to @f@ can be
a Plutus type variable and so we can't establish any connection between the type tag that
we'll end up having at runtime and a Plutus type variable that we have at compile time.
Which also implies that one can specify that a built-in function takes, say, a tuple of a type
variable and a boolean, but in the actual denotation unlift to a tuple of a unit and an integer
(boolean vs integer) and there won't be any Haskell type error for that, let alone a Plutus type
error -- it'll be an evaluation failure, maybe even a delayed one.
So be careful in the denotation of a builtin to unlift its arguments to what you promised to
unlift them to in its type signature.
-}
type SomeConstantOf :: forall k. (GHC.Type -> GHC.Type) -> k -> [GHC.Type] -> GHC.Type
data SomeConstantOf uni f reps where
    SomeConstantOfRes :: uni (Esc b) -> b -> SomeConstantOf uni b '[]
    SomeConstantOfArg
        :: uni (Esc a)
        -> SomeConstantOf uni (f a) reps
        -> SomeConstantOf uni f (rep ': reps)

-- | Extract the value stored in a 'SomeConstantOf'.
runSomeConstantOf :: HasHiddenValueOf uni => SomeConstantOf uni f reps -> HiddenValueOf uni
runSomeConstantOf (SomeConstantOfRes uniA x) = hiddenValueOf uniA x
runSomeConstantOf (SomeConstantOfArg _ svn)  = runSomeConstantOf svn

instance (uni `Contains` f, uni ~ uni', All (KnownTypeAst uni) reps) =>
            KnownTypeAst uni (SomeConstantOf uni' f reps) where
    type ToBinds (SomeConstantOf uni' f reps) = ListToBinds reps

    toTypeAst _ = toTypeAst $ Proxy @(SomeConstantPoly uni f reps)

-- | State needed during unlifting of a 'SomeConstantOf'.
type ReadSomeConstantOf
        :: forall k. (GHC.Type -> GHC.Type) -> (GHC.Type -> GHC.Type) -> k -> [GHC.Type] -> GHC.Type
data ReadSomeConstantOf m uni f reps =
    forall k (a :: k). ReadSomeConstantOf (SomeConstantOf uni a reps) (uni (Esc a))

instance (KnownBuiltinTypeIn uni term f, All (KnownTypeAst uni) reps, HasUniApply uni) =>
            KnownTypeIn uni term (SomeConstantOf uni f reps) where
    makeKnown _ = pure . fromConstant . runSomeConstantOf

    readKnown (mayCause :: Maybe cause) term = asConstant mayCause term >>= \case
        (toSomeValueOf -> Some (ValueOf uni xs)) -> do
            let uniF = knownUni @_ @_ @f
                err = fromString $ concat
                    [ "Type mismatch: "
                    , "expected an application of: " ++ gshow uniF
                    , "; but got the following type: " ++ gshow uni
                    ]
                wrongType :: (MonadError (ErrorWithCause err cause) m, AsUnliftingError err) => m a
                wrongType = throwingWithCause _UnliftingError err mayCause
            -- In order to prove that the type of @xs@ is an application of @f@ we need to
            -- peel all type applications off in the type of @xs@ until we get to the head and then
            -- check that the head is indeed @f@. Each peeled type application becomes a
            -- 'SomeConstantOfArg' in the final result.
            ReadSomeConstantOf res uniHead <-
                cparaM_SList @_ @(KnownTypeAst uni) @reps
                    Proxy
                    (ReadSomeConstantOf (SomeConstantOfRes uni xs) uni)
                    (\(ReadSomeConstantOf acc uniApp) ->
                        matchUniApply
                            uniApp
                            wrongType
                            (\uniApp' uniA ->
                                pure $ ReadSomeConstantOf (SomeConstantOfArg uniA acc) uniApp'))
            case uniHead `geq` uniF of
                Nothing   -> wrongType
                Just Refl -> pure res

instance {-# OVERLAPPING #-}
    ( TrySpecializeAsVar i j term (Opaque term rep)
    , HandleSpecialCases j k term (SomeConstantOf uni f reps)
    ) => HandleSpecialCases i k term (SomeConstantOf uni f (rep ': reps))

-- | Like 'cpara_SList' but the folding function is monadic.
cparaM_SList
    :: forall k c (xs :: [k]) proxy r m. (All c xs, Monad m)
    => proxy c
    -> r '[]
    -> (forall y ys. (c y, All c ys) => r ys -> m (r (y ': ys)))
    -> m (r xs)
cparaM_SList p z f =
    getCompose $ cpara_SList
        p
        (Compose $ pure z)
        (\(Compose r) -> Compose $ r >>= f)
