-- | This module assigns types to built-ins.
-- See the @plutus/plutus-core/docs/Constant application.md@
-- article for how this emerged.

{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE DefaultSignatures        #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}

module PlutusCore.Constant.Typed
    ( TypeScheme (..)
    , FoldArgs
    , FoldArgsEx
    , unliftConstant
    , TyNameRep (..)
    , TyVarRep
    , TyAppRep
    , TyForallRep
    , Opaque (..)
    , AsConstant (..)
    , FromConstant (..)
    , HasConstant
    , HasConstantIn
    , KnownTypeAst (..)
    , KnownType (..)
    , makeKnownNoEmit
    , KnownTypeMonad (..)
    , SomeValueN (..)
    , At (..)
    ) where

import           PlutusPrelude

import           PlutusCore.Constant.Dynamic.Emit
import           PlutusCore.Core
import           PlutusCore.Evaluation.Machine.ExBudget
import           PlutusCore.Evaluation.Machine.ExMemory
import           PlutusCore.Evaluation.Machine.Exception
import           PlutusCore.Evaluation.Result
import           PlutusCore.MkPlc
import           PlutusCore.Name
import           PlutusCore.Universe

import           Control.Lens.Prism
import           Control.Lens.TH
import           Control.Monad.Except
import qualified Data.ByteString                         as BS
import           Data.Functor.Compose
import           Data.Functor.Const
import qualified Data.Kind                               as GHC (Type)
import           Data.Proxy
import           Data.SOP.Constraint
import           Data.String
import qualified Data.Text                               as Text
import           GHC.TypeLits

infixr 9 `TypeSchemeArrow`

-- | Type schemes of primitive operations.
-- @as@ is a list of types of arguments, @r@ is the resulting type.
-- E.g. @Char -> Bool -> Integer@ is encoded as @TypeScheme term [Char, Bool] Integer@.
data TypeScheme term (args :: [GHC.Type]) res where
    TypeSchemeResult
        :: KnownType term res
        => Proxy res -> TypeScheme term '[] res
    TypeSchemeArrow
        :: KnownType term arg
        => Proxy arg -> TypeScheme term args res -> TypeScheme term (arg ': args) res
    TypeSchemeAll
        :: (KnownSymbol text, KnownNat uniq, KnownKind kind)
           -- Here we require the user to manually provide the unique of a type variable.
           -- That's nothing but silly, but I do not see what else we can do with the current design.
        => Proxy '(text, uniq, kind)
           -- We use a funny trick here: instead of binding
           --
           -- > TyVarRep ('TyNameRep @kind text uniq)
           --
           -- directly we introduce an additional and "redundant" type variable. The reason why we
           -- do that is because this way we can also bind such a variable later when constructing
           -- the 'TypeScheme' of a polymorphic builtin manually, so that for the user this looks
           -- exactly like a single bound type variable instead of this weird @TyVarRep@ thing.
        -> (forall ot. ot ~ TyVarRep ('TyNameRep @kind text uniq) =>
               Proxy ot -> TypeScheme term args res)
        -> TypeScheme term args res

-- | Turn a list of Haskell types @as@ into a functional type ending in @r@.
--
-- >>> :set -XDataKinds
-- >>> :kind! FoldArgs [Char, Bool] Integer
-- FoldArgs [Char, Bool] Integer :: *
-- = Char -> Bool -> Integer
type family FoldArgs args res where
    FoldArgs '[]           res = res
    FoldArgs (arg ': args) res = arg -> FoldArgs args res

-- | Calculates the parameters of the costing function for a builtin.
type family FoldArgsEx args where
    FoldArgsEx '[]           = ExBudget
    FoldArgsEx (arg ': args) = ExMemory -> FoldArgsEx args

{- Note [Motivation for polymorphic built-in functions]
We need to support polymorphism for built-in functions for these reasons:

1. @ifThenElse@ for 'Bool' (being a built-in type rather than a Scott-encoded one) has to be
   polymorphic as its type signature is

       ifThenElse : all a. Bool -> a -> a -> a

   Previously we had 'Bool' as a Scott-encoded type, but this required plenty of supporting machinery,
   because unlifting (aka Scott-decoding) a PLC 'Bool' into a Haskell 'Bool' is quite a non-trivial
   thing, see https://github.com/input-output-hk/plutus/blob/e222466e6d46bbca9f76243bb496b3c88ed02ca1/language-plutus-core/src/PlutusCore/Constant/Typed.hs#L165-L252

   Now that we got rid of all this complexity we have to pay for that by supporting polymorphic
   built-in functions (but we added that support long ago anyway, 'cause it was easy to do).

2. we may want to add efficient polymorphic built-in types like @IntMap@ or @Vector@ and most functions
   defined over them are polymorphic as well
-}

{- Note [Implemetation of polymorphic built-in functions]
Encoding polymorphism in an AST in an intrinsically-typed manner is not a pleasant thing to do in Haskell.
It's not impossible, see "Embedding F", Sam Lindley: http://homepages.inf.ed.ac.uk/slindley/papers/embedding-f.pdf
But we'd rather avoid such heavy techniques.

Fortunately, there is a simple trick: we have parametricity in Haskell, so a function that is
polymorphic in its argument can't inspect that argument in any way and so we never actually need to
convert such an argument from PLC to Haskell just to convert it back later without ever inspecting
the value. Instead we can keep the argument intact and apply the Haskell function directly to
the PLC AST representing some value.

E.g. Having a built-in function with the following signature (assuming we somehow have a PLC @list@
mapping to Haskell @[]@ -- that was possible before, but not now, but the example is still instructive):

    reverse : all a. list a -> list a

that maps to Haskell's

    reverse :: forall a. [a] -> [a]

evaluation of

    PLC.reverse {bool} (cons true (cons false nil))

proceeds as follows:

      PLC.reverse {bool} (cons true (cons false nil))
    ~ makeKnown (Haskell.reverse (readKnown (cons true (cons false nil))))
    ~ makeKnown (Haskell.reverse [Opaque true, Opaque false])
    ~ makeKnown [Opaque false, Opaque true]
    ~ EvaluationSuccess (cons false (cons true nil))

Note how we use the 'Opaque' wrapper in order to unlift a PLC term as an opaque Haskell value
using 'readKnown' and then lift the term back using 'makeKnown' without ever inspecting the term.

An opaque PLC @term@ whose type is a PLC type variable `a_0` has the following type on the Haskell
side:

    Opaque term (TyVarRep ('TyNameRep "a" 0))

where that last argument is a direct counterpart of the term-level

    TyVar () (TyName (Name "a" 0))

@Opaque term rep@ can be used for passing any @term@ through the builtin application machinery,
not just one whose type is a bound variable. For example, you can define a new data type

    data NatRep

provide a 'KnownTypeAst' instance for it (mapping a @Proxy NatRep@ to the actual type of natural
numbers in PLC) and define a (rather pointless) builtin like @idNat : nat -> nat@.

It's also possible to bind a type variable of a higher-kind, say, @f :: * -> *@ and make a builtin
with the following signature:

    idFInteger : all (f :: * -> *). f integer -> f integer

where the type application is handled with 'TyAppRep'. Note that the latter is defined as a
@data family@:

    data family TyAppRep (fun :: dom -> cod) (arg :: dom) :: cod

We do that because a @data family@ can return a poly-kinded argument, which allows us to get an
intrinsically-kinded representation of PLC types. For example, an opaque @term@ whose type is an
application of a type variable @f@ to a type variable @a@ is represented like this:

    Opaque term (TyAppRep (TyVarRep ('TyNameRep "f" 0)) (TyVarRep ('TyNameRep "a" 1 :: TyNameRep *)))

Note the @TyNameRep *@ kind annotation. It tells us three things:

1. a type-level name has a kind associated with it. The reason for that is that we use names in
binders (for example, in the universal quantifier) and as variables and kinds are important in
both these cases due to us having an intrinsically-kinded representation of types, so it's
convenient to annotate type-level names with kinds. Another reason is that we do not attempt to do
any kind of static analysis on reflected type variables and associating kinds with them allows us
to catch errors like "two variables with equal names and uniques, but different kinds" earlier
2. the kind is not stored as an argument to the @TyNameRep@ constructor. Instead it's stored as
an index of the data type. The point of this is that if we stored the kind as an argument, we'd
have to provide it manually, but since the representation is intrinsically-kinded there's no point
in doing so as GHC can infer all the kinds itself
3. ... apart from cases where they're inherently ambiguous, like in the case above. If we don't
specify the kind of the @a_1@ type variable, then there's no way GHC could infer it as the variable
is passed as an argument to another variable with an unspecified kind (@f_0@)
4. finally, an opaque term can only be of a type of kind @*@. You can't construct a term whose type
is of some other kind. That's why we don't need to annotate the @f_0@ type variable: the domain is
inferred from the kind of the argument (where it's explicitly specified via @TyNameRep *@) and the
codomain is inferred from the fact that the whole type is passed to 'Opaque' and so it has to be
of kind @*@

It would be nice if we didn't need to define that @*Rep@ stuff at the type level just to demote it
to the term level via a type class, but this hasn't been investigated yet. A plausible way would be
to ditch 'KnownTypeAst' (but keep 'KnownType') and provide PLC types manually. But that doesn't seem
to give rise to a terribly nice API. And we'd lose all the static guarantees, which is not a big
deal, but losing the automatic inference of type schemes would suck, given that it's already quite
handy and is going to be improved.

Representing contructors as poly-kinded data families and handling those with open type families
and/or type classes is a way of solving the expression problem for indexed data types at the type
level, if you are into these things.
-}

-- | Representation of a type variable: its name and unique and an implicit kind.
data TyNameRep (kind :: GHC.Type) = TyNameRep Symbol Nat

-- | Representation of an intrinsically-kinded type variable: a name.
data family TyVarRep (var :: TyNameRep kind) :: kind

-- | Representation of an intrinsically-kinded type application: a function and an argument.
data family TyAppRep (fun :: dom -> cod) (arg :: dom) :: cod

-- | Representation of of an intrinsically-kinded universal quantifier: a bound name and a body.
data family TyForallRep (var :: TyNameRep kind) (a :: GHC.Type) :: GHC.Type

-- See Note [Motivation for polymorphic built-in functions]
-- See Note [Implemetation of polymorphic built-in functions]
-- | The denotation of a term whose PLC type is encoded in @rep@ (for example a type variable or
-- an application of a type variable). I.e. the denotation of such a term is the term itself.
-- This is because we have parametricity in Haskell, so we can't inspect a value whose
-- type is, say, a bound variable, so we never need to convert such a term from Plutus Core to
-- Haskell and back and instead can keep it intact.
newtype Opaque term (rep :: GHC.Type) = Opaque
    { unOpaque :: term
    } deriving newtype (Pretty)

class AsConstant term where
    -- | Unwrap a shallowly embedded Haskell value from a @term@ or fail.
    asConstant :: term -> Maybe (Some (ValueOf (UniOf term)))

class FromConstant term where
    -- | Wrap a Haskell value as a @term@.
    fromConstant :: Some (ValueOf (UniOf term)) -> term

instance AsConstant (Term TyName Name uni fun ann) where
    asConstant (Constant _ val) = Just val
    asConstant _                = Nothing

instance (Closed uni, uni `Everywhere` ExMemoryUsage) =>
            FromConstant (Term tyname name uni fun ExMemory) where
    fromConstant value = Constant (memoryUsage value) value

instance FromConstant (Term tyname name uni fun ()) where
    fromConstant = Constant ()

-- | Ensures that @term@ has a 'Constant'-like constructor to lift values to and unlift values from.
--
-- 'AsConstant' and 'FromConstant' are separate, because we need only one instance of 'AsConstant'
-- per 'Term'-like type and 'FromConstant' requires as many instances as there are different kinds
-- of annotations (we're mostly interested in 'ExMemory' and @()@). Originally we had a single type
-- class but it proved to be less efficient than having two of them.
type HasConstant term = (AsConstant term, FromConstant term)

-- | Ensures that @term@ has a 'Constant'-like constructor to lift values to and unlift values from
-- and connects @term@ and its @uni@.
type HasConstantIn uni term = (UniOf term ~ uni, HasConstant term)

-- | Extract the 'Constant' from a 'Term'
-- (or throw an error if the term is not a 'Constant' or the constant is not of the expected type).
unliftConstant
    :: forall a m term err.
       (MonadError (ErrorWithCause err term) m, AsUnliftingError err, KnownBuiltinType term a)
    => term -> m a
unliftConstant term = case asConstant term of
    Just (Some (ValueOf uniAct x)) -> do
        let uniExp = knownUni @(UniOf term) @a
        case uniAct `geq` uniExp of
            Just Refl -> pure x
            Nothing   -> do
                let err = fromString $ concat
                        [ "Type mismatch: "
                        , "expected: " ++ gshow uniExp
                        , "; actual: " ++ gshow uniAct
                        ]
                throwingWithCause _UnliftingError err $ Just term
    Nothing -> throwingWithCause _UnliftingError "Not a constant" $ Just term

{- Note [KnownType's defaults]
We'd like to use @default@ for providing instances for built-in types instead of @DerivingVia@,
because the latter breaks on @m a@

It's possible to circumvent this, by using @forall r. (a -> m r) -> m r@ instead,
but then we need to recover the original handy definitions and make the API and
the code bloated (instances are more verbose with @DerivingVia@).

We don't use @default@ in 'KnownTypeAst', because an attempt to write

    default toTypeAst :: (k ~ GHC.Type, uni `Includes` a) => proxy a -> Type TyName uni ()
    toTypeAst = toBuiltinTypeAst

results in

    Expected kind '* -> *', but 'uni' has kind 'k -> *'

see https://gitlab.haskell.org/ghc/ghc/-/issues/15710
-}

class KnownTypeAst uni (a :: k) where
    -- | The type representing @a@ used on the PLC side.
    toTypeAst :: proxy a -> Type TyName uni ()

-- | A constraint for \"@a@ is a 'KnownType' by means of being included in @uni@\".
type KnownBuiltinTypeIn uni term a = (HasConstantIn uni term, GShow uni, GEq uni, uni `Contains` a)

-- | A constraint for \"@a@ is a 'KnownType' by means of being included in @UniOf term@\".
type KnownBuiltinType term a = KnownBuiltinTypeIn (UniOf term) term a

-- See Note [KnownType's defaults].
-- | A default implementation of 'toTypeAst' for built-in types.
toBuiltinTypeAst :: uni `Contains` a => proxy a -> Type TyName uni ()
toBuiltinTypeAst (_ :: proxy a) = mkTyBuiltin @a ()

-- See Note [KnownType's defaults]
-- | Haskell types known to exist on the PLC side.
class KnownTypeAst (UniOf term) a => KnownType term a where
    -- | Convert a Haskell value to the corresponding PLC term.
    -- The inverse of 'readKnown'.
    makeKnown
        :: ( MonadError (ErrorWithCause err term) m, AsUnliftingError err, AsEvaluationFailure err
           , MonadEmitter m
           )
        => a -> m term
    default makeKnown
        :: ( MonadError err m
           , KnownBuiltinType term a
           )
        => a -> m term
    -- Forcing the value to avoid space leaks. Note that the value is only forced to WHNF,
    -- so care must be taken to ensure that every value of a type from the universe gets forced
    -- to NF whenever it's forced to WHNF.
    makeKnown x = pure . fromConstant . someValue $! x

    -- | Convert a PLC term to the corresponding Haskell value.
    -- The inverse of 'makeKnown'.
    readKnown
        :: ( MonadError (ErrorWithCause err term) m, AsUnliftingError err, AsEvaluationFailure err
           )
        => term -> m a
    default readKnown
        :: ( MonadError (ErrorWithCause err term) m, AsUnliftingError err
           , KnownBuiltinType term a
           )
        => term -> m a
    readKnown = unliftConstant

newtype NoCauseT term m a = NoCauseT
    { unNoCauseT :: m a
    } deriving newtype (Functor, Applicative, Monad)

newtype NoUnliftingError err = NoUnliftingError err
makePrisms ''NoUnliftingError

instance AsEvaluationFailure err => AsUnliftingError (NoUnliftingError err) where
    _UnliftingError = prism (\_ -> NoUnliftingError evaluationFailure) Left

instance AsEvaluationFailure err => AsEvaluationFailure (NoUnliftingError err) where
    _EvaluationFailure = _NoUnliftingError . _EvaluationFailure

instance (MonadError err m, AsEvaluationFailure err) =>
            MonadError (ErrorWithCause (NoUnliftingError err) term) (NoCauseT term m) where
    throwError _ = NoCauseT $ throwError evaluationFailure
    NoCauseT a `catchError` h =
        NoCauseT $ a `catchError` \err ->
            unNoCauseT . h $ ErrorWithCause (NoUnliftingError err) Nothing

makeKnownNoEmit
    :: forall term a err m. (KnownType term a, MonadError err m, AsEvaluationFailure err)
    => a -> m term
makeKnownNoEmit = unNoCauseT @_ @term . unNoEmitterT . makeKnown

newtype KnownTypeMonad term a = KnownTypeMonad
    { unKnownTypeMonad
          :: forall err m.
              ( MonadError (ErrorWithCause err term) m, AsUnliftingError err
              , MonadEmitter m, AsEvaluationFailure err
              )
          => m a
    } deriving (Functor)

instance Applicative (KnownTypeMonad term) where
    pure x = KnownTypeMonad $ pure x
    KnownTypeMonad f <*> KnownTypeMonad a = KnownTypeMonad $ f <*> a

instance Monad (KnownTypeMonad term) where
    KnownTypeMonad a >>= f = KnownTypeMonad $ a >>= unKnownTypeMonad . f

instance KnownTypeAst uni a => KnownTypeAst uni (KnownTypeMonad m a) where
    toTypeAst _ = toTypeAst $ Proxy @a

instance (KnownType term a, term ~ term') => KnownType term (KnownTypeMonad term' a) where
    makeKnown = unKnownTypeMonad >=> makeKnown
    readKnown = throwingWithCause _UnliftingError "Not supported" . Just

instance KnownTypeAst uni a => KnownTypeAst uni (EvaluationResult a) where
    toTypeAst _ = toTypeAst $ Proxy @a

instance (KnownTypeAst (UniOf term) a, KnownType term a) =>
            KnownType term (EvaluationResult a) where
    makeKnown EvaluationFailure     = throwError evaluationFailure
    makeKnown (EvaluationSuccess x) = makeKnown x

    -- Catching 'EvaluationFailure' here would allow *not* to short-circuit when 'readKnown' fails
    -- to read a Haskell value of type @a@. Instead, in the denotation of the builtin function
    -- the programmer would be given an explicit 'EvaluationResult' value to handle, which means
    -- that when this value is 'EvaluationFailure', a PLC 'Error' was caught.
    -- I.e. it would essentially allow us to catch errors and handle them in a programmable way.
    -- We forbid this, because it complicates code and isn't supported by evaluation engines anyway.
    readKnown = throwingWithCause _UnliftingError "Error catching is not supported" . Just

instance KnownTypeAst uni a => KnownTypeAst uni (Emitter a) where
    toTypeAst _ = toTypeAst $ Proxy @a

instance KnownType term a => KnownType term (Emitter a) where
    makeKnown = unEmitter >=> makeKnown
    -- TODO: we really should tear 'KnownType' apart into two separate type classes.
    readKnown = throwingWithCause _UnliftingError "Can't unlift an 'Emitter'" . Just

type SomeValueN :: forall k. (GHC.Type -> GHC.Type) -> k -> [GHC.Type] -> GHC.Type
data SomeValueN uni (a :: k) reps where
    SomeValueRes :: uni a -> a -> SomeValueN uni a '[]
    SomeValueArg :: uni a -> SomeValueN uni (f a) reps -> SomeValueN uni f (rep ': reps)

-- type SomeValueN :: forall k. (GHC.Type -> GHC.Type) -> k -> GHC.Type
-- data SomeValueN uni (a :: k) where
--     SomeValueRes :: uni a -> a -> SomeValueN uni a
--     SomeValueArg :: uni a -> SomeValueN uni (f a) -> SomeValueN uni f

type At :: GHC.Type -> [GHC.Type] -> GHC.Type
newtype a `At` reps = At
    { unAt :: a
    }

-- foldlVec :: forall p a m.
--             (forall n. a -> p n -> p (S n)) ->
--             p Z ->
--             Vec a m -> p m

cparaP_SList
    :: forall k c (xs :: [k]) proxy r. All c xs
    => proxy c
    -> r '[]
    -> (forall y ys. (c y, All c ys) => Proxy (All c (y ': ys)) -> r ys -> r (y ': ys))
    -> r xs
cparaP_SList p z f = cpara_SList p z $ f Proxy

cfoldr_SList
    :: forall c xs r proxy. All c xs
    => proxy (All c xs)
    -> (forall y ys. (c y, All c ys) => Proxy (All c (y ': ys)) -> r -> r)
    -> r
    -> r
cfoldr_SList _ f z = getConst $ cparaP_SList @_ @c @xs Proxy (coerce z) (coerce . f)

cfoldl_SList
    :: forall c xs r proxy. All c xs
    => proxy (All c xs)
    -> (forall y ys. (c y, All c ys) => Proxy (All c (y ': ys)) -> r -> r)
    -> r
    -> r
cfoldl_SList _ f z = undefined

-- instance (uni `Contains` TypeApp f, uni ~ uni') => KnownTypeAst uni (SomeValueN uni' f) where
--     toTypeAst _ = mkTyBuiltin @(TypeApp f) ()

-- instance (KnownTypeAst uni a, All (KnownTypeAst uni) reps) => KnownTypeAst uni (a `At` reps) where
--     toTypeAst _ =
--         mkIterTyApp () (toTypeAst $ Proxy @a) $
--             cfoldr_SList
--                 (Proxy @(All (KnownTypeAst uni) reps))
--                 (\(_ :: Proxy (All (KnownTypeAst uni) (rep ': _reps'))) rs ->
--                     toTypeAst (Proxy @rep) : rs)
--                 []

instance (uni `Contains` TypeApp f, uni ~ uni', All (KnownTypeAst uni) reps) =>
            KnownTypeAst uni (SomeValueN uni' f reps) where
    toTypeAst _ =
        mkIterTyApp () (mkTyBuiltin @(TypeApp f) ()) $
            cfoldr_SList
                (Proxy @(All (KnownTypeAst uni) reps))
                (\(_ :: Proxy (All (KnownTypeAst uni) (rep ': _reps'))) rs ->
                    toTypeAst (Proxy @rep) : rs)
                []

-- newtype ReadSomeValueN r m f = ReadSomeValueN
--     { unReadSomeValueN
--         :: forall k (a :: k). r a -> uni (TypeApp a) -> m (r f)
--     }

-- '[]
-- '[1]
-- '[1,2]
-- ...



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


-- cparaP_SList
--     :: forall k c (xs :: [k]) proxy r. All c xs
--     => proxy c
--     -> r '[]
--     -> (forall y ys. (c y, All c ys) => Proxy (All c (y ': ys)) -> r ys -> r (y ': ys))
--     -> r xs
-- cparaP_SList p z f = cpara_SList p z $ f Proxy

-- reps ~ repsL ++ repsR

-- celimL_SList
--     :: forall k c (xs :: [k]) proxy r. All c xs
--     => proxy c
--     -> r '[]
--     -> (forall y ys. (c y, All c ys) => Proxy (All c (y ': ys)) -> r ys -> r (y ': ys))
--     -> r xs
-- celimL_SList p z f = undefined

-- foldlViaFoldr
--   : ∀ {a b} {A : Set a} (B : ℕ → Set b) {m} →
--     (∀ {n} → B n → A → B (suc n)) →
--     B zero →
--     Vec A m → B m
-- foldlViaFoldr {A = A} b {m} f z xs =
--   foldr
--     (λ n -> ∀ B -> (∀ {n} -> B n -> A -> B (suc n)) -> B 0 -> B n)
--     (λ x r B f' z' -> r (B ∘′ suc) f' $ f' z' x)
--     (λ _ _ -> id)
--     xs
--     b
--     f
--     z

newtype IFoldMMotive c m (xs :: [k]) = IFoldMMotive
    { unIFoldMMotive
        :: forall r.
           r '[]
        -> (forall y ys. (c y, All c ys) => Proxy y -> r ys -> m (r (y ': ys)))
        -> m (r xs)
    }

-- cparaP_SList
--     :: forall k c (xs :: [k]) proxy r. All c xs
--     => proxy c
--     -> r '[]
--     -> (forall y ys. (c y, All c ys) => Proxy (All c (y ': ys)) -> r ys -> r (y ': ys))
--     -> r xs
-- cparaP_SList p z f = cpara_SList p z $ f Proxy

type family Ins y xs where
    Ins y '[]       = '[y]
    Ins y (x ': xs) = x ': y ': xs

newtype StepR r y ys = StepR
    { unStepR :: r (y ': ys)
    }

-- cifoldM_SList
--     :: forall k c (xs :: [k]) proxy r m. (All c xs, Monad m)
--     => proxy c
--     -> r '[]
--     -> (forall y ys. (c y, All c ys) => r ys -> m (r (y ': ys)))
--     -> m (r xs)
-- cifoldM_SList p = undefined where -- unIFoldMMotive $ cpara_SList p zM fM where
--     zM :: IFoldMMotive c m '[]
--     zM = IFoldMMotive $ \z _ -> pure z

--     fM :: forall y ys. c y => IFoldMMotive c m ys -> IFoldMMotive c m (y ': ys)
--     fM (IFoldMMotive h) = IFoldMMotive $ \z f -> do
--         z' <- f Proxy z
--         unStepR <$> h (StepR z') (\p -> fmap _ . f p . unStepR) -- (\sr -> fmap StepR $ f $ unStepR sr)

--  f :: (forall y ys. (c y, All c ys) => r ys -> m (r (y ': ys)))

-- z' :: r [y]
-- f' :: (forall y ys. (c y, All c ys) => r (z ': ys) -> m (r (y ': z ': ys)))


instance
        ( KnownTypeAst uni (SomeValueN uni f reps)
        , KnownBuiltinTypeIn uni term (TypeApp f)
        , All (KnownTypeAst uni) reps
        , HasUniApply uni
        ) => KnownType term (SomeValueN uni f reps) where
    makeKnown = go where
        go :: Monad m => SomeValueN uni f' reps' -> m term
        go (SomeValueRes uniA x) = pure . fromConstant . Some $ ValueOf uniA x
        go (SomeValueArg _ svn)  = go svn

    readKnown term = case asConstant term of
        Nothing -> throwingWithCause _UnliftingError "Not a constant" $ Just term
        Just (Some (ValueOf uni xs)) -> do
            let uniF = knownUni @_ @(TypeApp f)
                err = fromString $ concat
                    [ "Type mismatch: "
                    , "expected an application of: " ++ gshow uniF
                    , "; but got the following type: " ++ gshow uni
                    ]
                wrongType :: (MonadError (ErrorWithCause err term) m, AsUnliftingError err) => m a
                wrongType = throwingWithCause _UnliftingError err $ Just term
            ReadSomeValueN res uniHead <-
                matchUniRunTypeApp
                    uni
                    wrongType
                    (\uniApp0 ->
                        cparaM_SList @_ @(KnownTypeAst uni) @reps
                            Proxy
                            (ReadSomeValueN (SomeValueRes uni xs) uniApp0)
                            (\(ReadSomeValueN acc uniApp) ->
                                matchUniApply
                                    uniApp
                                    wrongType
                                    (\uniApp' uniA ->
                                        pure $ ReadSomeValueN (SomeValueArg uniA acc) uniApp')))
            case uniHead `geq` uniF of
                Nothing   -> wrongType
                Just Refl -> pure res


            -- ReadSomeValueN res uniHead <-
            --     matchUniRunTypeApp
            --         uni
            --         wrongType
            --         (\uniTypeApp ->
            --             cifoldM_SList @_ @(KnownTypeAst uni) @reps
            --                 Proxy
            --                 (ReadSomeValueN (SomeValueRes uni xs) uniTypeApp)
            --                 (\(ReadSomeValueN acc uniApp) ->
            --                     matchUniApply
            --                         uniApp
            --                         wrongType
            --                         (\uniApp' uniA ->
            --                             pure $ ReadSomeValueN (SomeValueArg uniA acc) uniApp')))
            -- case uniHead `geq` uniF of
            --     Nothing   -> wrongType
            --     Just Refl -> pure res


--                             (ReadSomeValueN $ \res uniHead ->
--                     in undefined) -- unReadSomeValueN go $ SomeValueRes uni xs)



                -- (let go = cfoldr_SList
                --             (Proxy @(All (KnownTypeAst uni) reps))
                --             _
                --             (_ (SomeValueRes uni xs))
                --     in unReadSomeValueN go)
                --     --         (\_ (ReadSomeValueN r) -> ReadSomeValueN $ \res uniApp ->
                --     --             matchUniApply
                --     --                 uniApp
                --     --                 wrongType
                --     --                 (\uniApp' uniA -> _ res)) -- r (SomeValueArg uniA res) uniApp'))
                --     --         (ReadSomeValueN $ \res uniHead ->
                --     --             case uniHead `geq` uniF of
                --     --                 Nothing   -> wrongType
                --     --                 Just Refl -> _ res)
                --     -- in unReadSomeValueN go $ SomeValueRes uni xs)

-- foldlVec :: forall p a m.
--             (forall n. a -> p n -> p (S n)) ->
--             p Z ->
--             Vec a m -> p m

-- foldr : ∀ {a b} {A : Set a} (B : ℕ → Set b) {m} →
--         (∀ {n} → A → B n → B (suc n)) →
--         B zero →
--         Vec A m → B m

-- foldl : ∀ {a b} {A : Set a} (B : ℕ → Set b) {m} →
--         (∀ {n} → B n → A → B (suc n)) →
--         B zero →
--         Vec A m → B m

-- newtype ReadSomeValueN reps0 m uni f reps = ReadSomeValueN
--     { unReadSomeValueN
--         :: forall k (a :: k). uni (TypeApp a) -> m (SomeValueN uni f reps)
--     }

-- newtype ReadSomeValueN m uni f = ReadSomeValueN
--     { unReadSomeValueN
--         :: forall k (a :: k). SomeValueN uni a -> uni (TypeApp a) -> m (SomeValueN uni f)
--     }


data ReadSomeValueN m uni f reps =
    forall k (a :: k). ReadSomeValueN (SomeValueN uni a reps) (uni (TypeApp a))

toTyNameAst
    :: forall text uniq. (KnownSymbol text, KnownNat uniq)
    => Proxy ('TyNameRep text uniq) -> TyName
toTyNameAst _ =
    TyName $ Name
        (Text.pack $ symbolVal @text Proxy)
        (Unique . fromIntegral $ natVal @uniq Proxy)

instance (KnownSymbol text, KnownNat uniq) =>
            KnownTypeAst uni (TyVarRep ('TyNameRep text uniq)) where
    toTypeAst _ = TyVar () . toTyNameAst $ Proxy @('TyNameRep text uniq)

instance (KnownTypeAst uni fun, KnownTypeAst uni arg) => KnownTypeAst uni (TyAppRep fun arg) where
    toTypeAst _ = TyApp () (toTypeAst $ Proxy @fun) (toTypeAst $ Proxy @arg)

instance (KnownSymbol text, KnownNat uniq, KnownKind kind, KnownTypeAst uni a) =>
            KnownTypeAst uni (TyForallRep ('TyNameRep @kind text uniq) a) where
    toTypeAst _ =
        TyForall ()
            (toTyNameAst $ Proxy @('TyNameRep text uniq))
            (knownKind $ Proxy @kind)
            (toTypeAst $ Proxy @a)

instance KnownTypeAst uni rep => KnownTypeAst uni (Opaque term rep) where
    toTypeAst _ = toTypeAst $ Proxy @rep

instance (term ~ term', KnownTypeAst (UniOf term) rep) => KnownType term (Opaque term' rep) where
    makeKnown = pure . unOpaque
    readKnown = pure . Opaque

instance uni `Includes` Integer       => KnownTypeAst uni Integer       where
    toTypeAst = toBuiltinTypeAst
instance uni `Includes` BS.ByteString => KnownTypeAst uni BS.ByteString where
    toTypeAst = toBuiltinTypeAst
instance uni `Includes` Char          => KnownTypeAst uni Char          where
    toTypeAst = toBuiltinTypeAst
instance uni `Includes` ()            => KnownTypeAst uni ()            where
    toTypeAst = toBuiltinTypeAst
instance uni `Includes` Bool          => KnownTypeAst uni Bool          where
    toTypeAst = toBuiltinTypeAst
instance uni `Includes` [a]           => KnownTypeAst uni [a]           where
    toTypeAst = toBuiltinTypeAst
instance uni `Includes` (a, b)        => KnownTypeAst uni (a, b)        where
    toTypeAst = toBuiltinTypeAst

instance KnownBuiltinType term Integer       => KnownType term Integer
instance KnownBuiltinType term BS.ByteString => KnownType term BS.ByteString
instance KnownBuiltinType term Char          => KnownType term Char
instance KnownBuiltinType term ()            => KnownType term ()
instance KnownBuiltinType term Bool          => KnownType term Bool
instance KnownBuiltinType term [a]           => KnownType term [a]
instance KnownBuiltinType term (a, b)        => KnownType term (a, b)

{- Note [Int as Integer]
We represent 'Int' as 'Integer' in PLC and check that an 'Integer' fits into 'Int' when
unlifting constants fo type 'Int' and fail with an evaluation failure (via 'AsEvaluationFailure')
if it doesn't. We couldn't fail via 'AsUnliftingError', because an out-of-bounds error is not an
internal one -- it's a normal evaluation failure, but unlifting errors have this connotation of
being "internal".
-}

instance uni `Includes` Integer => KnownTypeAst uni Int where
    toTypeAst _ = toTypeAst $ Proxy @Integer

-- See Note [Int as Integer].
instance KnownBuiltinType term Integer => KnownType term Int where
    makeKnown = makeKnown . toInteger
    readKnown term = do
        i :: Integer <- readKnown term
        unless (fromIntegral (minBound :: Int) <= i && i <= fromIntegral (maxBound :: Int)) $
            throwingWithCause _EvaluationFailure () $ Just term
        pure $ fromIntegral i
