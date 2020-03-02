-- | This module assigns types to built-ins.
-- See the @plutus/language-plutus-core/docs/Constant application.md@
-- article for how this emerged.

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Constant.Typed
    ( TypeScheme (..)
    , TypedBuiltinName (..)
    , FoldArgs
    , DynamicBuiltinNameMeaning (..)
    , DynamicBuiltinNameDefinition (..)
    , DynamicBuiltinNameMeanings (..)
    , AnEvaluator
    , Evaluator
    , EvaluateT (..)
    , runEvaluateT
    , withEvaluator
    , KnownType (..)
    , OpaqueTerm (..)
    , readKnownM
    , readKnownBy
    , unliftConstant
    , unliftConstantEval
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.Universe

import           Control.Monad.Except
import           Control.Monad.Reader
import qualified Data.Kind                                          as GHC (Type)
import           Data.Map                                           (Map)
import           Data.Proxy
import           Data.String
import           GHC.TypeLits

infixr 9 `TypeSchemeArrow`

-- | Type schemes of primitive operations.
-- @as@ is a list of types of arguments, @r@ is the resulting type.
-- E.g. @Char -> Bool -> Integer@ is encoded as @TypeScheme uni [Char, Bool] Integer@.
data TypeScheme uni (args :: [GHC.Type]) res where
    TypeSchemeResult
        :: KnownType uni res => Proxy res -> TypeScheme uni '[] res
    TypeSchemeArrow
        :: KnownType uni arg
        => Proxy arg -> TypeScheme uni args res -> TypeScheme uni (arg ': args) res
    TypeSchemeAllType
        :: (KnownSymbol text, KnownNat uniq)
           -- Here we require the user to manually provide the unique of a type variable.
           -- That's nothing but silly, but I do not see what else we can do with the current design.
           -- Once the 'BuiltinPipe' thing gets implemented, we'll be able to bind 'uniq' inside
           -- the continuation and also put there the @KnownNat uniq@ constraint
           -- (i.e. use universal quantification for uniques) and that should work alright.
        => Proxy '(text, uniq)
           -- We use a funny trick here: instead of binding
           --
           -- > TypedBuiltin (OpaqueTerm text uniq)
           --
           -- directly we introduce an additional and "redundant" type variable. The reason why we
           -- do that is because this way we can also bind such a variable later when constructing
           -- the 'TypeScheme' of a polymorphic builtin, so that for the user this looks exactly
           -- like a single bound type variable instead of this weird @OpaqueTerm text uniq@ thing.
           --
           -- And note that in most cases we do not need to bind anything at the type level and can
           -- use the variable bound at the term level directly, because it's of the type that
           -- 'TypeSchemeResult' expects. Type-level binding is only needed when you want to apply
           -- a type constructor to the variable, like in
           --
           -- > reverse : all a. list a -> list a
        -> (forall ot. ot ~ OpaqueTerm uni text uniq => Proxy ot -> TypeScheme uni args res)
        -> TypeScheme uni args res

-- | A 'BuiltinName' with an associated 'TypeScheme'.
data TypedBuiltinName uni args res = TypedBuiltinName BuiltinName (TypeScheme uni args res)

-- | Turn a list of Haskell types @as@ into a functional type ending in @r@.
--
-- >>> :set -XDataKinds
-- >>> :kind! FoldArgs [Char, Bool] Integer
-- FoldArgs [Char, Bool] Integer :: *
-- = Char -> Bool -> Integer
type family FoldArgs args r where
    FoldArgs '[]           res = res
    FoldArgs (arg ': args) res = arg -> FoldArgs args res

{- Note [DynamicBuiltinNameMeaning]
We represent the meaning of a 'DynamicBuiltinName' as a 'TypeScheme' and a Haskell denotation.
We need both while evaluting a 'DynamicBuiltinName', because 'TypeScheme' is required for
well-typedness to avoid using 'unsafeCoerce' and similar junk, while the denotation is what
actually computes. We do not need denotations for type checking, nor strongly typed 'TypeScheme'
is required, however analogously to static built-ins, we compute the types of dynamic built-ins from
their 'TypeScheme's. This way we only define a 'TypeScheme', which we anyway need, and then compute
the corresponding 'Type' from it. And we can't go the other way around -- from untyped to typed --
of course. Therefore a typed thing has to go before the corresponding untyped thing and in the
final pipeline one has to supply a 'DynamicBuiltinNameMeaning' for each of the 'DynamicBuiltinName's.
-}

-- See Note [DynamicBuiltinNameMeaning].
-- | The meaning of a dynamic built-in name consists of its 'Type' represented as a 'TypeScheme'
-- and its Haskell denotation.
data DynamicBuiltinNameMeaning uni =
    forall args res. DynamicBuiltinNameMeaning
        (TypeScheme uni args res)
        (FoldArgs args res)
        (FoldArgs args ExBudget)

-- | The definition of a dynamic built-in consists of its name and meaning.
data DynamicBuiltinNameDefinition uni =
    DynamicBuiltinNameDefinition DynamicBuiltinName (DynamicBuiltinNameMeaning uni)

-- | Mapping from 'DynamicBuiltinName's to their 'DynamicBuiltinNameMeaning's.
newtype DynamicBuiltinNameMeanings uni = DynamicBuiltinNameMeanings
    { unDynamicBuiltinNameMeanings :: Map DynamicBuiltinName (DynamicBuiltinNameMeaning uni)
    } deriving (Semigroup, Monoid)

-- | A thing that evaluates @f@ in monad @m@, returns an @a@ and allows to extend the set of
-- dynamic built-in names.
type AnEvaluator f uni m a = DynamicBuiltinNameMeanings uni -> f TyName Name uni () -> m a

-- | A thing that evaluates @f@ in monad @m@ and allows to extend the set of
-- dynamic built-in names.
type Evaluator f uni m = AnEvaluator f uni m (Term TyName Name uni ())

-- | A computation that runs in @m@ and has access to an 'Evaluator' that runs in @m@.
newtype EvaluateT uni m a = EvaluateT
    { unEvaluateT :: ReaderT (Evaluator Term uni m) m a
    } deriving
        ( Functor, Applicative, Monad
        , MonadReader (Evaluator Term uni m)
        , MonadError e
        )

instance MonadTrans (EvaluateT uni) where
    lift m = EvaluateT $ lift m

-- | Run an 'EvaluateT' computation using the given 'Evaluator'.
runEvaluateT :: Evaluator Term uni m -> EvaluateT uni m a -> m a
runEvaluateT eval (EvaluateT a) = runReaderT a eval

-- | Wrap a computation binding an 'Evaluator' as a 'EvaluateT'.
withEvaluator :: (Evaluator Term uni m -> m a) -> EvaluateT uni m a
withEvaluator = EvaluateT . ReaderT

{- Note [Semantics of dynamic built-in types]
We only allow dynamic built-in types that

1. can be represented using static types in PLC. For example Haskell's 'Char' can be represented as
@integer@ in PLC. This restriction makes the dynamic built-in types machinery somewhat similar to
type aliases in Haskell (defined via the @type@ keyword). The reason for this restriction is that
storing values of arbitrary types of a host language in the AST of a target language is commonly far
from being trivial, hence we do not support this right now, but we plan to figure out a way to allow
such extensions to the AST
2. are of kind @*@. Dynamic built-in types that are not of kind @*@ can be encoded via recursive
instances. For example:

    instance KnownType uni a => KnownType uni [a] where
        ...

The meaning of a free type variable is 'OpaqueTerm'.

This is due to the fact that we use Haskell classes to assign semantics to dynamic built-in types and
since it's anyway impossible to assign a meaning to an open PLC type, because you'd have to somehow
interpret free variables, we're only interested in closed PLC types and those can be handled by
recursive instances as shown above.

Since type classes are globally coherent by design, we also have global coherence for dynamic built-in
types for free. Any dynamic built-in type means the same thing regardless of the blockchain it's
added to. It may prove to be restrictive, but it's a good property to start with, because less things
can silently stab you in the back.

An @KnownType a@ instance provides

1. a way to encode @a@ as a PLC type ('toTypeAst')
2. a function that encodes values of type @a@ as PLC terms ('makeKnown')
3. a function that decodes PLC terms back to Haskell values ('readKnown')

The last two are ought to constitute an isomorphism.
-}

{- Note [Converting PLC values to Haskell values]
The first thought that comes to mind when you asked to convert a PLC value to the corresponding Haskell
value is "just match on the AST". This works nicely for simple things like 'Char's which we encode as
@integer@s, see the @KnownType Char@ instance.

But how to convert something more complicated like lists? A PLC list gets passed as argument to
a built-in after it gets evaluated to WHNF. We can't just match on the AST here, because after
the initial lambda it can be anything there: function applications, other built-ins, recursive data,
anything. "Well, just normalize it" -- not so fast: for one, we did not have a term normalization
procedure at the moment this note was written, for two, it's not something that can be easily done,
because you have to carefully handle uniques (we generate new terms during evaluation) and perform
type substitutions, because types must be preserved.

Besides, matching on the AST becomes really complicated: you have to ensure that a term does have
an expected semantics by looking at the term's syntax. Huge pattern matches followed by multiple
checks that variables have equal names in right places and have distinct names otherwise. Making a
mistake is absolutely trivial here. Of course, one could just omit checks and hope it'll work alright,
but eventually it'll break and debugging won't be fun at all.

So instead of dealing with syntax of terms, we deal with their semantics. Namely, we evaluate terms
using some evaluator (normally, the CEK machine). For the temporary lack of ability to put values of
arbitrary Haskell types into the Plutus Core AST, we have some ad hoc strategies for converting PLC
values to Haskell values (ground, product, sum and recursive types are all handled distinctly,
see the "Language.PlutusCore.Constant.Dynamic.Instances" module).
-}

{- Note [Evaluators]
A dynamic built-in name can be applied to something that contains uninstantiated variables. There are
several possible ways to handle that:

1. each evaluator is required to perform substitutions to instantiate all variables in arguments to
built-ins. The drawback is that this can be inefficient in cases when there are many applications of
built-ins and arguments are of non-primitive types. Besides, substitution is tricky and is trivial to
screw up
2. we can break encapsulation and pass environments to the built-ins application machinery, so that it
knows how to instantiate variables. This would work for the strict CEK machine, but the lazy
CEK machine also has a heap and there can be other evaluators that have their internal state that
can't just be thrown away and it's impossible for the built-ins application machinery to handle states
of all possible evaluators beforehand
3. or we can just require to pass the current evaluator with its encapsulated state to functions that
evaluate built-in applications. The type of evaluators is this then:

    type Evaluator f m = DynamicBuiltinNameMeanings -> f TyName Name () -> m EvaluationResult

so @Evaluator Term m@ receives a map with meanings of dynamic built-in names which extends the map the
evaluator already has (this is needed, because we may add new dynamic built-in names during conversion
of PLC values to Haskell values), a 'Term' to evaluate and returns an @m EvaluationResult@.
Thus, whenever we want to resume evaluation during computation of a dynamic built-in application,
we just call the received evaluator

(3) seems best, so it's what is implemented.
-}

-- See Note [Semantics of dynamic built-in types].
-- See Note [Converting PLC values to Haskell values].
-- | Haskell types known to exist on the PLC side.
class KnownType uni a where
    -- | The type representing @a@ used on the PLC side.
    toTypeAst :: proxy a -> Type TyName uni ()

    -- | Convert a Haskell value to the corresponding PLC term.
    makeKnown :: a -> Term TyName Name uni ()

    -- See Note [Evaluators].
    -- | Convert a PLC term to the corresponding Haskell value using an explicit evaluator.
    readKnown
        :: (MonadError (ErrorWithCause uni err) m, AsUnliftingError err)
        => Evaluator Term uni m -> Term TyName Name uni () -> m a

-- | Convert a PLC term to the corresponding Haskell value using the evaluator
-- from the current context.
readKnownM
    :: (MonadError (ErrorWithCause uni err) m, AsUnliftingError err, KnownType uni a)
    => Term TyName Name uni () -> EvaluateT uni m a
readKnownM term = withEvaluator $ \eval -> readKnown eval term

-- | Convert a PLC term to the corresponding Haskell value using an explicit evaluator
-- extended with a provided set of built-in name meanings.
readKnownBy
    :: (MonadError (ErrorWithCause uni err) m, AsUnliftingError err, KnownType uni a)
    => Evaluator Term uni m -> DynamicBuiltinNameMeanings uni -> Term TyName Name uni () -> m a
readKnownBy eval means = readKnown $ eval . mappend means

{- Note [The reverse example]
Having a dynamic built-in with the following signature:

    reverse : all a. list a -> list a

that maps to Haskell's

    reverse :: forall a. [a] -> [a]

evaluation of

    PLC.reverse {bool} (cons true (cons false nil))

proceeds as follows:

      PLC.reverse {bool} (cons true (cons false nil))
    ~ makeKnown (Haskell.reverse (readKnown (cons true (cons false nil))))
    ~ makeKnown (Haskell.reverse [OpaqueTerm true, OpaqueTerm false])
    ~ makeKnown [OpaqueTerm false, OpaqueTerm true]
    ~ cons false (cons true nil)

Note how we use 'OpaqueTerm' in order to wrap a PLC term as a Haskell value using 'readKnown' and
then unwrap the term back using 'makeKnown' without ever inspecting the term.
-}

-- See Note [The reverse example] for an example.
-- | The denotation of a term whose type is a bound variable.
-- I.e. the denotation of such a term is the term itself.
-- This is because we have parametricity in Haskell, so we can't inspect a value whose
-- type is a bound variable, so we never need to convert such a term from Plutus Core to Haskell
-- and back and instead can keep it intact.
newtype OpaqueTerm uni (text :: Symbol) (unique :: Nat) = OpaqueTerm
    { unOpaqueTerm :: Term TyName Name uni ()
    }

instance (GShow uni, Closed uni, uni `Everywhere` Pretty) =>
            Pretty (OpaqueTerm uni text unique) where
    pretty = pretty . unOpaqueTerm

-- | Extract the 'Constant' from a 'Term'
-- (or throw an error if the term is not a 'Constant' or
-- the constant is not of the expected type).
unliftConstant
    :: forall a m uni err.
       ( MonadError (ErrorWithCause uni err) m, AsUnliftingError err
       , GShow uni, GEq uni, uni `Includes` a
       )
    => Term TyName Name uni () -> m a
unliftConstant term = case term of
    Constant () (Some (ValueOf uniAct x)) -> do
        let uniExp = knownUni @uni @a
        case uniAct `geq` uniExp of
            Just Refl -> pure x
            Nothing   -> do
                let err = fromString $ concat
                        [ "Type mismatch: "
                        , "expected: " ++ gshow uniExp
                        , "actual: " ++ gshow uniAct
                        ]
                throwingWithCause _UnliftingError err $ Just term
    _ -> throwingWithCause _UnliftingError "Not a constant" $ Just term

-- | Evaluate a term using an evaluator and extract the resulting 'Constant'
-- (or throw an error if the result is not a 'Constant' or
-- the constant is not of the expected type).
unliftConstantEval
    :: forall a m uni err.
       ( MonadError (ErrorWithCause uni err) m, AsUnliftingError err
       , GShow uni, GEq uni, uni `Includes` a
       )
    => DynamicBuiltinNameMeanings uni -> Evaluator Term uni m -> Term TyName Name uni () -> m a
unliftConstantEval means eval = eval means >=> unliftConstant

-- Encode '()' from Haskell as @all r. r -> r@ from PLC.
-- This is a very special instance, because it's used to define functions that are needed for
-- other instances, so we keep it here.
instance (GShow uni, GEq uni, uni `Includes` Integer) => KnownType uni () where
    toTypeAst _ = unit

    -- We need this matching, because otherwise Haskell expressions are thrown away rather than being
    -- evaluated and we use 'unsafePerformIO' for logging, so we want to compute the '()' just
    -- for side effects that the evaluation may cause.
    makeKnown () = unitval

    readKnown eval term = do
        let integer = mkTyBuiltin @Integer ()
            termApp = Apply () (TyInst () term integer) $ mkConstant @Integer () 1
        i <- unliftConstantEval mempty eval termApp
        if i == (1 :: Integer)
            then pure ()
            else throwingWithCause _UnliftingError "Not an integer-encoded ()" $ Just term
