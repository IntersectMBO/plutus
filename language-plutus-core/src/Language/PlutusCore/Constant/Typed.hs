-- | This module assigns types to built-ins.
-- See the @plutus/language-plutus-core/docs/Constant application.md@
-- article for how this emerged.

{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DerivingVia               #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeApplications          #-}

module Language.PlutusCore.Constant.Typed
    ( BuiltinStatic (..)
    , TypedBuiltinStatic (..)
    , TypedBuiltin (..)
    , TypedBuiltinValue (..)
    , TypeScheme (..)
    , TypedBuiltinName (..)
    , DynamicBuiltinNameMeaning (..)
    , DynamicBuiltinNameDefinition (..)
    , DynamicBuiltinNameMeanings (..)
    , Evaluator
    , EvaluateT (..)
    , ReflectT (..)
    , KnownDynamicBuiltinType (..)
    , OpaqueTerm (..)
    , thoist
    , eraseTypedBuiltinStatic
    , runEvaluateT
    , withEvaluator
    , runReflectT
    , mapReflectT
    , mapDeepReflectT
    , makeReflectT
    , makeRightReflectT
    , readDynamicBuiltinM
    ) where

import           Language.PlutusCore.Constant.Dynamic.Pretty
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Control.Monad.Except
import           Control.Monad.Morph                         as Morph
import           Control.Monad.Reader
import           Control.Monad.Trans.Inner
import qualified Data.ByteString.Lazy.Char8                  as BSL
import           Data.Map                                    (Map)
import           Data.Proxy
import           Data.Text                                   (Text)
import qualified Data.Text                                   as Text
import           Control.Monad.Trans.Compose                 (ComposeT (..))
import           GHC.TypeLits

infixr 9 `TypeSchemeArrow`

-- | Static built-in types.
data BuiltinStatic
    = BuiltinStaticInt
    | BuiltinStaticBS
    deriving (Show, Eq)

-- | Static built-in types along with their denotation.
data TypedBuiltinStatic a where
    TypedBuiltinStaticInt  :: TypedBuiltinStatic Integer
    TypedBuiltinStaticBS   :: TypedBuiltinStatic BSL.ByteString

-- | Built-in types. A type is considired "built-in" if it can appear in the type signature
-- of a primitive operation. So @boolean@ is considered built-in even though it is defined in PLC
-- and is not primitive.
data TypedBuiltin a where
    TypedBuiltinStatic :: TypedBuiltinStatic a -> TypedBuiltin a
    -- Any type that implements 'KnownDynamicBuiltinType' can be lifted to a 'TypedBuiltin',
    -- because any such type has a PLC representation and provides conversions back and forth
    -- between Haskell and PLC and that's all we need.
    TypedBuiltinDyn   :: KnownDynamicBuiltinType dyn => TypedBuiltin dyn

-- | A 'TypedBuiltin' packaged together with a value of the type that the 'TypedBuiltin' denotes.
data TypedBuiltinValue a = TypedBuiltinValue (TypedBuiltin a) a

-- | Type schemes of primitive operations.
-- @a@ is the Haskell denotation of a PLC type represented as a 'TypeScheme'.
-- @r@ is the resulting type in @a@, e.g. the resulting type in
-- @ByteString -> Size -> Integer@ is @Integer@.
data TypeScheme a r where
    TypeSchemeBuiltin :: TypedBuiltin a -> TypeScheme a a
    TypeSchemeArrow   :: TypeScheme a q -> TypeScheme b r -> TypeScheme (a -> b) r
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
           -- 'TypeSchemeBuiltin' expects. Type-level binding is only needed when you want to apply
           -- a type constructor to the variable, like in
           --
           -- > reverse : all a. list a -> list a
        -> (forall ot. ot ~ OpaqueTerm text uniq => TypedBuiltin ot -> TypeScheme a r)
        -> TypeScheme a r

    -- The @r@ is rather ad hoc and needed only for tests.
    -- We could use type families to compute it instead of storing as an index.
    -- That's a TODO perhaps.

-- | A 'BuiltinName' with an associated 'TypeScheme'.
data TypedBuiltinName a r = TypedBuiltinName BuiltinName (TypeScheme a r)
-- I attempted to unify various typed things, but sometimes type variables must be universally
-- quantified, sometimes they must be existentially quatified. And those are distinct type variables.

-- | Convert a 'TypedBuiltinStatic' to its untyped counterpart.
eraseTypedBuiltinStatic :: TypedBuiltinStatic a -> BuiltinStatic
eraseTypedBuiltinStatic TypedBuiltinStaticInt = BuiltinStaticInt
eraseTypedBuiltinStatic TypedBuiltinStaticBS  = BuiltinStaticBS

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

-- | The meaning of a dynamic built-in name consists of its 'Type' represented as a 'TypeScheme'
-- and its Haskell denotation.
data DynamicBuiltinNameMeaning =
    forall a r. DynamicBuiltinNameMeaning (TypeScheme a r) a
-- See the [DynamicBuiltinNameMeaning] note.

-- | The definition of a dynamic built-in consists of its name and meaning.
data DynamicBuiltinNameDefinition =
    DynamicBuiltinNameDefinition DynamicBuiltinName DynamicBuiltinNameMeaning

-- | Mapping from 'DynamicBuiltinName's to their 'DynamicBuiltinNameMeaning's.
newtype DynamicBuiltinNameMeanings = DynamicBuiltinNameMeanings
    { unDynamicBuiltinNameMeanings :: Map DynamicBuiltinName DynamicBuiltinNameMeaning
    } deriving (Semigroup, Monoid)

-- | A thing that evaluates @f@ in monad @m@ and allows to extend the set of
-- dynamic built-in names.
type Evaluator f m = DynamicBuiltinNameMeanings -> f TyName Name () -> m EvaluationResultDef

-- | A computation that runs in @t m@ and has access to an 'Evaluator' that runs in @m@.
-- The idea is that a computation that requires access to an evaluator may introduce new effects
-- even though the underlying evaluator does not have them.
--
-- For example reading of values (see 'readDynamicBuiltinM') runs in 'EvaluateT'
-- (because it needs access to an evaluator) and adds the 'ReflectT' effect on top of that
-- (see the docs of 'ReflectT' for what effects it consists of).
--
-- 'EvaluateT' is a monad transformer transfomer. I.e. it turns one monad transformer
-- into another one.
newtype EvaluateT t m a = EvaluateT
    { unEvaluateT :: ReaderT (Evaluator Term m) (t m) a
    } deriving
        ( Functor, Applicative, Monad, Alternative, MonadPlus
        , MonadReader (Evaluator Term m)
        , MonadError e
        )

-- | Run an 'EvaluateT' computation using the given 'Evaluator'.
runEvaluateT :: Evaluator Term m -> EvaluateT t m a -> t m a
runEvaluateT eval (EvaluateT a) = runReaderT a eval

-- | Wrap a computation binding an 'Evaluator' as a 'EvaluateT'.
withEvaluator :: (Evaluator Term m -> t m a) -> EvaluateT t m a
withEvaluator = EvaluateT . ReaderT

-- | 'thoist' for monad transformer transformers is what 'hoist' for monad transformers.
thoist :: Monad (t m) => (forall b. t m b -> s m b) -> EvaluateT t m a -> EvaluateT s m a
thoist f (EvaluateT a) = EvaluateT $ Morph.hoist f a

{- Note [Semantics of dynamic built-in types]
We only allow dynamic built-in types that

1. can be represented using static types in PLC. For example Haskell's 'Char' can be represented as
@integer 4@ in PLC. This restriction makes the dynamic built-in types machinery somewhat similar to
type aliases in Haskell (defined via the @type@ keyword). The reason for this restriction is that
storing values of arbitrary types of a host language in the AST of a target language is commonly far
from being trivial, hence we do not support this right now, but we plan to figure out a way to allow
such extensions to the AST
2. are of kind @*@. Dynamic built-in types that are not of kind @*@ can be encoded via recursive
instances. For example:

    instance KnownDynamicBuiltinType dyn => KnownDynamicBuiltinType [dyn] where
        ...

This is due to the fact that we use Haskell classes to assign semantics to dynamic built-in types and
since it's anyway impossible to assign a meaning to an open PLC type, because you'd have to somehow
interpret free variables, we're only interested in closed PLC types and those can be handled by
recursive instances as shown above.

Since type classes are globally coherent by design, we also have global coherence for dynamic built-in
types for free. Any dynamic built-in type means the same thing regardless of the blockchain it's
added to. It may prove to be restrictive, but it's a good property to start with, because less things
can silently stab you in the back.

An @KnownDynamicBuiltinType dyn@ instance provides

1. a way to encode @dyn@ as a PLC type ('getTypeEncoding')
2. a function that encodes values of type @dyn@ as PLC terms ('makeDynamicBuiltin')
3. a function that decodes PLC terms back to Haskell values ('readDynamicBuiltin')

The last two are ought to constitute an isomorphism (modulo 'Maybe').
-}

{- Note [Converting PLC values to Haskell values]
The first thought that comes to mind when you asked to convert a PLC value to the corresponding Haskell
value is "just match on the AST". This works nicely for simple things like 'Char's which we encode as
@integer@s, see the @KnownDynamicBuiltinType Char@ instance below.

But how to convert something more complicated like lists? A PLC list gets passed as argument to
a built-in after it gets evaluated to WHNF. We can't just match on the AST here, because after
the initial lambda it can be anything there: function applications, other built-ins, recursive data,
anything. "Well, just normalize it" -- not so fast: for one, we did not have a term normalization
procedure at the moment this note was written, for two, it's not something that can be easily done,
because you have to carefully handle uniques (we generate new terms during evaluation) and perform type
substitutions, because types must be preserved.

Besides, matching on the AST becomes really complicated: you have to ensure that a term does have
an expected semantics by looking at the term's syntax. Huge pattern matches followed by multiple
checks that variables have equal names in right places and have distinct names otherwise. Making a
mistake is absolutely trivial here. Of course, one could just omit checks and hope it'll work alright,
but eventually it'll break and debugging won't be fun at all.

So instead of dealing with syntax of terms, we deal with their semantics. Namely, we evaluate terms
using some evaluator (normally, the CEK machine). For the temporary lack of ability to put values of
arbitrary Haskell types into the Plutus Core AST, we convert PLC values to Haskell values and "emit"
the latter via a combination of 'unsafePerformIO' and 'IORef'. For example, we fold a PLC list with
a dynamic built-in name (called `emit`) that calls 'unsafePerformIO' over a Haskell function that
appends an element to the list stored in an 'IORef':

    plcListToHaskellList list =
        evaluateCek anEnvironment (foldList {dyn} {unit} (\(r : unit) -> emit) unitval list)

After evaluation finishes, we read a Haskell list from the 'IORef'
(which requires another 'unsafePerformIO') and return it.
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

    type Evaluator f = DynamicBuiltinNameMeanings -> f TyName Name () -> EvaluationResult

so @Evaluator Term@ receives a map with meanings of dynamic built-in names which extends the map the
evaluator already has (this is needed, because we add new dynamic built-in names during conversion of
PLC values to Haskell values, see Note [Converting PLC values to Haskell values]), a 'Term' to evaluate
and returns an 'EvaluationResult' (we may want to later add handling of errors here). Thus, whenever
we want to resume evaluation during computation of a dynamic built-in application, we just call the
received evaluator

(3) seems best, so it's what is implemented.
-}

-- | The monad in which we convert PLC terms to Haskell values.
-- Conversion can fail with
--
-- 1. 'EvaluationFailure' if at some point constants stop fitting into specified sizes.
-- 2. A textual error if a PLC term can't be converted to a Haskell value of a specified type.
newtype ReflectT m a = ReflectT
    { unReflectT :: ExceptT Text (InnerT EvaluationResult m) a
    } deriving
        ( Functor, Applicative, Monad
        , MonadError Text
        )
      deriving MonadTrans via ComposeT (ExceptT Text) (InnerT EvaluationResult)

-- Uses the 'Alternative' instance of 'EvaluationResult'.
instance Monad m => Alternative (ReflectT m) where
    empty = ReflectT . lift $ yield empty
    ReflectT (ExceptT (InnerT m)) <|> ReflectT (ExceptT (InnerT n)) =
        ReflectT . ExceptT . InnerT $ (<|>) <$> m <*> n

-- | Run a 'ReflectT' computation.
runReflectT :: ReflectT m a -> m (EvaluationResult (Either Text a))
runReflectT = unInnerT . runExceptT . unReflectT

-- | Map over the underlying representation of 'ReflectT'.
mapReflectT
    :: (ExceptT Text (InnerT EvaluationResult m) a -> ExceptT Text (InnerT EvaluationResult n) b)
    -> ReflectT m a
    -> ReflectT n b
mapReflectT f (ReflectT a) = ReflectT (f a)

-- | Map over the fully unwrapped underlying representation of a 'ReflectT' computation.
mapDeepReflectT
    :: (m (EvaluationResult (Either Text a)) -> n (EvaluationResult (Either Text b)))
    -> ReflectT m a
    -> ReflectT n b
mapDeepReflectT = mapReflectT . mapExceptT . mapInnerT

-- | Fully wrap a computation into 'ReflectT'.
makeReflectT :: m (EvaluationResult (Either Text a)) -> ReflectT m a
makeReflectT = ReflectT . ExceptT . InnerT

-- | Wrap a non-throwing computation into 'ReflectT'.
makeRightReflectT :: Monad m => m (EvaluationResult a) -> ReflectT m a
makeRightReflectT = ReflectT . lift . InnerT

-- See Note [Semantics of dynamic built-in types].
-- See Note [Converting PLC values to Haskell values].
-- Types and terms are supposed to be closed, hence no 'Quote'.
-- | Haskell types known to exist on the PLC side.
class KnownDynamicBuiltinType dyn where
    -- | The type representing @dyn@ used on the PLC side.
    toTypeEncoding :: proxy dyn -> Type TyName ()

    -- | Convert a Haskell value to the corresponding PLC value.
    -- 'Nothing' represents a conversion failure.
    makeDynamicBuiltin :: dyn -> Maybe (Term TyName Name ())

    -- See Note [Evaluators].
    -- | Convert a PLC value to the corresponding Haskell value using an explicit evaluator.
    readDynamicBuiltin :: Monad m => Evaluator Term m -> Term TyName Name () -> ReflectT m dyn

-- | Convert a PLC value to the corresponding Haskell value using the evaluator
-- from the current context.
readDynamicBuiltinM
    :: (Monad m, KnownDynamicBuiltinType a)
    => Term TyName Name () -> EvaluateT ReflectT m a
readDynamicBuiltinM term = withEvaluator $ \eval -> readDynamicBuiltin eval term

-- | The denotation of a term whose type is a bound variable.
-- I.e. the denotation of such a term is the term itself.
-- This is because we have parametricity in Haskell, so we can't inspect a value whose
-- type is a bound variable, so we never need to convert such a term from Plutus Core to Haskell
-- and back and instead can keep it intact.
newtype OpaqueTerm (text :: Symbol) (unique :: Nat) = OpaqueTerm
    { unOpaqueTerm :: Term TyName Name ()
    }

instance Pretty BuiltinStatic where
    pretty BuiltinStaticInt = "integer"
    pretty BuiltinStaticBS  = "bytestring"

instance Pretty (TypedBuiltinStatic a) where
    pretty = pretty . eraseTypedBuiltinStatic

instance Pretty (TypedBuiltin a) where
    pretty (TypedBuiltinStatic tbs) = parens $ pretty tbs
    -- TODO: do we want this entire thing to be 'PrettyBy' rather than 'Pretty'?
    -- This is just used in errors, so we probably do not care much.
    pretty dyn@TypedBuiltinDyn      = prettyPlcDef $ toTypeEncoding dyn

instance (PrettyDynamic a) => Pretty (TypedBuiltinValue a) where
    pretty (TypedBuiltinValue (TypedBuiltinStatic _) x)   = prettyDynamic x
    pretty (TypedBuiltinValue TypedBuiltinDyn          x) = prettyDynamic x

-- Encode '()' from Haskell as @all r. r -> r@ from PLC.
-- This is a very special instance, because it's used to define functions that are needed for
-- other instances, so we keep it here.
instance KnownDynamicBuiltinType () where
    toTypeEncoding _ = unit

    -- We need this matching, because otherwise Haskell expressions are thrown away rather than being
    -- evaluated and we use 'unsafePerformIO' in multiple places, so we want to compute the '()' just
    -- for side effects that the evaluation may cause.
    makeDynamicBuiltin () = pure unitval

    readDynamicBuiltin eval term = do
        let int = TyBuiltin () TyInteger
            asInt = Constant () . BuiltinInt ()
        res <- makeRightReflectT . eval mempty . Apply () (TyInst () term int) $ asInt 1
        case res of
            Constant () (BuiltinInt () 1) -> pure ()
            _                             -> throwError "Not a builtin ()"

instance (KnownSymbol text, KnownNat uniq) =>
        KnownDynamicBuiltinType (OpaqueTerm text uniq) where
    toTypeEncoding _ =
        TyVar () . TyName $
            Name ()
                (Text.pack $ symbolVal @text Proxy)
                (Unique . fromIntegral $ natVal @uniq Proxy)

    makeDynamicBuiltin = pure . unOpaqueTerm

    readDynamicBuiltin eval = fmap OpaqueTerm . makeRightReflectT . eval mempty
