-- | This module assigns types to built-ins.
-- See the @plutus/language-plutus-core/docs/Constant application.md@
-- article for how this emerged.

{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeApplications          #-}

module Language.PlutusCore.Constant.Typed
    ( BuiltinSized (..)
    , TypedBuiltinSized (..)
    , SizeEntry (..)
    , BuiltinType (..)
    , TypedBuiltin (..)
    , TypedBuiltinValue (..)
    , TypeScheme (..)
    , TypedBuiltinName (..)
    , DynamicBuiltinNameMeaning (..)
    , DynamicBuiltinNameDefinition (..)
    , DynamicBuiltinNameMeanings (..)
    , Evaluator
    , Evaluate
    , Convert
    , KnownDynamicBuiltinType (..)
    , OpaqueTerm (..)
    , eraseTypedBuiltinSized
    , runEvaluate
    , withEvaluator
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
import           Control.Monad.Reader
import qualified Data.ByteString.Lazy.Char8                  as BSL
import           Data.Map                                    (Map)
import           Data.Proxy
import           Data.Text                                   (Text)
import qualified Data.Text                                   as Text
import           GHC.TypeLits

infixr 9 `TypeSchemeArrow`

-- | Built-in types indexed by @size@.
data BuiltinSized
    = BuiltinSizedInt
    | BuiltinSizedBS
    | BuiltinSizedSize
    deriving (Show, Eq)

-- | Built-in types indexed by @size@ along with their denotation.
data TypedBuiltinSized a where
    TypedBuiltinSizedInt  :: TypedBuiltinSized Integer
    TypedBuiltinSizedBS   :: TypedBuiltinSized BSL.ByteString
    -- See Note [Semantics of sizes].
    TypedBuiltinSizedSize :: TypedBuiltinSized ()

{- Note [Semantics of sizes]
We convert each PLC's @size s@ into Haskell's '()'. I.e. sizes are completely ignored in
the semantics of various built-ins. Hence the Haskell's type signature of PLC's 'resizeInteger' is

    () -> Integer -> Integer

while its PLC signature is

    forall s0 s1. size s1 -> integer s0 -> integer s1

This does not mean that we do not perform all the checks prescribed by the specification.
Merely that we can't compute using sizes on the Haskell side, e.g. we cannot assign a semantics to

    maxIntegerOfGivenSize : forall s. size s -> integer s

There are two reasons for that:

1. Clarity. We want to be clear that size checks are not handled by Haskell interpretations of
   Plutus Core built-ins -- they're handled separately (see the "Apply" module).
   The reason for that is that we do not basically care what an operation do w.r.t. to sizes,
   we only care whether something it returns fits into some expected size.
   And this last checking step can be performed uniformly for all currently presented built-ins.

2. The semantics of @integer s@ is 'Integer'. While this may look ok, we actually lose size information,
   so e.g. there is no meaningful way we could interpret

       sizeOfInteger : forall s. integer s -> size s

   with @size s@ being interpreted as 'Size', because in @Integer -> Size@ the size of the 'Integer'
   is not specified. And we can't compute it, because we want its actual runtime size rather than
   the minimal size it fits into, as the former can be larger than the latter.
   Hence the semantics we have is

       sizeOfIntegerMeaning :: Integer -> ()

   I.e. this doesn't do anything useful at all. But it's not supposed to,
   since it returns a size and sizes are handled separately as (1) describes.
-}

-- | Type-level sizes.
data SizeEntry size
    = SizeValue Size  -- ^ A constant size.
    | SizeBound size  -- ^ A bound size variable.
    deriving (Eq, Ord, Functor)
-- We write @SizeEntry Size@ sometimes, so this data type is not perfect, but it works fine.

-- | Built-in types.
data BuiltinType size
    = BuiltinSized (SizeEntry size) BuiltinSized

-- | Built-in types. A type is considired "built-in" if it can appear in the type signature
-- of a primitive operation. So @boolean@ is considered built-in even though it is defined in PLC
-- and is not primitive.
data TypedBuiltin size a where
    TypedBuiltinSized :: SizeEntry size -> TypedBuiltinSized a -> TypedBuiltin size a
    -- Any type that implements 'KnownDynamicBuiltinType' can be lifted to a 'TypedBuiltin',
    -- because any such type has a PLC representation and provides conversions back and forth
    -- between Haskell and PLC and that's all we need.
    TypedBuiltinDyn   :: KnownDynamicBuiltinType dyn => TypedBuiltin size dyn

-- | A 'TypedBuiltin' packaged together with a value of the type that the 'TypedBuiltin' denotes.
data TypedBuiltinValue size a = TypedBuiltinValue (TypedBuiltin size a) a

-- | Type schemes of primitive operations.
-- @a@ is the Haskell denotation of a PLC type represented as a 'TypeScheme'.
-- @r@ is the resulting type in @a@, e.g. the resulting type in
-- @ByteString -> Size -> Integer@ is @Integer@.
data TypeScheme size a r where
    TypeSchemeBuiltin :: TypedBuiltin size a -> TypeScheme size a a
    TypeSchemeArrow   :: TypeScheme size a q -> TypeScheme size b r -> TypeScheme size (a -> b) r
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
           -- > TypedBuiltin size (OpaqueTerm text uniq)
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
        -> (forall qt. qt ~ OpaqueTerm text uniq => TypedBuiltin size qt -> TypeScheme size a r)
        -> TypeScheme size a r
    TypeSchemeAllSize :: (size -> TypeScheme size a r) -> TypeScheme size a r

    -- The @r@ is rather ad hoc and needed only for tests.
    -- We could use type families to compute it instead of storing as an index.
    -- That's a TODO perhaps.

-- | A 'BuiltinName' with an associated 'TypeScheme'.
data TypedBuiltinName a r = TypedBuiltinName BuiltinName (forall size. TypeScheme size a r)
-- I attempted to unify various typed things, but sometimes type variables must be universally
-- quantified, sometimes they must be existentially quatified. And those are distinct type variables.

-- | Convert a 'TypedBuiltinSized' to its untyped counterpart.
eraseTypedBuiltinSized :: TypedBuiltinSized a -> BuiltinSized
eraseTypedBuiltinSized TypedBuiltinSizedInt  = BuiltinSizedInt
eraseTypedBuiltinSized TypedBuiltinSizedBS   = BuiltinSizedBS
eraseTypedBuiltinSized TypedBuiltinSizedSize = BuiltinSizedSize

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
    forall a r. DynamicBuiltinNameMeaning (forall size. TypeScheme size a r) a
-- See the [DynamicBuiltinNameMeaning] note.

-- | The definition of a dynamic built-in consists of its name and meaning.
data DynamicBuiltinNameDefinition =
    DynamicBuiltinNameDefinition DynamicBuiltinName DynamicBuiltinNameMeaning

-- | Mapping from 'DynamicBuiltinName's to their 'DynamicBuiltinNameMeaning's.
newtype DynamicBuiltinNameMeanings = DynamicBuiltinNameMeanings
    { unDynamicBuiltinNameMeanings :: Map DynamicBuiltinName DynamicBuiltinNameMeaning
    } deriving (Semigroup, Monoid)

type Evaluator f m = DynamicBuiltinNameMeanings -> f TyName Name () -> m EvaluationResultDef

type Evaluate m = ReaderT (Evaluator Term m) m

runEvaluate :: Evaluator Term m -> Evaluate m a -> m a
runEvaluate = flip runReaderT

withEvaluator :: (Evaluator Term m -> m a) -> Evaluate m a
withEvaluator = ReaderT

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
type Convert a = ExceptT Text EvaluationResult a

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
    -- | Convert a PLC value to the corresponding Haskell value.
    readDynamicBuiltin :: Monad m => Evaluator Term m -> Term TyName Name () -> m (Convert dyn)

readDynamicBuiltinM
    :: (Monad m, KnownDynamicBuiltinType dyn)
    => Term TyName Name () -> Evaluate m (Convert dyn)
readDynamicBuiltinM term = withEvaluator $ \eval -> readDynamicBuiltin eval term

-- | The denotation of a term whose type is a bound variable.
-- I.e. the denotation of such a term is the term itself.
-- This is because we have parametricity in Haskell, so we can't inspect a value whose
-- type is a bound variable, so we never need to convert such a term from Plutus Core to Haskell
-- and back and instead can keep it intact.
newtype OpaqueTerm (text :: Symbol) (unique :: Nat) = OpaqueTerm
    { unOpaqueTerm :: Term TyName Name ()
    }

instance Pretty BuiltinSized where
    pretty BuiltinSizedInt  = "integer"
    pretty BuiltinSizedBS   = "bytestring"
    pretty BuiltinSizedSize = "size"

instance Pretty (TypedBuiltinSized a) where
    pretty = pretty . eraseTypedBuiltinSized

instance Pretty size => Pretty (SizeEntry size) where
    pretty (SizeValue size) = pretty size
    pretty (SizeBound size) = pretty size

instance Pretty size => Pretty (TypedBuiltin size a) where
    pretty (TypedBuiltinSized se tbs) = parens $ pretty tbs <+> pretty se
    -- TODO: do we want this entire thing to be 'PrettyBy' rather than 'Pretty'?
    -- This is just used in errors, so we probably do not care much.
    pretty dyn@TypedBuiltinDyn        = prettyPlcDef $ toTypeEncoding dyn

instance (size ~ Size, PrettyDynamic a) => Pretty (TypedBuiltinValue size a) where
    pretty (TypedBuiltinValue (TypedBuiltinSized se _) x) = pretty se <+> "!" <+> prettyDynamic x
    pretty (TypedBuiltinValue TypedBuiltinDyn          x) = prettyDynamic x

-- Encode '()' from Haskell as @all r. r -> r@ from PLC.
-- This is a very special instance, because it's used to define functions that are needed for
-- other instances, so we keep it here.
instance KnownDynamicBuiltinType () where
    toTypeEncoding _ = unit

    -- We need this matching, because otherwise Haskell expressions are thrown away rather than being
    -- evaluated and we use 'unsafePerformIO' in multiple places, so we want to compute the '()' just
    -- for side effects the evaluation may cause.
    makeDynamicBuiltin () = pure unitval

    readDynamicBuiltin eval term = do
        let int1 = TyApp () (TyBuiltin () TyInteger) (TyInt () 4)
            asInt1 = Constant () . BuiltinInt () 1
        res <- eval mempty . Apply () (TyInst () term int1) $ asInt1 1
        pure $ lift res >>= \case
            Constant () (BuiltinInt () 1 1) -> pure ()
            _                               -> throwError "Not a builtin ()"

instance (KnownSymbol text, KnownNat uniq) =>
        KnownDynamicBuiltinType (OpaqueTerm text uniq) where
    toTypeEncoding _ =
        TyVar () . TyName $
            Name ()
                (Text.pack $ symbolVal @text Proxy)
                (Unique . fromIntegral $ natVal @uniq Proxy)

    makeDynamicBuiltin = pure . unOpaqueTerm

    readDynamicBuiltin eval term = lift . fmap OpaqueTerm <$> eval mempty term
