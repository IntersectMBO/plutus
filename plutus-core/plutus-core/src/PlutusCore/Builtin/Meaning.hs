{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE StandaloneKindSignatures  #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

{-# LANGUAGE StrictData                #-}

module PlutusCore.Builtin.Meaning where

import PlutusPrelude

import PlutusCore.Builtin.Elaborate
import PlutusCore.Builtin.HasConstant
import PlutusCore.Builtin.KnownKind
import PlutusCore.Builtin.KnownType
import PlutusCore.Builtin.KnownTypeAst
import PlutusCore.Builtin.Runtime
import PlutusCore.Builtin.TypeScheme
import PlutusCore.Core
import PlutusCore.Evaluation.Machine.ExBudgetStream
import PlutusCore.Evaluation.Machine.ExMemoryUsage
import PlutusCore.Name

import Control.DeepSeq
import Data.Array
import Data.Kind qualified as GHC
import Data.Proxy
import Data.Some.GADT
import GHC.Exts (inline, lazy, oneShot)
import GHC.TypeLits

-- | Turn a list of Haskell types @args@ into a functional type ending in @res@.
--
-- >>> :set -XDataKinds
-- >>> :kind! FoldArgs [(), Bool] Integer
-- FoldArgs [(), Bool] Integer :: *
-- = () -> Bool -> Integer
type family FoldArgs args res where
    FoldArgs '[]           res = res
    FoldArgs (arg ': args) res = arg -> FoldArgs args res

-- | The meaning of a built-in function consists of its type represented as a 'TypeScheme',
-- its Haskell denotation and its uninstantiated runtime denotation.
--
-- The 'TypeScheme' of a built-in function is used for example for
--
-- 1. computing the PLC type of the function to be used during type checking
-- 2. getting arity information
-- 3. generating arbitrary values to apply the function to in tests
--
-- The denotation is lazy, so that we don't need to worry about a builtin being bottom
-- (happens in tests). The production path is not affected by that, since only runtime denotations
-- are used for evaluation.
data BuiltinMeaning val cost =
    forall args res. BuiltinMeaning
        (TypeScheme val args res)
        ~(FoldArgs args res)
        (cost -> BuiltinRuntime val)

-- | Constraints available when defining a built-in function.
type HasMeaningIn uni val = (Typeable val, ExMemoryUsage val, HasConstantIn uni val)

-- | A type class for \"each function from a set of built-in functions has a 'BuiltinMeaning'\".
class
        ( Typeable uni
        , Typeable fun
        , Bounded fun
        , Enum fun
        , Ix fun
        , Default (BuiltinSemanticsVariant fun)
        ) => ToBuiltinMeaning uni fun where
    -- | The @cost@ part of 'BuiltinMeaning'.
    type CostingPart uni fun

    -- | See Note [Builtin semantics variants]
    data BuiltinSemanticsVariant fun

    -- | Get the 'BuiltinMeaning' of a built-in function.
    toBuiltinMeaning
        :: HasMeaningIn uni val
        => BuiltinSemanticsVariant fun
        -> fun
        -> BuiltinMeaning val (CostingPart uni fun)

-- | Get the type of a built-in function.
typeOfBuiltinFunction
    :: forall uni fun. ToBuiltinMeaning uni fun
    => BuiltinSemanticsVariant fun
    -> fun
    -> Type TyName uni ()
typeOfBuiltinFunction semvar fun =
    case toBuiltinMeaning @_ @_ @(Term TyName Name uni fun ()) semvar fun of
        BuiltinMeaning sch _ _ -> typeSchemeToType sch

{- Note [Builtin semantics variants]
The purpose of the "builtin semantics variant" feature is to provide multiple,
different denotations (implementations) for the same builtin(s).  An example use
of this feature is for "fixing" the behaviour of `ConsByteString` builtin to
throw an error instead of overflowing its first argument.

One denotation from each builtin is grouped into a 'BuiltinSemanticsVariant'.
Each Plutus Language version is linked to a specific 'BuiltinSemanticsVariant'
(done by plutus-ledger-api); e.g. plutus-v1 and plutus-v2 are linked to
'DefaultFunSemanticsVariant1', whereas plutus-v3 changes the set of denotations
to 'DefaultFunSemanticsVariant2' (thus fixing 'ConsByteString').

Each 'BuiltinSemanticsVariant' (grouping) can change the denotation of one or
more builtins --- or none, but what's the point in that?

This 'BuiltinSemanticsVariant' is modelled as a datatype *associated* to the
@fun@. This associated datatype is required to provide an instance of 'Default'
for quality-of-life purpose; the 'def'ault builtin semantics variant is expected
to point to the builtin semantics variant that the plutus-tx/plutus-ir compiler
is currently targeting.

Note that (old) denotations of a 'BuiltinSemanticsVariant' cannot be removed or
deprecated once published to the chain.

The way that this feature is implemented buys us more than we currently need:
- allows also a versioned change to a builtin's *type signature*, i.e. type of arguments/result as
  well as number of arguments.
- allows also a versioned change to a builtin's cost model parameters

Besides having no need for this currently, it complicates the codebase since the
typechecker now pointlessly wants to know the builtin semantics before
typechecking. To alleviate this, we use the 'Default.def' builtin semantics
variant during typechecking / lifting. @effectfully: the solution to the problem
would be to establish what kind of backwards compatibility we're willing to
maintain and pull all of that into a separate data type and make it a part of
BuiltinMeaning.
-}

{- Note [Automatic derivation of type schemes]
We use two type classes for automatic derivation of type/runtime schemes and runtime denotations:
'KnownPolytype' and 'KnownMonotype'.
The terminology is due to
https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system#The_Hindley%E2%80%93Milner_
type_system

Check out the source of "PlutusCore.Builtin.Runtime" for an explanation of what a runtime
denotation is.

'KnownPolytype' and 'KnownMonotype' are responsible for deriving polymorphic and monomorphic types,
respectively.

'KnownPolytype' turns every bound variable into a 'TypeSchemeAll'/'BuiltinExpectForce'. We extract
variables from the type of the Haskell denotation using the 'ToBinds' associated type
family. Variables are collected in the order that they appear in (i.e. just like in Haskell). For
example, processing a type like

      :: ( a ~ Opaque val (TyVarRep ('TyNameRep "a" 0))
         , b ~ Opaque val (TyVarRep ('TyNameRep "b" 1))
         )
      => b -> a -> b

with 'ToBinds' results in the following list of bindings:

    '[ 'Some ('TyNameRep "b" 1), 'Some ('TyNameRep "a" 0) ]

'KnownMonotype' turns every argument that the Haskell denotation of a builtin receives into a
'TypeSchemeArrow'/'BuiltinExpectArgument'. We extract the arguments from the type of the Haskell
denotation using the 'GetArgs' type family.

Higher-kinded type variables are fully supported.

At this point in the pipeline the type of the denotation of a builtin is assumed to be fully
elaborated (i.e. monomorphic).
-}

-- | Chop a function type to get a list of its argument types.
type GetArgs :: GHC.Type -> [GHC.Type]
type family GetArgs a where
    GetArgs (a -> b) = a ': GetArgs b
    GetArgs _        = '[]

{- Note [Merging the denotation and the costing function]
The runtime denotation of a builtin computes both the builtin application and its cost
(see the docs of 'BuiltinRuntime' for details). Doing both at the same time has a number of benefits
(see Note [runCostingFun* API]), however in the user-facing API we want to separate the concepts
of the denotation and the costing function. This is because:

1. the two are fundamentally distinct and we have loads of documentation for each of them
   separately, so conflating them in the actual API would be unnecessary coupling
2. right now it's clear which bits of the definition of a builtin constitute evaluation and which
   ones constitute costing as the two are different arguments to 'makeBuiltinMeaning'. If evaluation
   and costing were intertwined, it would be much harder to review the definition of a builtin
3. ... and it would also be more boilerplate and less clear type signatures

Hence we want 'makeBuiltinMeaning' to take evaluation and costing bits separately and intertwine
them behind the scenes. Which is straightforward: we only need to pass the two together in the
methods of the 'KnownMonotype' and 'KnownPolytype' classes and zip them argument by argument
into a single 'BuiltinRuntime'.
-}

-- | A class that allows us to derive a monotype for a builtin.
-- We could've computed the runtime denotation from the
-- 'TypeScheme' and the denotation of the builtin, but not statically (due to unfolding not working
-- for recursive functions and 'TypeScheme' being recursive, i.e. requiring the conversion function
-- to be recursive), and so it would cause us to retain a lot of evaluation-irrelevant stuff in the
-- constructors of 'BuiltinRuntime', which has to make evaluation slower (we didn't check) and
-- certainly makes the generated Core much harder to read. Technically speaking, we could get
-- a 'RuntimeScheme' from the 'TypeScheme' and the denotation statically if we changed the
-- definition of 'TypeScheme' and made it a singleton, but then the conversion function would have
-- to become a class anyway and we'd just replicate what we have here, except in a much more
-- complicated way.
class KnownMonotype val args res where
    knownMonotype :: TypeScheme val args res

    -- | Convert the denotation of a builtin to its runtime counterpart .
    -- The argument is in 'ReadKnownM', because that's what deferred unlifting amounts to:
    -- passing the action returning the builtin application around until full saturation, which is
    -- when the action actually gets run.
    toMonoF
        :: ReadKnownM (FoldArgs args res, FoldArgs args ExBudgetStream)
        -> BuiltinRuntime val

-- | Once we've run out of term-level arguments, we return a
-- 'TypeSchemeResult'/'RuntimeSchemeResult'.
instance (Typeable res, KnownTypeAst TyName (UniOf val) res, MakeKnown val res) =>
            KnownMonotype val '[] res where
    knownMonotype = TypeSchemeResult

    -- We need to lift the 'ReadKnownM' action into 'MakeKnownM',
    -- hence 'liftReadKnownM'.
    toMonoF =
        either
            -- Unlifting has failed and we don't care about costing at this point, since we're about
            -- to terminate evaluation anyway, hence we put 'mempty' as the cost of the operation.
            --
            -- Note that putting the cost inside of 'MakeKnownM' is not an option, since forcing
            -- the 'MakeKnownM' computation is exactly forcing the builtin application, which we
            -- can't do before accounting for the cost of the application, i.e. the cost must be
            -- outside of 'MakeKnownM'.
            --
            -- We could introduce a level of indirection and say that a 'BuiltinResult' is either
            -- a budgeting failure or a budgeting success with a cost and a 'MakeKnownM' computation
            -- inside, but that would slow things down a bit and the current strategy is
            -- reasonable enough.
            (BuiltinResult (ExBudgetLast mempty) . MakeKnownFailure mempty)
            (\(x, cost) -> BuiltinResult cost $ makeKnown x)
    {-# INLINE toMonoF #-}

{- Note [One-shotting runtime denotations]
In @KnownMonotype val (arg ': args) res@ we 'oneShot' the runtime denotations. Otherwise GHC creates
let-bindings and lifts them out of some of the lambdas in the runtime denotation, which would speed
up partial applications if they were getting reused, but at some point it was verified that we
didn't have any reusage of partial applications: https://github.com/input-output-hk/plutus/pull/4629

One-shotting the runtime denotations alone made certain game contracts slower by ~9%. A lot of time
was spent on the investigation, but we still don't know why that was happening. Plus, basically any
other change to the builtins machinery would cause the same kind of slowdown, so we just admitted
defeat and decided it wasn't worth investigating the issue further.
Relevant thread: https://github.com/input-output-hk/plutus/pull/4620

The speedup that adding a call to 'oneShot' gives us, if any, is smaller than our noise threshold,
however it also makes those confusing allocations disappear from the generated Core, which is enough
of a reason to add the call.
-}

{- Note [Strict application in runtime denotations]
Runtime denotations contain strict let-bindings. Those are important: without them GHC thinks that
the argument may not be needed in the end and so creates a thunk for it, which is not only
unnecessary allocation, but also prevents things from being unboxed. The argument may indeed not be
needed in the end, but in that case we've got an evaluation failure and we're about to terminate
evaluation anyway, hence we care much more about optimizing the happy path.
-}

-- | Every term-level argument becomes a 'TypeSchemeArrow'/'RuntimeSchemeArrow'.
instance
        ( Typeable arg, KnownTypeAst TyName (UniOf val) arg, MakeKnown val arg, ReadKnown val arg
        , KnownMonotype val args res
        ) => KnownMonotype val (arg ': args) res where
    knownMonotype = TypeSchemeArrow knownMonotype

    -- See Note [One-shotting runtime denotations].
    -- Grow the builtin application within the received action and recurse on the result.
    toMonoF getBoth = BuiltinExpectArgument . oneShot $ \arg ->
        -- Ironically computing the unlifted value strictly is the best way of doing deferred
        -- unlifting. This means that while the resulting 'ReadKnownM' is only handled upon full
        -- saturation and any evaluation failure is only registered when the whole builtin
        -- application is evaluated, a Haskell exception will occur immediately.
        -- It shouldn't matter though, because a builtin is not supposed to throw an
        -- exception at any stage, that would be a bug regardless.
        toMonoF @val @args @res $! do
            (f, exF) <- getBoth
            x <- readKnown arg
            -- See Note [Strict application in runtime denotations].
            let !exY = exF x
            pure (f x, exY)
    {-# INLINE toMonoF #-}

-- | A class that allows us to derive a polytype for a builtin.
class KnownMonotype val args res => KnownPolytype (binds :: [Some TyNameRep]) val args res where
    knownPolytype :: TypeScheme val args res

    -- | Convert the denotation of a builtin to its runtime counterpart.
    -- The argument is in 'ReadKnownM', because that's what we need to do:
    -- passing the action returning the builtin application around until full saturation, which is
    -- when the action actually gets run.
    toPolyF
        :: ReadKnownM (FoldArgs args res, FoldArgs args ExBudgetStream)
        -> BuiltinRuntime val

-- | Once we've run out of type-level arguments, we start handling term-level ones.
instance KnownMonotype val args res => KnownPolytype '[] val args res where
    knownPolytype = knownMonotype

    toPolyF  = toMonoF @val @args @res
    {-# INLINE toPolyF #-}

-- Here we unpack an existentially packed @kind@ and constrain it afterwards!
-- So promoted existentials are true sigmas! If we were at the term level, we'd have to pack
-- @kind@ along with the @KnownKind kind@ constraint, otherwise when we unpack the existential,
-- all information is lost and we can't do anything with @kind@.
-- | Every type-level argument becomes a 'TypeSchemeAll'.
instance (KnownSymbol name, KnownNat uniq, KnownKind kind, KnownPolytype binds val args res) =>
            KnownPolytype ('Some ('TyNameRep @kind name uniq) ': binds) val args res where
    knownPolytype = TypeSchemeAll @name @uniq @kind Proxy $ knownPolytype @binds

    toPolyF = BuiltinExpectForce . toPolyF @binds @val @args @res
    {-# INLINE toPolyF #-}

-- | Ensure a built-in function is not nullary and throw a nice error otherwise.
type ThrowOnBothEmpty :: [Some TyNameRep] -> [GHC.Type] -> Bool -> GHC.Type -> GHC.Constraint
type family ThrowOnBothEmpty binds args isBuiltin a where
    ThrowOnBothEmpty '[] '[] 'True a =
        TypeError (
            'Text "A built-in function must take at least one type or term argument" ':$$:
            'Text "‘" ':<>: 'ShowType a ':<>: 'Text "’ is a built-in type" ':<>:
            'Text " so you can embed any of its values as a constant" ':$$:
            'Text "If you still want a built-in function, add a dummy ‘()’ argument"
            )
    ThrowOnBothEmpty '[] '[] 'False a =
        TypeError (
            'Text "A built-in function must take at least one type or term argument" ':$$:
            'Text "To fix this error add a dummy ‘()’ argument"
            )
    ThrowOnBothEmpty _ _ _ _ = ()

-- | A function turned into a type class with exactly one fully general instance.
-- We can't package up the constraints of 'makeBuiltinMeaning' (see the instance) into a type or
-- class synonym, because they contain a bunch of variables defined by @~@ or determined via
-- functional dependencies and neither class nor type definitions can handle that
-- (see https://gitlab.haskell.org/ghc/ghc/-/issues/7100). Inlining three lines of constraints
-- whenever we need to call 'makeBuiltinMeaning' over a non-concrete type is a bad option and this
-- abstraction is free anyway, hence its existence.
--
-- The @a@ type variable goes first, because @makeBuiltinMeaning \@A@ is a common pattern.
class MakeBuiltinMeaning a val where
    -- See Note [Automatic derivation of type schemes]
    -- | Construct the meaning for a built-in function by automatically deriving its
    -- 'TypeScheme', given
    --
    -- 1. the denotation of the builtin
    -- 2. an uninstantiated costing function
    makeBuiltinMeaning
        :: a
        -> (cost -> FoldArgs (GetArgs a) ExBudgetStream)
        -> BuiltinMeaning val cost
instance
        ( uni ~ UniOf val, binds ~ ToBinds uni '[] a, args ~ GetArgs a, a ~ FoldArgs args res
        , ThrowOnBothEmpty binds args (IsBuiltin uni a) a
        , ElaborateFromTo uni 0 j val a, KnownPolytype binds val args res
        ) => MakeBuiltinMeaning a val where
    makeBuiltinMeaning f toExF =
        BuiltinMeaning (knownPolytype @binds @val @args @res) f $ \cost ->
            -- In order to make the 'BuiltinRuntime' of a builtin cacheable we need to tell GHC to
            -- create a thunk for it, which we achieve by applying 'lazy' to the 'BuiltinRuntime'
            -- here.
            --
            -- Those thunks however require a lot of care to be properly shared rather than
            -- recreated every time a builtin application is evaluated, see 'toBuiltinsRuntime' for
            -- how we sort it out.
            lazy $ case toExF cost of
                -- See Note [Optimizations of runCostingFun*] for why we use strict @case@.
                !exF -> toPolyF @binds @val @args @res $ pure (f, exF)
    {-# INLINE makeBuiltinMeaning #-}

-- | Convert a 'BuiltinMeaning' to a 'BuiltinRuntime' given a cost model.
toBuiltinRuntime :: cost -> BuiltinMeaning val cost -> BuiltinRuntime val
toBuiltinRuntime cost (BuiltinMeaning _ _ denot) = denot cost
{-# INLINE toBuiltinRuntime #-}

-- See Note [Inlining meanings of builtins].
-- | Calculate runtime info for all built-in functions given meanings of builtins (as a constraint),
-- the semantics variant of the set of builtins and a cost model.
toBuiltinsRuntime
    :: (cost ~ CostingPart uni fun, ToBuiltinMeaning uni fun, HasMeaningIn uni val)
    => BuiltinSemanticsVariant fun
    -> cost
    -> BuiltinsRuntime fun val
toBuiltinsRuntime semvar cost =
    let runtime = BuiltinsRuntime $ toBuiltinRuntime cost . inline toBuiltinMeaning semvar
        -- This pragma is very important, removing it destroys the carefully set up optimizations of
        -- of costing functions (see Note [Optimizations of runCostingFun*]). The reason for that is
        -- that if @runtime@ doesn't have a pragma, then GHC sees that it's only referenced once and
        -- inlines it below, together with this entire function (since we tell GHC to), at which
        -- point everything's inlined and we're completely at GHC's mercy to optimize things
        -- properly. Unfortunately, GHC doesn't want to cooperate and push 'toBuiltinRuntime' to
        -- the inside of the inlined to 'toBuiltinMeaning' call, creating lots of 'BuiltinMeaning's
        -- instead of 'BuiltinRuntime's with the former hiding the costing optimizations behind a
        -- lambda binding the @cost@ variable, which renders all the optimizations useless. By
        -- using a @NOINLINE@ pragma we tell GHC to create a separate thunk, which it can properly
        -- optimize, because the other bazillion things don't get in the way.
        {-# NOINLINE runtime #-}
    in
        -- Force each 'BuiltinRuntime' to WHNF, so that the thunk is allocated and forced at
        -- initialization time rather than at runtime. Not that we'd lose much by not forcing all
        -- 'BuiltinRuntime's here, but why pay even very little if there's an easy way not to pay.
        force runtime
{-# INLINE toBuiltinsRuntime #-}
