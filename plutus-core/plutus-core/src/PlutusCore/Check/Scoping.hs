{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE UndecidableInstances  #-}
-- TODO: add @NoFieldSelectors@ once we are past antiquity, so that 'ScopeError' doesn't generate
-- partial field selectors.

module PlutusCore.Check.Scoping where

import PlutusCore.Name.Unique
import PlutusCore.Quote

import Control.Monad (join, unless)
import Data.Bifunctor
import Data.Coerce
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict as Map
import Data.Maybe
import Data.Proxy
import Data.Set as Set
import Text.Pretty
import Text.PrettyBy

{- Note [Example of a scoping check]
Consider the following type:

    \(x_42 :: *) -> x_42

This Note describes how we can use this type to check that a renamer handles scoping correctly.
Any other type could be used as well (and in property tests we generate random ones), but the type
above is the simplest example, so we're going to use it.

First, we traverse the type and freshen every single name in it, which gives us

    \(x_0 :: *) -> x_1

After this procedure all names in the new type are distinct, not just globally unique -- completely
distinct: all variables are free variables with different uniques and all bindings are distinct and
never referenced.

Now for each binder we insert one in-scope variable and one out-of-scope one by referencing them
in an added constructor (we could use 'TyFun', but we use 'TyApp', 'cause it has an analogue at the
term level -- 'Apply' and we can also reference a type variable in a 'Term' via a similar
constructor -- 'TyInst'). That gives us

    (\(x_0 :: *) -> x_1 x_0) x_0

(currently we just decorate the binder with those constructors. In future we could employ a fancier
strategy and go under to the leaves of the term being processed etc).

The next step is to annotate each name with what is supposed to happen to it once the renaming is
performed.

1. the @x_0@ binding is supposed to be renamed and hence will disappear
2. the @x_1@ variable is free, so it's supposed to stay free
3. the inner @x_0@ variable is in scope and so is supposed to be renamed
4. the outer @x_0@ is out of scope and so is free and is supposed to stay

In the actual implementation everything that we did above happens in a single definition.

After this initial scoping setup is performed, we run the provided renamer (which is not supposed
to touch any annotations) and collect all the available information: which names disappeared,
which didn't, which appeared etc, simultaneously checking that the names that were supposed to
disappear indeed disappeared and the names that were supposed to stay indeed stayed.

Note that to tell that e.g. a binding disappeared it's crucial that the AST node with the appopriate
annotation is itself preserved, only the name changed. If some pass removes the AST node of a
binding that is supposed to be disappear, it won't be accounted for. Which is precisely what we need
for passes like inlining.

Once all this scoping information is collected, we run 'checkScopeInfo' to check that the
information is coherent. See its docs for the details on what exactly the checked invariants are.

The advantage of this approach is that we can pinpoint exactly where what is visible and, just
as importantly, what is not.
-}

data ScopedName
    = TypeName TyName
    | TermName Name
    deriving stock (Show, Eq, Ord)

isSameScope :: ScopedName -> ScopedName -> Bool
isSameScope TypeName{} TypeName{} = True
isSameScope TermName{} TermName{} = True
isSameScope TypeName{} TermName{} = False
isSameScope TermName{} TypeName{} = False

-- | Staying names.
data Stays
    = StaysOutOfScopeVariable  -- ^ An out-of-scope variable does not get renamed and hence stays.
    | StaysFreeVariable        -- ^ A free variable does not get renamed and hence stays.
    deriving stock (Show, Eq)

-- | Changing names.
data Disappears
    = DisappearsBinding   -- ^ A binding gets renamed and hence the name that it binds disappears.
    | DisappearsVariable  -- ^ A bound variable gets renamed and hence its name disappears.
    deriving stock (Show, Eq)

-- | A name either stays or disappears.
data NameAction
    = Stays Stays
    | Disappears Disappears
    deriving stock (Show, Eq)

data NameAnn
    = NameAction NameAction ScopedName
    | NotAName
    deriving stock (Show, Eq)

instance Pretty NameAnn where
    pretty = viaShow

class ToScopedName name where
    toScopedName :: name -> ScopedName

instance ToScopedName TyName where
    toScopedName = TypeName

instance ToScopedName Name where
    toScopedName = TermName

-- Naming: @introduce*@ for bindings and @register*@ for variables.

-- | Annotation for a binding saying \"supposed to disappear\".
introduceBound :: ToScopedName name => name -> NameAnn
introduceBound = NameAction (Disappears DisappearsBinding) . toScopedName

-- | Annotation for a bound variable saying \"supposed to disappear\".
registerBound :: ToScopedName name => name -> NameAnn
registerBound = NameAction (Disappears DisappearsVariable) . toScopedName

-- | Annotation for an out-of-scope variable saying \"supposed to stay out of scope\".
registerOutOfScope :: ToScopedName name => name -> NameAnn
registerOutOfScope = NameAction (Stays StaysOutOfScopeVariable) . toScopedName

-- | Annotation for a free variable saying \"supposed to stay free\".
registerFree :: ToScopedName name => name -> NameAnn
registerFree = NameAction (Stays StaysFreeVariable) . toScopedName

class Reference n t where
    -- | Take a registering function, apply it to the provided name, create a type\/term variable
    -- out of the resulting annotation and the original name and reference that variable in the
    -- provided type\/term by prepending a constructor to it mentioning the variable.
    referenceVia
        :: (forall name. ToScopedName name => name -> NameAnn)
        -> n
        -> t NameAnn
        -> t NameAnn

-- | Reference the provided variable in the provided type\/term as an in-scope one.
referenceBound :: Reference n t => n -> t NameAnn -> t NameAnn
referenceBound = referenceVia registerBound

-- | Reference the provided variable in the provided type\/term as an out-of-scope one.
referenceOutOfScope :: Reference n t => n -> t NameAnn -> t NameAnn
referenceOutOfScope = referenceVia registerOutOfScope

-- #####################################################
-- ## Information about scopes and relevant functions ##
-- #####################################################

-- | Each kind of old and new names.
data ScopeEntry
    = DisappearedBindings
    | DisappearedVariables
    | AppearedBindings
    | AppearedVariables
    | StayedOutOfScopeVariables
    | StayedFreeVariables
    deriving stock (Show, Eq, Ord)

-- | A 'ScopeInfo' is a set of 'ScopedName's for each of the 'ScopeEntry'.
-- If a 'ScopeEntry' is not present in the map, the corresponding set of 'ScopeName's is considered
-- to be empty.
newtype ScopeInfo = ScopeInfo (Map ScopeEntry (Set ScopedName))
    deriving stock (Show)

-- Defining manually because of plan to move to @NoFieldSelectors@.
unScopeInfo :: ScopeInfo -> Map ScopeEntry (Set ScopedName)
unScopeInfo = coerce

-- | Extract the set stored in the provided 'ScopeInfo' at the provided 'ScopeEntry'.
to :: ScopeEntry -> ScopeInfo -> Set ScopedName
to entry = fromMaybe Set.empty . Map.lookup entry . unScopeInfo

emptyScopeInfo :: ScopeInfo
emptyScopeInfo = ScopeInfo Map.empty

-- | Check if a set is empty and report an error with the set embedded in it otherwise.
checkEmptyOn
    :: (Set ScopedName -> Set ScopedName -> Set ScopedName)
    -> (Set ScopedName -> Set ScopedName -> ScopeError)
    -> Set ScopedName
    -> Set ScopedName
    -> Either ScopeError ()
checkEmptyOn f err s1 s2 = unless (Set.null $ f s1 s2) . Left $ err s1 s2

-- | Merge two 'ScopeInfo's checking that binders in them do not intersect along the way.
mergeScopeInfo :: ScopeInfo -> ScopeInfo -> Either ScopeError ScopeInfo
mergeScopeInfo si1 si2 = do
    let disappearedBindings1 = to DisappearedBindings si1
        disappearedBindings2 = to DisappearedBindings si2
        appearedBindings1    = to AppearedBindings    si1
        appearedBindings2    = to AppearedBindings    si2
    checkEmptyOn
        Set.intersection
        DuplicateBindersInTheInput
        disappearedBindings1
        disappearedBindings2
    checkEmptyOn
        Set.intersection
        DuplicateBindersInTheOutput
        appearedBindings1
        appearedBindings2
    Right $ coerce (Map.unionWith Set.union) si1 si2

-- We might want to use @Validation@ or something instead of 'Either'.
-- @newtype@-ing it for the sake of providing very convenient 'Semigroup' and 'Monoid' instances.
newtype ScopeErrorOrInfo = ScopeErrorOrInfo (Either ScopeError ScopeInfo)

-- Defining manually because of plan to move to @NoFieldSelectors@.
unScopeErrorOrInfo :: ScopeErrorOrInfo -> Either ScopeError ScopeInfo
unScopeErrorOrInfo = coerce

instance Semigroup ScopeErrorOrInfo where
    ScopeErrorOrInfo errOrInfo1 <> ScopeErrorOrInfo errOrInfo2 =
        ScopeErrorOrInfo . join $ mergeScopeInfo <$> errOrInfo1 <*> errOrInfo2

instance Monoid ScopeErrorOrInfo where
    mempty = ScopeErrorOrInfo $ Right emptyScopeInfo

-- | Whether it's OK if the pass removes bindings. A renamer isn't supposed to do that, but for
-- example an inliner may do it, since it's basically the entire point of an inliner.
data BindingRemoval
    = BindingRemovalOk
    | BindingRemovalNotOk
    deriving stock (Show, Eq)

-- ########################################################################
-- ## Main class for collecting scope information and relevant functions ##
-- ########################################################################

class EstablishScoping t where
    {-| Traverse a 't' freshening every name (both at the binding and the use sites)
    and annotating the freshened names with either 'DisappearsBinding' or 'StaysFreeVariable'
    depending on whether the name occurs at the binding or the use site.

    In addition to that every binder should be decorated with one out-of-scope variable (annotated
    with 'StaysOutOfScopeVariable') and one in-scope one (annotated with 'DisappearsVariable').

    Note that no original name occurring in 't' should survive this procedure (and hence we don't
    care if any of the freshened names clashes with an original one as all original ones are
    supposed to be gone).

    How to provide an implementation:

    1. handle bindings with 'freshen*Name' + 'establishScopingBinder' (or similar)
    2. handle variables with 'freshen*Name' + 'registerFree'
    3. everything else is direct recursion + 'Applicative' stuff
    -}
    establishScoping :: t ann -> Quote (t NameAnn)

-- That will retraverse the same type multiple times. Should we have @referenceListVia@ as a
-- primitive instead and derive 'referenceVia' in terms of it for better performance?
-- Should we only pick an arbitrary sublist of the provided list instead of using the whole list
-- for better performance? That requires enhancing 'Reference' with @Hedgehog.Gen@ or something.
instance Reference n t => Reference [n] t where
    referenceVia reg = flip . Prelude.foldr $ referenceVia reg

instance Reference n t => Reference (NonEmpty n) t where
    referenceVia reg = referenceVia reg . NonEmpty.toList

-- Given that it's straightforward to provide an implementation for the method,
-- it would be nice to somehow do that generically by default.
class CollectScopeInfo t where
    {-| Collect scoping information after scoping was established and renaming was performed.

    How to provide an implementation:

    1. handle names (both bindings and variables) with 'handleSname'
    2. everything else is direct recursion + 'Monoid' stuff
    -}
    collectScopeInfo :: t NameAnn -> ScopeErrorOrInfo

instance EstablishScoping Proxy where
    establishScoping _ = pure Proxy

instance CollectScopeInfo Proxy where
    collectScopeInfo _ = mempty

-- See Note [Example of a scoping check].
type Scoping t = (EstablishScoping t, CollectScopeInfo t)

-- | Take a constructor for a binder, a name bound by it, a sort (kind\/type), a value of that sort
-- (type\/term) and call 'establishScoping' on both the sort and its value and reassemble the
-- original binder with the annotated sort and its value, but also decorate the reassembled binder
-- with one out-of-scope variable and one in-scope one.
establishScopingBinder
    :: (Reference name value, ToScopedName name, EstablishScoping sort, EstablishScoping value)
    => (NameAnn -> name -> sort NameAnn -> value NameAnn -> value NameAnn)
    -> name
    -> sort ann
    -> value ann
    -> Quote (value NameAnn)
establishScopingBinder binder name sort value = do
    sortS <- establishScoping sort
    referenceOutOfScope name .
        binder (introduceBound name) name sortS .
            referenceBound name <$>
                establishScoping value

-- #############################################
-- ## Checking coherence of scope information ##
-- #############################################

-- | Every kind of error thrown by the scope checking machinery at different stages.
data ScopeError
    = UnannotatedName !ScopedName
    | NameChangedItsScope
        { _oldName :: !ScopedName
        , _newName :: !ScopedName
        }
    | NameUnexpectedlyDisappeared
        { _oldName :: !ScopedName
        , _newName :: !ScopedName
        }
    | NameUnexpectedlyStayed !ScopedName
    | DuplicateBindersInTheInput
        { _duplicateBindersLeft  :: !(Set ScopedName)
        , _duplicateBindersRight :: !(Set ScopedName)
        }
    | DuplicateBindersInTheOutput !(Set ScopedName) !(Set ScopedName)
    | DisappearedBindingsDiscordWithBoundVariables
        { _disappearedBindings :: !(Set ScopedName)
        , _boundVariables      :: !(Set ScopedName)
        }
    | DisappearedBindingsDiscordWithOutOfScopeVariables
        { _disappearedBindings :: !(Set ScopedName)
        , _outOfScopeVariables :: !(Set ScopedName)
        }
    | AppearedBindingsDiscordWithBoundVariables
        { _appearedBindings :: !(Set ScopedName)
        , _boundVariables   :: !(Set ScopedName)
        }
    | DisappearedBindingsClashWithFreeVariables
        { _disappearedBindings :: !(Set ScopedName)
        , _freeVariables       :: !(Set ScopedName)
        }
    | DisappearedBindingsClashWithAppearedBindings
        { _disppearedBindings :: !(Set ScopedName)
        , _appearedBindings   :: !(Set ScopedName)
        }
    | AppearedBindingsClashWithFreeVariabes
        { _appearedBindings :: !(Set ScopedName)
        , _freeVariables    :: !(Set ScopedName)
        }
    deriving stock (Show)

instance Pretty ScopeError where
    pretty = viaShow

-- | Override the set at the provided 'ScopeEntry' to contain only the provided 'ScopedName'.
overrideSname :: ScopeEntry -> ScopedName -> ScopeInfo -> ScopeInfo
overrideSname key = coerce . Map.insert key . Set.singleton

-- | Use a 'Stays' to handle an unchanged old name.
applyStays :: Stays -> ScopedName -> ScopeInfo
applyStays stays sname = overrideSname key sname emptyScopeInfo where
    key = case stays of
        StaysOutOfScopeVariable -> StayedOutOfScopeVariables
        StaysFreeVariable       -> StayedFreeVariables

-- | Use a 'Disappears' to handle differing old and new names.
applyDisappears :: Disappears -> ScopedName -> ScopedName -> ScopeInfo
applyDisappears disappears snameOld snameNew =
    overrideSname keyNew snameNew $ overrideSname keyOld snameOld emptyScopeInfo where
        (keyOld, keyNew) = case disappears of
            DisappearsBinding  -> (DisappearedBindings, AppearedBindings)
            DisappearsVariable -> (DisappearedVariables, AppearedVariables)

-- | Use a 'NameAction' to handle an old and a new name.
applyNameAction
    :: NameAction -> ScopedName -> ScopedName -> Either ScopeError ScopeInfo
applyNameAction (Stays stays) snameOld snameNew
    | snameOld == snameNew = Right $ applyStays stays snameOld
    | otherwise            = Left $ NameUnexpectedlyDisappeared snameOld snameNew
applyNameAction (Disappears disappears) snameOld snameNew
    | snameOld == snameNew = Left $ NameUnexpectedlyStayed snameOld
    | otherwise            = Right $ applyDisappears disappears snameOld snameNew

-- | Use a 'NameAnn' to handle a new name.
handleSname :: ToScopedName name => NameAnn -> name -> ScopeErrorOrInfo
handleSname ann nameNew = ScopeErrorOrInfo $ do
    let snameNew = toScopedName nameNew
    case ann of
        NotAName -> Left $ UnannotatedName snameNew
        NameAction action snameOld ->
            if snameOld `isSameScope` snameNew
                then applyNameAction action snameOld snameNew
                else Left $ NameChangedItsScope snameOld snameNew

symmetricDifference :: Ord a => Set a -> Set a -> Set a
symmetricDifference s t = (s `Set.union` t) `Set.difference` (s `Set.intersection` t)

{-| Check that each kind of 'Set' from 'ScopeInfo' relates to all other ones in a certain way.
We start with these three relations that are based on the assumption that for each binder we add
at least one out-of-scope variable and at least one in-scope one:

1. disappeared bindings should be the same as stayed out of scope variables
     (ensures that old bindings disappear via renaming and not via removal)
2. disappeared bindings should be the same as disappeared variables
     (ensures that old names consistently disappear at the binding and use sites)
3. appeared bindings should be the same as appeared variables
     (ensures that new names consistently appear at the binding and use sites)

Once we've ensured all of that, we're left with only three sets and 3C2 equals 3,
so we only need to consider three more relations:

1. disappeared bindings should not intersect with free variables
     (an internal sanity check)
2. appeared bindings should not intersect with disappeared bindings
3. appeared bindings should not intersect with free variables

The last two ensure that no new name has an old name's unique.
-}
checkScopeInfo :: BindingRemoval -> ScopeInfo -> Either ScopeError ()
checkScopeInfo bindRem scopeInfo = do
    let disappearedBindings       = to DisappearedBindings       scopeInfo
        disappearedVariables      = to DisappearedVariables      scopeInfo
        appearedBindings          = to AppearedBindings          scopeInfo
        appearedVariables         = to AppearedVariables         scopeInfo
        stayedOutOfScopeVariables = to StayedOutOfScopeVariables scopeInfo
        stayedFreeVariables       = to StayedFreeVariables       scopeInfo
    unless (bindRem == BindingRemovalOk) $ do
        checkEmptyOn
            symmetricDifference
            DisappearedBindingsDiscordWithOutOfScopeVariables
            disappearedBindings
            stayedOutOfScopeVariables
    checkEmptyOn
        symmetricDifference
        DisappearedBindingsDiscordWithBoundVariables
        disappearedBindings
        disappearedVariables
    checkEmptyOn
        symmetricDifference
        AppearedBindingsDiscordWithBoundVariables
        appearedBindings
        appearedVariables
    checkEmptyOn
        Set.intersection
        DisappearedBindingsClashWithFreeVariables
        disappearedBindings
        stayedFreeVariables
    checkEmptyOn
        Set.intersection
        DisappearedBindingsClashWithAppearedBindings
        appearedBindings
        disappearedBindings
    checkEmptyOn
        Set.intersection
        AppearedBindingsClashWithFreeVariabes
        appearedBindings
        stayedFreeVariables

-- | The type of errors that the scope checking machinery returns.
data ScopeCheckError t = ScopeCheckError
    { _input    :: !(t NameAnn)  -- ^ What got fed to the scoping check pass before preparation.
    , _prepared :: !(t NameAnn)  -- ^ What got fed to the scoping check pass after preparation.
    , _output   :: !(t NameAnn)  -- ^ What got out of it.
    , _error    :: !ScopeError   -- ^ The error returned by the scoping check pass.
    }

deriving stock instance Show (t NameAnn) => Show (ScopeCheckError t)

instance PrettyBy config (t NameAnn) => PrettyBy config (ScopeCheckError t) where
    prettyBy config (ScopeCheckError input prepared output err) = vsep
        [ pretty err
        , "when checking that transformation of" <> hardline
        , indent 2 $ prettyBy config input <> hardline
        , "to" <> hardline
        , indent 2 $ prettyBy config prepared <> hardline
        , "to" <> hardline
        , indent 2 $ prettyBy config output <> hardline
        , "is correct"
        ]

-- See Note [Example of a scoping check].
-- | Check if a pass respects scoping.
--
-- Returns the thing that the scoping tests run on, the result of the pass and the scope checking
-- outcome, respectively.
checkRespectsScoping
    :: Scoping t
    => BindingRemoval
    -> (t NameAnn -> t NameAnn)  -- ^ For preparation before running the scoping tests.
                                 --   Commonly, either @runQuote . rename@ or @id@.
    -> (t NameAnn -> t NameAnn)  -- ^ The runner of the pass.
    -> t ann
    -> Either (ScopeCheckError t) ()
checkRespectsScoping bindRem prep run thing =
    first (ScopeCheckError input prepared output) $
        unScopeErrorOrInfo (collectScopeInfo output) >>= checkScopeInfo bindRem
  where
    input    = runQuote $ establishScoping thing
    prepared = prep input
    output   = run prepared
