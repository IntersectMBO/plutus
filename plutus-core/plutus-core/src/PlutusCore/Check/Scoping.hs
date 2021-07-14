{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}

module PlutusCore.Check.Scoping where

import           PlutusCore.Name
import           PlutusCore.Quote

import           Control.Monad.Except
import           Data.Coerce
import           Data.Map.Strict      as Map
import           Data.Maybe
import           Data.Set             as Set

-- let nonrec x_1 = x_2 in x_3

-- let nonrec @(disappears_binding x_1) x_1 = @(stays_out_of_scope x_1) x_1 -> @(stays_free x_2) x_2 in @(disappears_bound x_1) x_1 -> @(stays_free x_3) x_3

-- let nonrec @(disappears_binding x_1) x_4 = @(stays_out_of_scope x_1) x_1 -> @(stays_free x_2) x_2 in @(disappears_bound x_1) x_4 -> @(stays_free x_3) x_3

-- @(disappears_binding x_1) x_4: x_1 must not be equal to x_4, x_1 is added to out_of_scope, x_4 is added to in_scope
-- @(stays_out_of_scope x_1) x_1: x_1 must be equal to x_1, x_1 must be in out_of_scope, x_1 must not be in in_scope
-- @(stays_free x_2) x_2: x_2 must be equal to x_2, x_2 must not be in out_of_scope, x_2 must not be in in_scope
-- @(disappears_bound x_1) x_4: x_1 must not be equal to x_4, x_1 must be in out_of_scope, x_4 must be in in_scope
-- @(stays_free x_3) x_3: x_3 must be equal to x_3, x_3 must not be in out_of_scope, x_3 must not be in in_scope



-- let nonrec x_1 = x_2 in x_3
-- let nonrec x_1 = x_2 in let nonrec x_1 = x_2 in x_3  -- Duplicating a binding makes the duplicate disappear


-- \x_1 -> x_2
-- x_1 (\x_1 -> x_1 x_2)
-- @(stays_out_of_scope x_1) x_1 (\(@disappears_binding x_1) x_1 -> @(disappears_variable x_1) x_1 @(stays_free x_2) x_2)
-- @(stays_out_of_scope x_1) x_1 (\(@disappears_binding x_1) x_3 -> @(disappears_variable x_1) x_3 @(stays_free x_2) x_2)

data ScopedName
    = TypeName TyName
    | TermName Name
    deriving (Show, Eq, Ord)

isSameScope :: ScopedName -> ScopedName -> Bool
isSameScope TypeName{} TypeName{} = True
isSameScope TermName{} TermName{} = True
isSameScope TypeName{} TermName{} = False
isSameScope TermName{} TypeName{} = False

data Persists
    = StaysOutOfScopeVariable
    | StaysFreeVariable
    deriving (Show)

data Changes
    = DisappearsBinding
    | DisappearsVariable
    deriving (Show)

data NameAction
    = Persists Persists
    | Changes Changes
    deriving (Show)

data NameAnn
    = NameAction NameAction ScopedName
    | NotAName
    deriving (Show)

class ToScopedName name where
    toScopedName :: name -> ScopedName

instance ToScopedName TyName where
    toScopedName = TypeName

instance ToScopedName Name where
    toScopedName = TermName

introduceBound :: ToScopedName name => name -> NameAnn
introduceBound = NameAction (Changes DisappearsBinding) . toScopedName

registerBound :: ToScopedName name => name -> NameAnn
registerBound = NameAction (Changes DisappearsVariable) . toScopedName

registerOutOfScope :: ToScopedName name => name -> NameAnn
registerOutOfScope = NameAction (Persists StaysOutOfScopeVariable) . toScopedName

registerFree :: ToScopedName name => name -> NameAnn
registerFree = NameAction (Persists StaysFreeVariable) . toScopedName

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
referenceInScope :: Reference n t => n -> t NameAnn -> t NameAnn
referenceInScope = referenceVia registerBound

-- | Reference the provided variable in the provided type\/term as an out-of-scope one.
referenceOutOfScope :: Reference n t => n -> t NameAnn -> t NameAnn
referenceOutOfScope = referenceVia registerOutOfScope

-- #####################################################
-- ## Information about scopes and relevant functions ##
-- #####################################################

data ScopeEntry
    = DisappearedBindings
    | DisappearedVariables
    | AppearedBindings
    | AppearedVariables
    | StayedOutOfScopeVariables
    | StayedFreeVariables
    deriving (Show, Eq, Ord)

newtype ScopeInfo = ScopeInfo
    { unScopeInfo :: Map ScopeEntry (Set ScopedName)
    } deriving (Show)

-- | Extract the set stored in the provided 'ScopeInfo' at the provided 'ScopeEntry'.
to :: ScopeEntry -> ScopeInfo -> Set ScopedName
to entry = fromMaybe Set.empty . Map.lookup entry . unScopeInfo

emptyScopeInfo :: ScopeInfo
emptyScopeInfo = ScopeInfo Map.empty

-- | Check if a set is empty and report an error with the set embedded in it otherwise.
checkEmpty :: (Set ScopedName -> ScopeError) -> Set ScopedName -> Either ScopeError ()
checkEmpty err s = unless (Set.null s) . Left $ err s

-- | Merge two 'ScopeInfo's checking that they do not intersect along the way.
mergeScopeInfo :: ScopeInfo -> ScopeInfo -> Either ScopeError ScopeInfo
mergeScopeInfo si1 si2 = do
    let disappearedBindings1 = to DisappearedBindings si1
        disappearedBindings2 = to DisappearedBindings si2
        appearedBindings1    = to AppearedBindings    si1
        appearedBindings2    = to AppearedBindings    si2
        duplicateDisappearedBindings = disappearedBindings1 `Set.intersection` disappearedBindings2
        duplicateAppearedBindings    = appearedBindings1    `Set.intersection` appearedBindings2
    checkEmpty DuplicateBindersInTheInput  duplicateDisappearedBindings
    checkEmpty DuplicateBindersInTheOutput duplicateAppearedBindings
    Right $ coerce (Map.unionWith Set.union) si1 si2

newtype ScopeErrorOrInfo = ScopeErrorOrInfo
    -- We might want to use @Validation@ or something instead of 'Either'.
    { unScopeErrorOrInfo :: Either ScopeError ScopeInfo
    }

instance Semigroup ScopeErrorOrInfo where
    ScopeErrorOrInfo errOrInfo1 <> ScopeErrorOrInfo errOrInfo2 =
        ScopeErrorOrInfo . join $ mergeScopeInfo <$> errOrInfo1 <*> errOrInfo2

instance Monoid ScopeErrorOrInfo where
    mempty = ScopeErrorOrInfo $ Right emptyScopeInfo

-- ########################################################################
-- ## Main class for collecting scope information and relevant functions ##
-- ########################################################################

-- Given that it's straightforward to provide an implementation for each of the methods,
-- it would be nice to somehow do that generically by default.
class Scoping t where
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
    establishScoping :: MonadQuote m => t ann -> m (t NameAnn)

    {-| Collect scoping information after scoping was established and renaming was performed.

    How to provide an implementation:

    1. handle names (both bindings and variables) with 'handleSname'
    2. everything else is direct recursion + 'Monoid' stuff
    -}
    collectScopeInfo :: t NameAnn -> ScopeErrorOrInfo

-- | Take a binder, a name bound by it, a sort (kind\/type), a value of that sort (type\/term)
-- and call 'establishScoping' on both the sort and its value and reassemble the original binder
-- with the annotated sort and its value, but also decorate the reassembled binder with
-- one out-of-scope variable and one in-scope one.
establishScopingBinder
    :: (Reference name lower, ToScopedName name, Scoping upper, Scoping lower, MonadQuote m)
    => (NameAnn -> name -> upper NameAnn -> lower NameAnn -> lower NameAnn)
    -> name
    -> upper ann
    -> lower ann
    -> m (lower NameAnn)
establishScopingBinder binder name upper lower = do
    upperS <- establishScoping upper
    referenceOutOfScope name .
        binder (introduceBound name) name upperS .
            referenceInScope name <$>
                establishScoping lower

-- #############################################
-- ## Checking coherence of scope information ##
-- #############################################

data ScopeError
    = UnannotatedName ScopedName
    | NameChangedItsScope ScopedName ScopedName
    | NameUnexpectedlyChanged ScopedName ScopedName
    | NameUnexpectedlyStayed ScopedName
    | DuplicateBindersInTheInput (Set ScopedName)
    | DuplicateBindersInTheOutput (Set ScopedName)
    | OldBindingsDiscordWithBoundVariables (Set ScopedName)
    | OldBindingsDiscordWithOutOfScopeVariables (Set ScopedName)
    | NewBindingsDiscordWithBoundVariables (Set ScopedName)
    | OldBindingsClashWithFreeVariables (Set ScopedName)
    | OldBindingsClashWithNewBindings (Set ScopedName)
    | NewBindingsClashWithFreeVariabes (Set ScopedName)
    deriving (Show)

-- | Overrisde the set at the provided 'ScopeEntry' to contain only the provided 'ScopedName'.
overrideSname :: ScopeEntry -> ScopedName -> ScopeInfo -> ScopeInfo
overrideSname key = coerce . Map.insert key . Set.singleton

-- | Use a 'Persists' to handle an unchanged old name.
applyPersists :: Persists -> ScopedName -> ScopeInfo
applyPersists persists sname = overrideSname key sname emptyScopeInfo where
    key = case persists of
        StaysOutOfScopeVariable -> StayedOutOfScopeVariables
        StaysFreeVariable       -> StayedFreeVariables

-- | Use a 'Changes' to handle differing old and new names.
applyChanges :: Changes -> ScopedName -> ScopedName -> ScopeInfo
applyChanges changes snameOld snameNew =
    overrideSname keyNew snameNew $ overrideSname keyOld snameOld emptyScopeInfo where
        (keyOld, keyNew) = case changes of
            DisappearsBinding  -> (DisappearedBindings, AppearedBindings)
            DisappearsVariable -> (DisappearedVariables, AppearedVariables)

-- | Use a 'NameAction' to handle an old and a new name.
applyNameAction
    :: NameAction -> ScopedName -> ScopedName -> Either ScopeError ScopeInfo
applyNameAction (Persists persists) snameOld snameNew =
    if snameOld == snameNew
        then Right $ applyPersists persists snameOld
        else Left $ NameUnexpectedlyChanged snameOld snameNew
applyNameAction (Changes changes) snameOld snameNew =
    if snameOld == snameNew
        then Left $ NameUnexpectedlyStayed snameOld
        else Right $ applyChanges changes snameOld snameNew

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
     (an internal sanity check)
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
checkScopeInfo :: ScopeInfo -> Either ScopeError ()
checkScopeInfo scopeInfo = do
    let disappearedBindings       = to DisappearedBindings       scopeInfo
        disappearedVariables      = to DisappearedVariables      scopeInfo
        appearedBindings          = to AppearedBindings          scopeInfo
        appearedVariables         = to AppearedVariables         scopeInfo
        stayedOutOfScopeVariables = to StayedOutOfScopeVariables scopeInfo
        stayedFreeVariables       = to StayedFreeVariables       scopeInfo
    checkEmpty OldBindingsDiscordWithOutOfScopeVariables $
        disappearedBindings `symmetricDifference` stayedOutOfScopeVariables
    checkEmpty OldBindingsDiscordWithBoundVariables $
        disappearedBindings `symmetricDifference` disappearedVariables
    checkEmpty NewBindingsDiscordWithBoundVariables $
        appearedBindings `symmetricDifference` appearedVariables
    checkEmpty OldBindingsClashWithFreeVariables $
        disappearedBindings `Set.intersection` stayedFreeVariables
    checkEmpty OldBindingsClashWithNewBindings $
        appearedBindings  `Set.intersection` disappearedBindings
    checkEmpty NewBindingsClashWithFreeVariabes $
        appearedBindings `Set.intersection` stayedFreeVariables

-- | Check if a renamer respects scoping.
checkRespectsScoping :: Scoping t => (t NameAnn -> t NameAnn) -> t ann -> Either ScopeError ()
checkRespectsScoping ren =
    checkScopeInfo <=< unScopeErrorOrInfo . collectScopeInfo . ren . runQuote . establishScoping
