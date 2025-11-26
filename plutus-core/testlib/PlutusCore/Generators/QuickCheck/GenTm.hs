-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusCore.Generators.QuickCheck.GenTm
  ( module PlutusCore.Generators.QuickCheck.GenTm
  , module Export
  , Arbitrary (..)
  , Gen
  ) where

import PlutusCore.Generators.QuickCheck.Common
import PlutusCore.Generators.QuickCheck.Utils

import PlutusCore.Default
import PlutusCore.Name.Unique
import PlutusIR
import PlutusIR.Compiler
import PlutusIR.Subst

import Control.Monad.Reader
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Set.Lens (setOf)
import Data.String
import Test.QuickCheck (Arbitrary (..), Gen)
import Test.QuickCheck qualified as QC
import Test.QuickCheck.GenT as Export hiding (var)

instance MonadReader r m => MonadReader r (GenT m) where
  ask = lift ask
  local f (GenT k) = GenT $ \qc size -> local f $ k qc size

{-| Term generators carry around a context to know
e.g. what types and terms are in scope. -}
type GenTm = GenT (Reader GenEnv)

data GenEnv = GenEnv
  { geAstSize :: Int
  -- ^ Generator size bound. See Note [Recursion Control and geAstSize]
  , geDatas :: Map TyName (Datatype TyName Name DefaultUni ())
  {-^ Datatype context.
  TODO: it's a little weird, 'cause it maps the datatype name to the datatype and the datatype
  introduces multiple names. It's probably fine to have something like that, though. -}
  , geTypes :: TypeCtx
  -- ^ Type context
  , geTerms :: Map Name (Type TyName DefaultUni ())
  -- ^ Term context
  , geUnboundUsedTyNames :: Set TyName
  -- ^ Names that we have generated and don't want to shadow but haven't bound yet.
  , geEscaping :: AllowEscape
  -- ^ Are we in a place where we are allowed to generate a datatype binding?
  , geCustomGen
      :: Maybe (Type TyName DefaultUni ())
      -- TODO: this could return a `Maybe` perhaps. Or it
      -- could be `Maybe (Maybe Type -> ...)`.
      -> GenTm (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
  {-^ A custom user-controlled generator for terms - useful for situations where
  we want to e.g. generate custom strings for coverage or test some specific
  pattern that generates a special case for the compiler. -}
  , geCustomFreq :: Int
  {-^ How often do we use the custom generator -
  values in the range of 10-30 are usually reasonable. -}
  , geDebug :: Bool
  -- ^ Are we currently running in debug-mode (to debug our generators)
  }

{- Note [Recursion Control and geAstSize]
One would be forgiven for thinking that you don't need `geAstSize` in `GenTm` because size is
built-in to 'Gen'. However, if you use 'Gen's built-in size to control the size of both the terms
you generate *and* the size of the constants in the terms you will end up with skewed
terms. Constants near the top of the term will be big and constants near the bottom of the term will
be small. For this reason we follow QuickCheck best practice and keep track of the "recursion
control size" separately from 'Gen's size in the 'geAstSize' field of the 'GenEnv'
environment. I.e. we let the QuickCheck's size parameter to be responsible for the size of constants
at the leaves of the AST and use 'geAstSize' to control the size of the AST itself.
-}

-- | Run a generator in debug-mode.
withDebug :: GenTm a -> GenTm a
withDebug gen = local (\env -> env {geDebug = True}) gen

{-| Run a `GenTm  generator in a top-level empty context where we are allowed to generate
datatypes. -}
runGenTm :: GenTm a -> Gen a
runGenTm = runGenTmCustom 0 (error "No custom generator.")

{-| Run a `GenTm` generator with a plug-in custom generator for terms that is included with
the other generators. -}
runGenTmCustom
  :: Int
  -> ( Maybe (Type TyName DefaultUni ())
       -> GenTm (Type TyName DefaultUni (), Term TyName Name DefaultUni DefaultFun ())
     )
  -> GenTm a
  -> Gen a
runGenTmCustom f cg g = do
  sized $ \n -> do
    let env =
          GenEnv
            { -- Duplicating the QC size parameter that we use to control the size of constants as
              -- the initial AST size parameter.
              geAstSize = n
            , geDatas = Map.empty
            , geTypes = Map.empty
            , geTerms = Map.empty
            , geUnboundUsedTyNames = Set.empty
            , geEscaping = YesEscape
            , geCustomGen = cg
            , geCustomFreq = f
            , geDebug = False
            }
    flip runReader env <$> runGenT g

{-| Create a generator that runs the given generator and applies the given function to produced
values until the result is a @Just y@, returning the @y@. -}
suchThatMap :: Monad m => GenT m a -> (a -> Maybe b) -> GenT m b
gen `suchThatMap` f = fmap fromJust $ fmap f gen `suchThat` isJust

{-| Create a generator that runs the given generator until the result is a @Just x@,
returning the @x@. -}
deliver :: Monad m => GenT m (Maybe a) -> GenT m a
deliver gen = gen `suchThatMap` id

-- * Utility functions

-- | Don't allow types to escape from a generator.
withNoEscape :: GenTm a -> GenTm a
withNoEscape = local $ \env -> env {geEscaping = NoEscape}

-- * Dealing with size

-- | Map a function over the generator size
onAstSize :: (Int -> Int) -> GenTm a -> GenTm a
onAstSize f = local $ \env -> env {geAstSize = f (geAstSize env)}

{-| Default to the first generator if the size is zero (or negative),
use the second generator otherwise. -}
ifAstSizeZero :: GenTm a -> GenTm a -> GenTm a
ifAstSizeZero ifZ nonZ = do
  n <- asks geAstSize
  if n <= 0 then ifZ else nonZ

-- | Locally set the size in a generator
withAstSize :: Int -> GenTm a -> GenTm a
withAstSize = onAstSize . const

{-| Split the size between two generators in the ratio specified by
the first two arguments. -}
astSizeSplit_ :: Int -> Int -> GenTm a -> GenTm b -> GenTm (a, b)
astSizeSplit_ a b ga gb = astSizeSplit a b ga (const gb)

{-| Split the size between two generators in the ratio specified by
the first two arguments and use the result of the first generator
in the second. -}
astSizeSplit :: Int -> Int -> GenTm a -> (a -> GenTm b) -> GenTm (a, b)
astSizeSplit a b ga gb = do
  n <- asks geAstSize
  let na = (a * n) `div` (a + b)
      nb = (b * n) `div` (a + b)
  x <- withAstSize na ga
  (,) x <$> withAstSize nb (gb x)

-- * Names

{- Note [Chaotic Good fresh name generation]
Currently we don't use 'Quote' for generating fresh names in the QuickCheck generators. It's mostly
for historical reasons and it's very non-trivial to change the current alignment to use 'Quote' at
this point. It does have positive sides to it, though, which we'll discuss below.

So what we do right now is track all names that are in the scope (not all actually and not in the
scope, more on that later, for now let's pretend the statement is correct) in separate maps:

- one for type names
- one for term names
- one for datatype-associated names (the name of the data type, its matcher and constructors)

and all these maps are processed in a linear fashion each time we need to generate a bunch of fresh
names. The processing is done via collecting in a set all uniques of names found in the maps: the
key sets of all the three maps and the names in the elements of the data map. Why do we need the
latter given that the names there are present as keys in the term map? No idea.

What makes it hard to change the current alignment to use 'Quote' is that names are generated all
over the place and put into the current context, inside and outside of the 'GenTm' monad. Any
operation on the context automatically makes the name generation machinery aware of the changes,
because the machinery looks at the whole context each time. It's really hard to move all of that to
run in 'Quote' simply because it’s trivial to miss a call here and there and types don't help much.

Another challenge is that the current fresh name generation is pretty fancy and doesn’t just always
pick the next fresh name. It can pick the next 10th fresh name, then go back, then again forward etc
– all of that between different calls to the function generating fresh names. We want to keep this
logic as it allows us to produce more diverse terms. We probably can simulate this kind of logic
with 'Quote', but it's non-trivial for sure.

Finally, we do not have any function that generates a definitely fresh name or a function that
generates a definitely non-fresh name -- both for very technical reasons (see the docs inline).
This likely isn't intentional, but it's hard to change that at this point and we don't care much
anyway, name clashes are fine. Moreover, the term map rather than containing all term names that
are in the scope only contains those that can be correctly inserted into the program (i.e. don't
reference shadowed type variables in their type). However the data map isn't filtered the same way
as the term map and so there can be constructors whose type references shadowed type variables,
which we never notice because those are only used for fresh name generation... which I guess is how
looking at the elements of the data map isn't redundant in the end.

Overall, this chaotic goodness needs to be sorted out.
-}

-- | Get all uniques we have generated and are used in the current context.
getUniques :: GenTm (Set Unique)
getUniques = do
  GenEnv {geDatas = dts, geTypes = tys, geTerms = tms, geUnboundUsedTyNames = used} <- ask
  return $
    Set.mapMonotonic (_nameUnique . unTyName) (Map.keysSet dts <> Map.keysSet tys <> used)
      <> Set.mapMonotonic _nameUnique (Map.keysSet tms)
      <> Set.unions [names d | d <- Map.elems dts]
  where
    names (Datatype _ _ _ m cs) = Set.fromList $ _nameUnique m : [_nameUnique c | VarDecl _ c _ <- cs]

{- Note [Warning about generating fresh names]
Since 'GenTm' is a *reader* monad names are not immediately put into any state when generated.
In order to bind generated names you need to use functions like 'bindTyName' and 'bindTmName', e.g.

    genLam k1 k2 = do
        x <- genMaybeFreshTyName "a"
        --                                              v--- LOOK HERE!
        fmap (TyLam () x k1) $ onAstSize (subtract 1) $ bindTyName x k1 (genType k2)
-}

-- | Generate a likely fresh name. See Note [Warning about generating fresh names].
genLikelyFreshName :: String -> GenTm Name
genLikelyFreshName s = head <$> genLikelyFreshNames [s]

-- See Note [Chaotic Good fresh name generation].
-- See Note [Warning about generating fresh names].
{-| Generate one likely fresh name per string in the input list.
Note that this may not give you a fresh name, if it happens to generate a name that was removed
from the terms map in 'bindTyName' (due to referencing a now-shadowed type variable) but is still
in the scope. -}
genLikelyFreshNames :: [String] -> GenTm [Name]
genLikelyFreshNames ss = do
  used <- getUniques
  let i = fromEnum $ Set.findMax $ Set.insert (Unique 0) used
      js = [j | j <- [1 .. i], not $ Unique j `Set.member` used]
      is = js ++ take (length ss + 10) [i + 1 ..]
  is' <- liftGen $ QC.shuffle is
  return [Name (fromString $ s ++ show j) (toEnum j) | (s, j) <- zip ss is']

-- | Same as 'genLikelyFreshName', except gives you a 'TyName'.
genLikelyFreshTyName :: String -> GenTm TyName
genLikelyFreshTyName s = TyName <$> genLikelyFreshName s

-- | Same as 'genLikelyFreshNames', except gives you 'TyName's.
genLikelyFreshTyNames :: [String] -> GenTm [TyName]
genLikelyFreshTyNames ss = map TyName <$> genLikelyFreshNames ss

-- See Note [Chaotic Good fresh name generation].
{-| Generate a name that likely overlaps with existing names on purpose. If there are no existing
names, generate a fresh name. This function doesn't distinguish between the type- and term-level
scopes, hence it may generate a 'Name' \"clashing\" with a previously generated 'TyName' and not
clashing with any previously generated 'Name'. Which is a good thing, because we want to check
that Plutus is able to handle such spurious name clashes. Generating weird stuff is useful for a
testing machinery! We don't need any \"definitely non-fresh name\" anyway, since we get enough
non-fresh names already. -}
genLikelyNotFreshName :: String -> GenTm Name
genLikelyNotFreshName s = do
  used <- Set.toList <$> getUniques
  case used of
    [] -> genLikelyFreshName s
    _ -> liftGen $ elements [Name (fromString $ s ++ show (unUnique i)) i | i <- used]

{-| Generate a fresh name most (roughly 75%) of the time and otherwise
generate an already bound name. When there are no bound names generate a fresh name. -}
genMaybeFreshName :: String -> GenTm Name
genMaybeFreshName s = frequency [(3, genLikelyFreshName s), (1, genLikelyNotFreshName s)]

-- | See `genMaybeFreshName`
genMaybeFreshTyName :: String -> GenTm TyName
genMaybeFreshTyName s = TyName <$> genMaybeFreshName s

-- | Bind a type name to a kind and avoid capturing free type variables.
bindTyName :: TyName -> Kind () -> GenTm a -> GenTm a
bindTyName x k = local $ \e ->
  e
    { geTypes = Map.insert x k (geTypes e)
    , -- See Note [Chaotic Good fresh name generation].
      geTerms = Map.filter (\ty -> not $ x `Set.member` setOf ftvTy ty) (geTerms e)
    , geDatas = Map.delete x (geDatas e)
    }

-- | Bind type names
bindTyNames :: [(TyName, Kind ())] -> GenTm a -> GenTm a
bindTyNames = flip $ foldr (uncurry bindTyName)

{-| Remember that we have generated a type name locally but don't bind it.
Useful for non-recursive definitions where we want to control name overlap. -}
registerTyName :: TyName -> GenTm a -> GenTm a
registerTyName n = local $ \e -> e {geUnboundUsedTyNames = Set.insert n (geUnboundUsedTyNames e)}

-- | Bind a term to a type in a generator.
bindTmName :: Name -> Type TyName DefaultUni () -> GenTm a -> GenTm a
bindTmName x ty = local $ \e -> e {geTerms = Map.insert x ty (geTerms e)}

-- | Bind term names
bindTmNames :: [(Name, Type TyName DefaultUni ())] -> GenTm a -> GenTm a
bindTmNames = flip $ foldr (uncurry bindTmName)

-- | Create a fresh term name, bind it to a type, and use it in a generator.
bindLikelyFreshTmName :: String -> Type TyName DefaultUni () -> (Name -> GenTm a) -> GenTm a
bindLikelyFreshTmName name ty k = do
  x <- genLikelyFreshName name
  bindTmName x ty (k x)

-- | Bind a datatype declaration in a generator.
bindDat
  :: Datatype TyName Name DefaultUni ()
  -> GenTm a
  -> GenTm a
bindDat dat@(Datatype _ (TyVarDecl _ a k) _ _ _) cont =
  bindTyName a k $
    local (\e -> e {geDatas = Map.insert a dat (geDatas e)}) $
      foldr (uncurry bindTmName) cont (matchType dat : constrTypes dat)

-- | Bind a binding.
bindBind
  :: Binding TyName Name DefaultUni DefaultFun ()
  -> GenTm a
  -> GenTm a
bindBind (DatatypeBind _ dat) = bindDat dat
bindBind (TermBind _ _ (VarDecl _ x ty) _) = bindTmName x ty
-- TODO: We should generate type bindings
bindBind _ = error "unreachable"

-- | Bind multiple bindings
bindBinds :: Foldable f => f (Binding TyName Name DefaultUni DefaultFun ()) -> GenTm a -> GenTm a
bindBinds = flip (foldr bindBind)
