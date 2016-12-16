{-# OPTIONS -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}





-- | This module defines a kind of abstract binding tree (ABT). It uses a type
-- similar to the 'Fix' type, but with an added constructor for variables, and
-- an intermediate type 'Scope' for representing (possibly empty) binders.
-- For uniformity, every argument to a construct is a 'Scope', even args that
-- normally aren't seen as scopes. For example, whereas normally you might
-- expect that a pair has the form @pair(M;N)@ (using the PFPL notation), with
-- these ABTs, it has the form @pair([].M;[].N)@ where the pair elements are
-- binders with an empty list of bound variables. This avoids the need to make
-- two different types available to the class of constructions, one for terms
-- and one for scopes.

module Utils.ABT where

import Utils.Vars

import Control.Monad.State
import Data.Bifunctor
import Data.Bitraversable
import qualified Data.Foldable as F
import Data.Functor.Classes
import Data.List (elemIndex)
import GHC.Generics







-- * Main types



-- | 'ABT' is like 'Fix', but with the addition of tools for binders. Like
-- 'Fix', we have a parameter 'f' for functors that define the shape of the
-- constructors for the type of interest. In this sense, then, the subset
-- of elements that have no variables and non-binding 'Scope's is just a
-- kind of least fixed point, in the F-algebra sense. The addition of
-- variables and scopes simply introduces new constructions in the right
-- places to represent binding. It's similar to the free monad construction,
-- but the variable parameter is fixed to be 'Variable'.
--
-- The particular choices for 'f' can be simple polynomial functors, such as
-- 
-- > data LC a = Pair a a | Fst a | Snd a | Lam a | App a a
--
-- as for the a simple lambda calculus with pairs and functions, or it can be
-- more complex, such as
--
-- > data LC a = ... | Con String [a] | Case a [(Pattern, a)]
--
-- which has constructed data (eg @Con "True" []@ for @True@), as well as
-- case expressions with a list of clauses, represented by pairs of patterns
-- and associated clause bodies.
--
-- The choice to represent ABTs as functors was to make this kind of
-- representation possible, without simultaneously forcing every kind of
-- construct (lists, clauses, etc.) into the ABT type.

data ABT f
  = Var Variable
  | In (f (Scope f))
  deriving (Generic)

deriving instance Show (f (Scope f)) => Show (ABT f)







-- | Three types of variables are used. 'Free' variables are for
-- user-supplied names that can be abstracted for binding, or can be left
-- free for use as names for defined terms, and other such things. 'Bound'
-- variables are de Bruijn indexes, and are used only in the scope of the
-- binder that binds the index. All both have string values that represent the
-- stored display name of the variable, for pretty printing.

data Variable
  = Free FreeVar
  | Bound String BoundVar
  | Meta MetaVar
  deriving (Show,Generic)


-- | The name of a variable.

name :: Variable -> String
name (Free (FreeVar n)) = n
name (Bound n _)        = n
name (Meta i)           = "?" ++ show i


-- | Equality of variables is by the parts which identify them, so names for
-- 'Free' variables, and identifying numbers for 'Bound'.

instance Eq Variable where
  Free x    == Free y    = x == y
  Bound _ i == Bound _ j = i == j
  Meta m    == Meta n    = m == n
  _         == _         = False







-- | A @Scope f@ is a list of bound variable names used for both display
-- purposes and to track how many bound variables there are, along with a
-- @ABT f@ for the body of the scope. a value @Scope ["x","y"] m@ corresponds
-- to a PFPL scope of the form @x,y.m@

data Scope f
  = Scope
      { names :: [String]
      , freeNames :: [FreeVar]
      , body :: ABT f
      }
  deriving (Generic)

deriving instance Show (f (Scope f)) => Show (Scope f)






-- * Translating ABTs between construction signatures



-- | When @f@ is a bifunctor, @ABT (f a)@ will be functorial in @a@. This lets
-- use use 'Scope' like we'd use 'Fix' — to define parameterized types such as
-- 'List' here:
--
-- @
--    data ListF a r = Nil | Cons a r
--    
--    type List a = Fix (ListF a)
-- @
--
-- and the result 'List' here is itself functorial. However, juggling the
-- relationships between 'Functor' and 'Bifunctor' to make this automatic
-- is tedious. We can define the derived map once and for all over 'Bifunctor'
-- without any concern for functor instances.

translate :: Bifunctor f
          => (forall r. f a r -> f b r)
          -> ABT (f a) -> ABT (f b)
translate _ (Var v) = Var v
translate n (In x) = In (n (second (translateScope n) x))


-- | Similarly, we can translate a scope, by just propogating the translation.

translateScope :: Bifunctor f
               => (forall r. f a r -> f b r)
               -> Scope (f a) -> Scope (f b)
translateScope n (Scope ns fns x) = Scope ns fns (translate n x)







-- * Folds over ABTs



-- | ABTs can be folded over whenever their parameter is a functor.

fold :: Functor f
     => (Variable -> a)  -- ^ The action on variables.
     -> (f a -> a)       -- ^ The action on recursive results.
     -> (Int -> a -> a)  -- ^ The action on scopes. The argument is the number
                         -- of variables bound by the scope.
     -> ABT f -> a
fold aVar _    _   (Var v) = aVar v
fold aVar aRec aSc (In x)  = aRec (fmap (foldScope aVar aRec aSc) x)


-- | Scopes can also be folded over.

foldScope :: Functor f
          => (Variable -> a)  -- ^ The action on variables.
          -> (f a -> a)       -- ^ The action on recursive results.
          -> (Int -> a -> a)  -- ^ The action on scopes. The argument is the
                              -- number of variables bound by the scope.
          -> Scope f -> a
foldScope aVar aRec aSc (Scope ns _ b) =
  aSc (length ns) (fold aVar aRec aSc b)







-- * Free variables in an ABT



-- | A term has some specified free variables. We can compute these whenever
-- the constructions form a 'Foldable' instance.

freeVars :: (Functor f, Foldable f) => ABT f -> [FreeVar]
freeVars = fold fvAlgV fvAlgRec fvAlgSc
  where
    fvAlgV (Free n) = [n]
    fvAlgV _        = []
    
    fvAlgRec :: Foldable f => f [FreeVar] -> [FreeVar]
    fvAlgRec = foldMap id
    
    fvAlgSc :: Int -> [FreeVar] -> [FreeVar]
    fvAlgSc _ ns = ns




-- | 'freeVarNames' just gives back the free names for the free vars.

freeVarNames :: (Functor f, Foldable f) => ABT f -> [String]
freeVarNames = map (\(FreeVar n) -> n) . freeVars





-- | The 'BinderNameSource' class captures the idea that some data constitutes
-- a source for names in binders. For instance, the raw name in a lambda
-- expression, or a pattern in a case expression, are both sources of names
-- for a binding construct. The fundamental characteristic of such things is
-- that they can have dummy variables which in concrete syntax are just
-- underscores, but which ought to be converted into fresh names before an
-- actual scope is formed. For example, @\_ -> M@ should become @\x -> M@ for
-- some @x@ that's not used in @M@. Or similarly, the clause @Foo _ _ -> M@
-- should become @Foo x x' -> M@ again where @x@ and @x'@ are not in @M@. The
-- 'BinderNameSource' class represents this functionality.
--
-- These tools should be used during parse time to ensure that the result of
-- parsing is always something sensible wrt dummy variables.

class BinderNameSource a where
  sourceNames :: a -> [String]
  replaceDummies :: a -> [String] -> (a,[String])





-- | A 'BinderNameSource' can have its dummy variables swapped for fresh names
-- by getting its names, finding out how many dummies there are, generating
-- that many fresh names, and then replacing the dummies.

dummiesToFreshNames :: BinderNameSource a => [String] -> a -> a
dummiesToFreshNames ns x =
  let varNames = sourceNames x
      dummies = filter ("_"==) varNames
      newNamesToFreshen = take (length dummies) (repeat "x")
      freshNames = freshen ns newNamesToFreshen
  in fst (replaceDummies x freshNames)





-- | A utility type to block generative instances.

data BNSString = BNSString { unBNSString :: String }





-- | A string is a 'BinderNameSource' in a trivial way.

instance BinderNameSource BNSString where
  sourceNames (BNSString x) = [x]
  replaceDummies (BNSString "_") (n:ns) = (BNSString n,ns)
  replaceDummies x ns = (x,ns)





-- | A foldable traversable functor of 'BinderNameSource's is also a
-- 'BinderNameSource'.

instance (Functor f, Foldable f, Traversable f, BinderNameSource a)
      => BinderNameSource (f a) where
  sourceNames xs = F.fold (fmap sourceNames xs)
  replaceDummies xs ns =
    runState (traverse (state . replaceDummies) xs) ns





-- | An 'ABT f' is a 'BinderNameSource' provided that 'f' is a foldable
-- traversable functor. Then the names are just the 'freeVars'.

instance (Functor f, Foldable f, Traversable f)
      => BinderNameSource (ABT f) where
  sourceNames x = [ n | FreeVar n <- freeVars x ]
  replaceDummies x0 ns0 = runState (go x0) ns0
    where
      go (Var (Free (FreeVar "_"))) =
        do n <- nextItem
           return (Var (Free (FreeVar n)))
      go (Var v) = return (Var v)
      go (In x) = In <$> traverse (underF go) x
      
      nextItem :: State [a] a
      nextItem = state (\(a:as) -> (a,as))









-- * Shifting bound variables



-- | The 'shift' function appropriately increments a term's free variables,
-- to handle substitution under binders. Any bound variable inside a term
-- that gets substituted under a binder needs to still point to its own
-- binder higher up, or else it'll be captured. The @l@ argument of 'shift'
-- represents how many bound variables in the substituted term the 'shift' has
-- passed under, while the @i@ represents how many new bound variables there
-- are in the scope that's being substituted into. We use @l-1@ in the
-- condition because if there are @l@ many bound vars, than the index for the
-- binders are the numbers in the range @[0..l-1]@, so any bound var above that
-- range points to a higher binder.
--
-- For example, consider the function term @λx. (λy.λz.y) x@. This can
-- be normalized to @λx.λz.x@ by beta reducing the inner application.
-- To do this, we need to substitute @x@ for @y@ in @λz.y@. But @x@ is a
-- bound variable, bound by the outer lambda, so we need to avoid capture, by
-- shifting it appropriately. With de Bruijn indices, want to turn the term
-- @λ.(λ.λ.1)0@ into the term @λ.λ.1@. The index for @x@ has to shift from @0@
-- to @1@ because it's being used under the binder for @z@. This is what the
-- @i@ argument to 'shift' represents.
--
-- Similarly, if we had also put a binder around @x@, as in the term
-- @λx. (λy.λz.y) (λw.x)@ we need to track that as well. This should normalize
-- to @λx.λz.λw.x@. With de Bruijn indices, @λ. (λ.λ.1) (λ.1)@ should become
-- the term @λ.λ.λ.2@. The variable @x@ initially was coded as @1@, but shifts
-- to @2@, as expected. However, if we had normalized @λx. (λy.λz.y) (λw.w)@
-- which with de Bruijn indexes is @λ. (λ.λ.1) (λ.0)@, we expect to get back
-- @λx.λz.λw.w@ which with de Bruin indexes is @λ.λ.λ.0@. Notice that although
-- the variable @w@ corresponds to the index @0@, the 'shift' function must
-- leave it unchanged. So not all bound variables are shifted, only those that
-- were bound outside of any new binders that 'shift' passes under. This is
-- what the variable @l@ represents in 'shift'.

shift :: Functor f => Int -> Int -> ABT f -> ABT f
shift l i (Var (Bound n (BoundVar v))) | v > l-1 =
  Var (Bound n (BoundVar (v+i)))
shift _ _ (Var v) = Var v
shift l i (In x) = In (fmap (shiftScope l i) x)



-- | When shifting a scope, we keep track of the number of new variables that
-- are brought into scope, so the number of variables bound by the scope is
-- added to the current value of @l@ in the recursive call.

shiftScope :: Functor f => Int -> Int -> Scope f -> Scope f
shiftScope l i (Scope ns fns x) = Scope ns fns (shift (l+length ns) i x)







-- * Unshifting bound variables



-- | Just as we need to shift, sometimes we also need to unshift. In this
-- case, for evaluation under binders so that a variable bound outside its
-- nearest binder still points appropriately. For example, consider
-- @λx. (λy.x) c@, which corresponds to the de Bruijn term @λ. (λ.1) c@. If we
-- evaluate under the binder, we expect to get @λx.x@ because @[c/y]x = x@,
-- which is the de Bruijn term @λ.0@. The index @1@ in the original had to be
-- unshifted down to @0@ because its enclosing binder was removed.
--
-- In the function 'unshift', the argument @l@ indicates the number of bound
-- variables that were in scope before the relevant outer scope was removed.
-- This includes the original variables bound by the now-removed scope, and
-- any variables bound by binders inside that scope that have been passed
-- under by 'unshift'. A variable in the relevant range will be left
-- un-altered, because either it's been instantiated out of existence or its
-- binder is still present. A variable outside the range will be reduced by
-- @i@, which represents the number of variables bound by the now-removed
-- binder.

unshift :: Functor f => Int -> Int -> ABT f -> ABT f
unshift l i (Var (Bound n (BoundVar v))) | v > l-1 =
  Var (Bound n (BoundVar (v-i)))
unshift _ _ (Var v) = Var v
unshift l i (In x) = In (fmap (unshiftScope l i) x)



-- | When unshifting a scope, we keep track of the number of new variables
-- that are brought into scope, so the number of variables bound by the scope
-- is added to the current value of @l@ in the recursive call.

unshiftScope :: Functor f => Int -> Int -> Scope f -> Scope f
unshiftScope l i (Scope ns fns x) = Scope ns fns (unshift (l+length ns) i x)







-- * Binding a free variable



-- | We bind variables by replacing them with an appropriately named 'Bound'.
-- The argument @l@ tracks how many binders we've recursed under.

bind :: (Functor f, Foldable f) => Int -> [FreeVar] -> ABT f -> ABT f
bind _ [] x = x
bind l ns (Var v@(Free n)) =
  case elemIndex n ns of
    Nothing -> Var v
    Just i -> Var (Bound (name v) (BoundVar (l + i)))
bind _ _ (Var v) = Var v
bind l ns (In x) = In (fmap (bindScope l ns) x)



-- | We also can bind scopes. As before, @l@ tracks new variables.

bindScope :: (Functor f, Foldable f) => Int -> [FreeVar] -> Scope f -> Scope f
bindScope _ [] sc = sc
bindScope l ns (Scope ns' _ b) =
  Scope ns' fv b'
  where
    b' = bind (l + length ns') ns b
    fv = freeVars b'







-- * Unbinding a bound variable



-- | We unbind by doing the opposite of binding, replacing bound variables
-- with free variables.

unbind :: (Functor f, Foldable f) => Int -> [FreeVar] -> ABT f -> ABT f
unbind _ [] x = x
unbind l ns (Var (Bound n (BoundVar i))) =
  if i < l  -- i is a locally bound variable
  then Var (Bound n (BoundVar i))
  else if i >= l + length ns  -- i is bound outside the variables to replace
  then Var (Bound n (BoundVar i))
  else Var (Free (ns !! (i - l)))
unbind _ _ (Var v) = Var v
unbind l ns (In x) = In (fmap (unbindScope l ns) x)



-- | We also can unbind scopes.

unbindScope :: (Functor f, Foldable f)
            => Int -> [FreeVar] -> Scope f -> Scope f
unbindScope l ns (Scope ns' _ b) =
  Scope ns' fv b'
  where
    b' = unbind (l + length ns') ns b
    fv = freeVars b'







-- * Smart constructors



-- | A smart constructor that creates a @Scope f@ while also performing actual
-- binding of free variables. This also calculates the remaining free
-- variables in the body of the scope and stores them.

scope :: (Functor f, Foldable f) => [String] -> ABT f -> Scope f
scope ns b = Scope { names = ns
                   , freeNames = freeVars b'
                   , body = b'
                   }
  where b' = bind 0 (map FreeVar ns) b


-- | Descoping a scope involves reversing the actions of 'scope' that made it.
-- However, because a scope's names might conflict with the free variables in
-- the scope body, we need to rename them first, before unbinding. 'descope'
-- also returns the fresh names.

descope :: (Functor f, Foldable f) => Scope f -> ([String], ABT f)
descope (Scope ns fns b) = (freshNs, unbind 0 (map FreeVar freshNs) b)
  where freshNs = freshen [ n | FreeVar n <- fns ] ns







-- * Substitution



-- | Substitution on ABTs just looks up variables, and recurses into scopes.
-- We do however need to track how many binders we've passed under in order to
-- shift free variables.

subst :: (Functor f, Foldable f) => Int -> [(FreeVar, ABT f)] -> ABT f -> ABT f
subst l subs (Var (Free n)) =
  case lookup n subs of
    Nothing -> Var (Free n)
    Just x -> shift 0 l x
subst _ _ (Var v) = Var v
subst l subs (In x) = In (fmap (substScope l subs) x)



-- | Substitution for scopes is similarly simple.

substScope :: (Functor f, Foldable f)
           => Int -> [(FreeVar, ABT f)] -> Scope f -> Scope f
substScope l subs (Scope ns _ b) =
  Scope ns (freeVars b') b'
  where b' = subst (l + length ns) subs b







-- * Instantiation of scopes



-- | Instantiating a scope simply means substituting an appropriate number
-- of terms in for the variables bound by the scope. The resulting term has to
-- be unshifted by the number of variables now removed by instantiation,
-- because some of the terms inside the result might be variables bound by a
-- scope higher than the one being instantiated.

instantiate :: (Functor f, Foldable f) => Scope f -> [ABT f] -> ABT f
instantiate (Scope ns fns b) xs
  | length ns /= length xs =
      error "Cannot instantiate along differing numbers of arguments."
  | null ns = b
  | otherwise = subst 0 subs (unshift l l b')
    where
      l = length xs
      (freshNs, b') = descope (Scope ns fns b)
      subs = zip (map FreeVar freshNs) xs


-- | A convenience function for instantiating at exactly no arguments.

instantiate0 :: (Functor f, Foldable f) => Scope f -> ABT f
instantiate0 a = instantiate a []







-- * Utility functions



-- | We can apply functions under a binder without disturbing the binding.

under :: (ABT f -> ABT f) -> Scope f -> Scope f
under f (Scope ns fns b) = Scope ns fns (f b)


-- | A functor-lifted version of 'under'

underF :: Functor m => (ABT f -> m (ABT f)) -> Scope f -> m (Scope f)
underF f (Scope ns fns b) = Scope ns fns <$> f b


-- | A convenience function that makes it easier to do iterated binding.

helperFold :: (a -> b -> b) -> [a] -> b -> b
helperFold c xs n = foldr c n xs


-- | It's desirable to distinguish between free variables and names for
-- defined terms. To do this for a "complete" term, one which is about to be
-- elaborated, we can replace all free variables in the term at once, by
-- applying a function that wraps them with a supplied function. The function
-- should basically turn @Free n@ into @In (Defined n)@ or some equivalent
-- term that represents the name of a defined term.

freeToDefined :: (Functor f, Foldable f)
              => (String -> ABT f) -> ABT f -> ABT f
freeToDefined d (Var (Free (FreeVar n))) = d n
freeToDefined _ (Var v) = Var v
freeToDefined d (In x) = In (fmap (freeToDefinedScope d) x)


-- | Similarly, we can swap out the free variables in scopes.

freeToDefinedScope :: (Functor f, Foldable f)
                   => (String -> ABT f) -> Scope f -> Scope f
freeToDefinedScope d (Scope ns _ b) =
  Scope ns [] (freeToDefined d b)







-- * Operations with Metavariables



-- | Just as free variables can be substituted for, metasvariables can too.
-- Since metavariables are in some sense always free, their substitution is
-- much simpler.

substMetas :: (Functor f, Foldable f) => [(MetaVar, ABT f)] -> ABT f -> ABT f
substMetas [] x = x
substMetas subs (Var (Meta m)) =
  case lookup m subs of
    Nothing -> Var (Meta m)
    Just x -> x
substMetas _ (Var v) =
  Var v
substMetas subs (In x) =
  In (fmap (substMetasScope subs) x)


-- | We need to also be able to substitute metavariables in scopes.

substMetasScope :: (Functor f, Foldable f)
                => [(MetaVar, ABT f)] -> Scope f -> Scope f
substMetasScope subs sc = substMetas subs `under` sc


-- | We can perform occurs checks on ABTs by using the generic ABT fold.

occurs :: (Functor f, Foldable f) => MetaVar -> ABT f -> Bool
occurs m x = fold ocAlgV ocAlgRec ocAlgSc x
  where
    ocAlgV :: Variable -> Bool
    ocAlgV (Meta m') = m == m'
    ocAlgV _ = False
    
    ocAlgRec :: Foldable f => f Bool -> Bool
    ocAlgRec = F.foldl' (||) False
    
    ocAlgSc :: Int -> Bool -> Bool
    ocAlgSc _ b = b


-- | We can get a list of the metavars in an ABT.

metaVars :: (Functor f, Foldable f) => ABT f -> [MetaVar]
metaVars = fold mvAlgV mvAlgRec mvAlgSc
  where
    mvAlgV (Meta n) = [n]
    mvAlgV _        = []
    
    mvAlgRec :: Foldable f => f [MetaVar] -> [MetaVar]
    mvAlgRec = foldMap id
    
    mvAlgSc :: Int -> [MetaVar] -> [MetaVar]
    mvAlgSc _ ns = ns






-- * Equality


instance Eq1 f => Eq (ABT f) where
  Var x == Var y = x == y
  In x == In y = eq1 x y
  _ == _ = False


instance Eq1 f => Eq (Scope f) where
  Scope ns _ x == Scope ns' _ y =
    length ns == length ns' && x == y







-- * Zipping



-- | This class defines a generic notion of bifunctorial zipping.

class Bizippable f where
  bizip :: f a b -> f a' b' -> Maybe ( [(a,a')], [(b,b')] )


-- | For a bizppable @f@, we can zip an @ABT (f a)@ with an @ABT (f b)@ by
-- pairing up the @a@s and the @b@s, provided that the 'ABT' structure is
-- the same in both.

zipABTF :: Bizippable f => ABT (f a) -> ABT (f b) -> Maybe [(a,b)]
zipABTF (Var x) (Var y)
  | x == y    = Just []
  | otherwise = Nothing
zipABTF (In x) (In y) =
  do (zippedABs, zippedScope) <- bizip x y
     zippedABss <- mapM (uncurry zipScopeF) zippedScope
     return $ zippedABs ++ concat zippedABss
zipABTF _ _ = Nothing


zipScopeF :: Bizippable f => Scope (f a) -> Scope (f b) -> Maybe [(a,b)]
zipScopeF (Scope ns _ x) (Scope ns' _ y)
  | length ns == length ns' = zipABTF x y
  | otherwise = Nothing







-- * Traversing



bisequenceABTF :: (Applicative f, Bitraversable g)
               => ABT (g (f a)) -> f (ABT (g a))
bisequenceABTF (Var v) = pure (Var v)
bisequenceABTF (In x) = In <$> bitraverse id bisequenceScopeF x


bisequenceScopeF :: (Applicative f, Bitraversable g)
                 => Scope (g (f a)) -> f (Scope (g a))
bisequenceScopeF (Scope ns fns x) = Scope ns fns <$> bisequenceABTF x