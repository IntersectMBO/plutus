{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module UntypedPlutusCore.Core.Plated
    ( termConstants
    , termBinds
    , termVars
    , termUniques
    , termSubterms
    , termConstantsDeep
    , termSubtermsDeep
    , termUniquesDeep
    ) where

import PlutusCore.Core (HasUniques)
import PlutusCore.Name.Unique
import UntypedPlutusCore.Core.Type

import Control.Lens
import Universe

-- | Get all the direct constants of the given 'Term' from 'Constant's.
termConstants :: Traversal' (Term name uni fun ann) (Some (ValueOf uni))
termConstants f term0 = case term0 of
    Constant ann val -> Constant ann <$> f val
    Var{}            -> pure term0
    LamAbs{}         -> pure term0
    Error{}          -> pure term0
    Apply{}          -> pure term0
    Force{}          -> pure term0
    Delay{}          -> pure term0
    Builtin{}        -> pure term0
    Constr{}         -> pure term0
    Case{}           -> pure term0
    Let{}            -> pure term0
    Bind{}           -> pure term0

-- | Get all the direct child 'name a's of the given 'Term' from 'LamAbs'es.
termBinds :: Traversal' (Term name uni fun ann) name
termBinds f = \case
    LamAbs ann n t -> f n <&> \n' -> LamAbs ann n' t
    x              -> pure x

-- | Get all the direct child 'name a's of the given 'Term' from 'Var's.
termVars :: Traversal' (Term name uni fun ann) name
termVars f = \case
    Var ann n -> Var ann <$> f n
    x         -> pure x

-- | Get all the direct child 'Unique's of the given 'Term'.
termUniques :: HasUniques (Term name uni fun ann) => Traversal' (Term name uni fun ann) Unique
termUniques f = \case
    LamAbs ann n t -> theUnique f n <&> \n' -> LamAbs ann n' t
    Var ann n      -> theUnique f n <&> Var ann
    x              -> pure x

-- | Get all the direct child 'Term's of the given 'Term'.
termSubterms :: Traversal' (Term name uni fun ann) (Term name uni fun ann)
termSubterms f = \case
    LamAbs ann n t     -> LamAbs ann n <$> f t
    Apply ann t1 t2    -> Apply ann <$> f t1 <*> f t2
    Delay ann t        -> Delay ann <$> f t
    Force ann t        -> Force ann <$> f t
    Constr ann i args  -> Constr ann i <$> traverse f args
    Case ann arg cs    -> Case ann <$> f arg <*> traverse f cs
    Let ann names body -> Let ann names <$> f body
    Bind ann t binds   -> Bind ann <$> f t <*> traverse f binds
    e@Error {}         -> pure e
    v@Var {}           -> pure v
    c@Constant {}      -> pure c
    b@Builtin {}       -> pure b
{-# INLINE termSubterms #-}

-- | Get all the transitive child 'Constant's of the given 'Term'.
termConstantsDeep :: Fold (Term name uni fun ann) (Some (ValueOf uni))
termConstantsDeep = termSubtermsDeep . termConstants

-- | Get all the transitive child 'Term's of the given 'Term'.
termSubtermsDeep :: Fold (Term name uni fun ann) (Term name uni fun ann)
termSubtermsDeep = cosmosOf termSubterms

-- | Get all the transitive child 'Unique's of the given 'Term'.
termUniquesDeep :: HasUniques (Term name uni fun ann) => Fold (Term name uni fun ann) Unique
termUniquesDeep = termSubtermsDeep . termUniques
