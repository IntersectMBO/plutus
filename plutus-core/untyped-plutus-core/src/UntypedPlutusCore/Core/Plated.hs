{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module UntypedPlutusCore.Core.Plated
    ( termBinds
    , termVars
    , termUniques
    , termSubterms
    , termSubtermsDeep
    , termUniquesDeep
    ) where

import           PlutusCore.Core             (HasUniques)
import           PlutusCore.Name
import           UntypedPlutusCore.Core.Type

import           Control.Lens

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

{-# INLINE termSubterms #-}
-- | Get all the direct child 'Term's of the given 'Term'.
termSubterms :: Traversal' (Term name uni fun ann) (Term name uni fun ann)
termSubterms f = \case
    LamAbs ann n t  -> LamAbs ann n <$> f t
    Apply ann t1 t2 -> Apply ann <$> f t1 <*> f t2
    Delay ann t     -> Delay ann <$> f t
    Force ann t     -> Force ann <$> f t
    e@Error {}      -> pure e
    v@Var {}        -> pure v
    c@Constant {}   -> pure c
    b@Builtin {}    -> pure b

-- | Get all the transitive child 'Term's of the given 'Term'.
termSubtermsDeep :: Fold (Term name uni fun ann) (Term name uni fun ann)
termSubtermsDeep = cosmosOf termSubterms

-- | Get all the transitive child 'Unique's of the given 'Term'.
termUniquesDeep :: HasUniques (Term name uni fun ann) => Fold (Term name uni fun ann) Unique
termUniquesDeep = termSubtermsDeep . termUniques
