{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Instance.Eq.Monad
    ( L (..)
    , R (..)
    , EqRename
    , ScopedEqRename
    , runEqRename
    , runScopedEqRename
    , withRenamedTwins
    , eqNameM
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Name
import           Language.PlutusCore.Rename.Monad

import           Control.Lens

newtype L a = L
    { unL :: a
    } deriving (Generic)

newtype R a = R
    { unR :: a
    } deriving (Generic)

data Bilateral a = Bilateral
    { _bilateralL :: a
    , _bilateralR :: a
    }

makeLenses ''Bilateral

instance Wrapped (L a)
instance Wrapped (R a)
instance HasUnique name unique => HasUnique (L name) (L unique)
instance HasUnique name unique => HasUnique (R name) (R unique)

instance Semigroup a => Semigroup (Bilateral a) where
    Bilateral l1 r1 <> Bilateral l2 r2 = Bilateral (l1 <> l2) (r1 <> r2)

instance Monoid a => Monoid (Bilateral a) where
    mempty = Bilateral mempty mempty

instance HasRenaming ren unique => HasRenaming (Bilateral ren) (L unique) where
    renaming = bilateralL . renaming . coerced @(Renaming unique)

instance HasRenaming ren unique => HasRenaming (Bilateral ren) (R unique) where
    renaming = bilateralR . renaming . coerced @(Renaming unique)

type EqRename ren = RenameT (Bilateral ren) Maybe ()
type ScopedEqRename = EqRename ScopedRenaming

runEqRename :: EqRename (Renaming unique) -> Bool
runEqRename = isJust . mrunRenameT

runScopedEqRename :: ScopedEqRename -> Bool
runScopedEqRename = isJust . mrunRenameT

-- | Note that this functions handles type-level names as well as term-level names.
withRenamedTwins
    :: (HasRenaming ren unique, HasUnique name unique, Monad m)
    => name -> name -> RenameT (Bilateral ren) m c -> RenameT (Bilateral ren) m c
withRenamedTwins name1 name2 k =
    withRenamedName (L name1) (L name2) $
    withRenamedName (R name2) (R name1) k

-- | Note that this functions handles type-level names as well as term-level names.
eqNameM
    :: (HasRenaming ren unique, HasUnique (name ann) unique, Eq unique)
    => name ann -> name ann -> EqRename ren
eqNameM name1 name2 = do
    mayUniq2' <- lookupNameM $ L name1
    mayUniq1' <- lookupNameM $ R name2
    let uniq1 = name1 ^. unique
        uniq2 = name2 ^. unique
    guard $ case (mayUniq1', mayUniq2') of
        (Nothing        , Nothing        ) -> uniq1 == uniq2
        (Just (R uniq1'), Just (L uniq2')) -> uniq1 == uniq1' && uniq2 == uniq2'
        (_              , _              ) -> False
