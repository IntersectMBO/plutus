{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE StrictData            #-}
{-# LANGUAGE TypeFamilies          #-}

-- | Relational joins for Haskell datatypes.
--
-- This code is cribbed from Gabriel Gonzalez's excellent blog.
-- See http://www.haskellforall.com/2014/12/a-very-general-api-for-relational-joins.html
module Plutus.PAB.Relation where

import           Control.Applicative (Alternative, empty, liftA2, (<|>))
import           Data.Map            (Map)
import qualified Data.Map            as Map
import           Data.Maybe          (catMaybes)
import           Data.Set            (Set)
import qualified Data.Set            as Set
import           Prelude             hiding (lookup)

data Keys k
    = All
    | Some (Set k)
    deriving (Show, Eq)

extract :: Keys a -> Maybe (Set a)
extract All      = Nothing
extract (Some s) = Just s

intersection :: Ord k => Keys k -> Keys k -> Keys k
intersection All ks              = ks
intersection ks All              = ks
intersection (Some xs) (Some ys) = Some (Set.intersection xs ys)

union :: Ord k => Keys k -> Keys k -> Keys k
union All _               = All
union _ All               = All
union (Some k1) (Some k2) = Some (Set.union k1 k2)

------------------------------------------------------------
data Table k v =
    Table
        { keys   :: Keys k
        , lookup :: k -> Maybe v
        }

instance Functor (Table k) where
    fmap f table = table {lookup = fmap f . lookup table}

instance Ord k => Applicative (Table k) where
    pure v = Table All (pure (pure v))
    Table s1 f <*> Table s2 x = Table (intersection s1 s2) (liftA2 (<*>) f x)

instance Ord k => Alternative (Table k) where
    empty = Table (Some Set.empty) (const Nothing)
    Table s1 f1 <|> Table s2 f2 = Table (union s1 s2) (\k -> f1 k <|> f2 k)

instance (Show k, Show v) => Show (Table k v) where
    show Table {keys, lookup} =
        case keys of
            All -> "<function>"
            Some ks ->
                unlines $
                catMaybes $ do
                    k <- Set.toList ks
                    pure $ show <$> lookup k

fromMap :: Ord k => Map k v -> Table k v
fromMap = fromList . Map.toList

fromList :: Ord k => [(k, v)] -> Table k v
fromList xs =
    Table {keys = Some $ Set.fromList $ Map.keys m, lookup = flip Map.lookup m}
  where
    m = Map.fromList xs
