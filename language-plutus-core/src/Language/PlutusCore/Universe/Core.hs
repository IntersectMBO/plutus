{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE QuantifiedConstraints     #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TemplateHaskell #-}

module Language.PlutusCore.Universe.Core
    ( Some (..)
    , In (..)
    , Of (..)
    , SomeIn
    , SomeOf
    , someValue
    , Includes (..)
    , Closed (..)
    , type (<:)
    , knownUniOf
    , GEq (..)
    , (:~:) (..)
    , GShow (..)
    , gshow
    ) where

import           Control.DeepSeq
import           Control.Monad
import           Data.GADT.Compare
import           Data.GADT.Show
import           Data.Hashable
import           Data.List
import           Data.Proxy
import           Data.Text.Prettyprint.Doc (Pretty (..))
import           GHC.Exts

data Some f = forall a. Some (f a)

newtype In uni a = In (uni a)

data Of uni a = Of (uni a) a

type SomeIn uni = Some (In uni)
type SomeOf uni = Some (Of uni)

-- We probably want to use that together with `fastsum`.
class uni `Includes` a where
    knownUni :: uni a

knownUniOf :: uni `Includes` a => proxy a -> uni a
knownUniOf _ = knownUni

someValue :: forall a uni. uni `Includes` a => a -> SomeOf uni
someValue = Some . Of knownUni

class Closed uni where
    type Everywhere uni (constr :: * -> Constraint) :: Constraint
    tagOf :: uni a -> Int
    uniAt :: Int -> Maybe (SomeIn uni)
    bring :: uni `Everywhere` constr => proxy constr -> uni a -> (constr a => r) -> r

type uni1 <: uni2 = uni1 `Everywhere` Includes uni2

-------------------- 'Show' / 'GShow'

parens :: String -> String
parens str = "(" ++ str ++ ")"

-- TODO: precedence.
instance GShow f => Show (Some f) where
   show (Some a) = "Some " ++ parens (gshow a)

-- TODO: precedence.
instance GShow uni => Show (In uni a) where
    show (In uni) = "In " ++ parens (gshow uni)

-- TODO: precedence.
instance (GShow uni, Closed uni, uni `Everywhere` Show) => Show (Of uni a) where
    show (Of uni x) =
        intercalate " "
            [ "Of"
            , parens $ gshow uni
            , parens $ bring (Proxy @Show) uni (show x)
            ]

instance GShow uni => GShow (In uni) where
    gshowsPrec = showsPrec

instance (GShow uni, Closed uni, uni `Everywhere` Show) => GShow (Of uni) where
    gshowsPrec = showsPrec

-------------------- 'Pretty'

instance GShow uni => Pretty (In uni a) where
    pretty (In uni) = pretty $ gshow uni

instance (Closed uni, uni `Everywhere` Pretty) => Pretty (Of uni a) where
    pretty (Of uni x) = bring (Proxy @Pretty) uni $ pretty x

instance GShow uni => Pretty (Some (In uni)) where
    pretty (Some s) = pretty s

instance (Closed uni, uni `Everywhere` Pretty) => Pretty (Some (Of uni)) where
    pretty (Some s) = pretty s

-------------------- 'Eq' / 'GEq'

instance GEq f => Eq (Some f) where
    Some a1 == Some a2 = a1 `defaultEq` a2

deriving newtype instance GEq uni => GEq (In uni)

instance (GEq uni, Closed uni, uni `Everywhere` Eq) => GEq (Of uni) where
    Of uni1 x1 `geq` Of uni2 x2 = do
        Refl <- uni1 `geq` uni2
        guard $ bring (Proxy @Eq) uni1 (x1 == x2)
        Just Refl

-------------------- 'NFData'

instance NFData (In uni a) where
    rnf (In uni) = uni `seq` ()

instance (Closed uni, uni `Everywhere` NFData) => NFData (Of uni a) where
    rnf (Of uni x) = bring (Proxy @NFData) uni $ rnf x

instance NFData (Some (In uni)) where
    rnf (Some s) = rnf s

instance (Closed uni, uni `Everywhere` NFData) => NFData (Some (Of uni)) where
    rnf (Some s) = rnf s

-------------------- 'Hashable'

instance Closed uni => Hashable (In uni a) where
    hashWithSalt salt (In uni) = hashWithSalt salt $ tagOf uni

instance (Closed uni, uni `Everywhere` Hashable) => Hashable (Of uni a) where
    hashWithSalt salt (Of uni x) =
        bring (Proxy @Hashable) uni $ hashWithSalt salt (Some (In uni), x)

instance Closed uni => Hashable (Some (In uni)) where
    hashWithSalt salt (Some s) = hashWithSalt salt s

instance (Closed uni, uni `Everywhere` Hashable) => Hashable (Some (Of uni)) where
    hashWithSalt salt (Some s) = hashWithSalt salt s
