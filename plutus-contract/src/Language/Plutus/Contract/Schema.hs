{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE DerivingVia             #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE OverloadedLabels        #-}
{-# LANGUAGE OverloadedStrings       #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -fno-warn-unticked-promoted-constructors #-}
module Language.Plutus.Contract.Schema(
      Hooks(..)
    , Event(..)
    , generalise
    , initialise
    , First
    , Second
    ) where

import           Data.Aeson            (FromJSON, ToJSON, (.:))
import qualified Data.Aeson            as Aeson
import qualified Data.Aeson.Types      as Aeson
import           Data.Functor.Identity
import           Data.Functor.Product
import           Data.Proxy            (Proxy (..))
import           Data.Row
import           Data.Row.Internal
import qualified Data.Row.Records      as Records
import qualified Data.Row.Variants     as Variants
import           Data.Text             (Text)
import qualified Data.Text             as Text

import           GHC.TypeLits

{- Note [Contract Schema]

Every contract has a schema that describes the data types used by the contract
to interact with the outside world. Conceptually the schema is a map of symbols
to pairs of types. Each entry in this map stands for a named request-response
pair.

For example, the 'WriteTx' interaction is defined as

  type WriteTx = "tx" .== ((), [UnbalancedTx])

Meaning that the output produced by the contract (2nd element) is a list of
unbalanced transactions, and the input the contract expects as a result (1st
element) is the unit value, telling it that the transactions have been
submitted.

In practice the schema is a type of the 'Data.Row.Row' kind.

-}

newtype Event s = Event { unEvent :: Var (First s) }

deriving instance Forall (First s) Show => Show (Event s)
deriving instance Forall (First s) Eq => Eq (Event s)

newtype Hooks s = Hooks { unHooks :: Rec (Second s) }

deriving instance Forall (Second s) Show => Show (Hooks s)

instance Forall (Second s) ToJSON => ToJSON (Hooks s) where
  toJSON = Aeson.object . Records.eraseWithLabels @ToJSON @(Second s) @Text @Aeson.Value Aeson.toJSON . unHooks

instance (AllUniqueLabels (Second s), Forall (Second s) FromJSON) => FromJSON (Hooks s) where
  parseJSON vl = Hooks <$> Records.fromLabelsA @FromJSON @Aeson.Parser @(Second s)  (\lbl -> Aeson.withObject "Rec" (\obj -> obj .: (Text.pack $ show lbl) >>= Aeson.parseJSON) vl)

instance Forall (Second s) Semigroup => Semigroup (Hooks s) where
  (<>) = merge @s

instance (AllUniqueLabels (Second s), Forall (Second s) Semigroup, Forall (Second s) Monoid) => Monoid (Hooks s) where
  mempty = Hooks (Records.default' @Monoid @(Second s) mempty)
  mappend = (<>)

initialise :: forall (s :: Row *) l a. (AllUniqueLabels (Second s), Forall (Second s) Semigroup, Forall (Second s) Monoid, KnownSymbol l, HasType l a (Second s)) => a -> Hooks s
initialise a =
  let Hooks h = mempty @(Hooks s)
  in Hooks (Records.update (Label @l) a h)

generalise :: forall s s'. (AllUniqueLabels (Second s'), Forall (Second s') Monoid, (Second s .// Second s') ~ (Second s')) => Hooks s -> Hooks s'
generalise (Hooks l) = Hooks $ l .// Records.default' @Monoid @(Second s') mempty

merge :: forall s. Forall (Second s) Semigroup => Hooks s -> Hooks s -> Hooks s
merge (Hooks rec1) (Hooks rec2) = Hooks $ metamorph @_ @(Second s) @Semigroup @(Product Rec Rec) @Rec @Identity Proxy doNil doUncons doCons (Pair rec1 rec2)
  where
    doNil _ = empty
    doUncons l (Pair r1 r2) = (Identity $ r1 .! l <> r2 .! l, Pair (Records.unsafeRemove l r1) (Records.unsafeRemove l r2))
    doCons l (Identity v) = Records.unsafeInjectFront l v


instance (AllUniqueLabels (First s), Forall (First s) FromJSON) => FromJSON (Event s) where
  parseJSON vl = Event <$> Variants.fromLabels @FromJSON @(First s) @Aeson.Parser (\lbl -> Aeson.withObject "Var" (\obj -> do { tg <- obj .: "tag"; if tg == show lbl then (obj .: "value") >>= Aeson.parseJSON else fail "Wrong label" }) vl)

instance Forall (First s) ToJSON => ToJSON (Event s) where
  toJSON (Event v) = Aeson.object [Variants.eraseWithLabels @ToJSON @(First s)  @Text @Aeson.Value Aeson.toJSON v]

type family First (r :: Row *) where
  First ('R r) = 'R (FirstR r)

type family FirstR (r :: [LT *]) where
  FirstR '[] = '[]
  FirstR (l ':-> (t1, _) ': r) =
    l ':-> t1 ': FirstR r
  FirstR (l ':-> t ': _) =
    TypeError ('Text "First requires all types to be tuples."
                :$$: 'Text "For one, the label " :<>: ShowType l :<>: 'Text " has type " :<>: ShowType t)

type family Second (r :: Row *) where
  Second ('R r) = 'R (SecondR r)

type family SecondR (r :: [LT *]) where
  SecondR '[] = '[]
  SecondR (l ':-> (_, t2) ': r) =
    l ':-> t2 ': SecondR r
  SecondR (l ':-> t ': _) =
    TypeError ('Text "Second requires all types to be tuples."
                :$$: 'Text "For one, the label " :<>: ShowType l :<>: 'Text " has type " :<>: ShowType t)

