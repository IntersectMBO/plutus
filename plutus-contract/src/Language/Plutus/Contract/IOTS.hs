{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedLabels    #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.IOTS(
    IotsType(..)
  , schemaMap
  ) where

import           Data.Functor.Const
import           Data.Functor.Identity
import           Data.Proxy            (Proxy (..))
import           Data.Row
import           Data.Row.Internal     (Unconstrained1)
import qualified Data.Row.Records      as Records
import           Data.Sequence         (Seq)
import qualified Data.Sequence         as Seq
import           Data.Text             (Text)
import qualified Data.Text             as Text
import           GHC.TypeLits          (symbolVal)
import           IOTS                  (IotsType (..), export)


mksConst :: forall l a. (KnownSymbol l, IotsType a) => Label l -> (Const (Seq Text)) a
mksConst Label = Const (Seq.fromList [Text.pack $ symbolVal (Proxy @l), export (Proxy @a)])

mkSchema :: forall s. (AllUniqueLabels s, Forall s IotsType) => Rec (Records.Map (Const (Seq Text)) s)
mkSchema = runIdentity (Records.fromLabelsMapA @IotsType @Identity @(Const (Seq Text)) @s (Identity . mksConst))

unSchema :: forall s. Forall s Unconstrained1 => Rec (Records.Map (Const (Seq Text)) s) -> Const (Seq Text) (Rec s)
unSchema = Records.sequence

schemaMap :: forall s. (AllUniqueLabels s, Forall s IotsType, Forall s Unconstrained1) => Const (Seq Text) (Rec s)
schemaMap = unSchema @s (mkSchema @s)
