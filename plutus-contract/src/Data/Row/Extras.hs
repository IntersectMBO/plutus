{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Instances for 'Data.Row.Records.Rec' and 'Data.Row.Variants.Var' types
module Data.Row.Extras(
      JsonRec(..)
    , JsonVar(..)
    , namedBranchFromJSON
    , type (.\\)
    ) where

import           Data.Aeson        (FromJSON, ToJSON, (.:), (.=))
import qualified Data.Aeson        as Aeson
import qualified Data.Aeson.Types  as Aeson
import           Data.Row          hiding (type (.\\))
import           Data.Row.Internal hiding (type (.\\))
import qualified Data.Row.Records  as Records
import qualified Data.Row.Variants as Variants
import           Data.Text         (Text)
import qualified Data.Text         as Text
import           GHC.TypeLits      hiding (Text)

newtype JsonVar s = JsonVar { unJsonVar :: Var s }

instance (AllUniqueLabels s, Forall s FromJSON) => FromJSON (JsonVar s) where
    parseJSON vl = fmap JsonVar $ do
      Aeson.withObject "Var" (\obj -> do
        theTag <- obj .: "tag"
        theValue <- obj .: "value"
        namedBranchFromJSON theTag theValue)
        vl

instance Forall s ToJSON => ToJSON (JsonVar s) where
    toJSON (JsonVar v) =
      let (lbl, vl) = Variants.eraseWithLabels @ToJSON @s  @Text @Aeson.Value Aeson.toJSON v
      in Aeson.object ["tag" .= lbl, "value" .= vl]

newtype JsonRec s = JsonRec { unJsonRec :: Rec s }

-- | Parse a 'Var s' from JSON if the label of the branch is known.
namedBranchFromJSON :: forall s. (AllUniqueLabels s, Forall s FromJSON) => String -> Aeson.Value -> Aeson.Parser (Var s)
namedBranchFromJSON nm vl =
  Variants.fromLabels @FromJSON @s @Aeson.Parser (\case { n | show n == nm -> Aeson.parseJSON vl; _ -> fail "Wrong label" })

instance Forall s ToJSON => ToJSON (JsonRec s) where
  toJSON = Aeson.object . Records.eraseWithLabels @ToJSON @s @Text @Aeson.Value Aeson.toJSON . unJsonRec

instance (AllUniqueLabels s, Forall s FromJSON) => FromJSON (JsonRec s) where
  parseJSON vl = JsonRec <$> Records.fromLabelsA @FromJSON @Aeson.Parser @s  (\lbl -> Aeson.withObject "Rec" (\obj -> obj .: (Text.pack $ show lbl) >>= Aeson.parseJSON) vl)

-- | Fast diff. The implementation in row-types is exponential in time and memory in the number of
--   overlapping rows, due to limitations in ghc's handling of type families. This version is much
--   faster.
infixl 6 .\\ {- This comment needed to appease CPP -}
-- | Type level Row difference.  That is, @l '.\\' r@ is the row remaining after
-- removing any matching elements of @r@ from @l@.
type family (l :: Row k) .\\ (r :: Row k) :: Row k where
  'R l .\\ 'R r = 'R (Diff l r)

type family Diff (l :: [LT k]) (r :: [LT k]) where
  Diff '[] r = '[]
  Diff l '[] = l
  Diff (l ':-> al ': tl) (l ':-> al ': tr) = Diff tl tr
  Diff (hl ':-> al ': tl) (hr ':-> ar ': tr) =
    DiffCont (CmpSymbol hl hr) hl al tl hr ar tr

type family DiffCont (o :: Ordering)
                     (hl :: Symbol) (al :: k) (tl :: [LT k])
                     (hr :: Symbol) (ar :: k) (tr :: [LT k]) where
    DiffCont 'LT hl al tl hr ar tr =
      (hl ':-> al ': Diff tl (hr ':-> ar ': tr))
    DiffCont _ hl al tl hr ar tr =
      (Diff (hl ':-> al ': tl) tr)
