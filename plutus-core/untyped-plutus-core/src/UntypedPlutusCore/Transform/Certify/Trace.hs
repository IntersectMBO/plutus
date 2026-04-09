{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module UntypedPlutusCore.Transform.Certify.Trace where

import UntypedPlutusCore.Core.Type (Term)
import UntypedPlutusCore.Transform.Certify.Hints qualified as Certify

import Control.DeepSeq
import GHC.Generics

data Certified = Certified
  deriving stock (Show, Generic)
  deriving anyclass (NFData)

data NotCertified = NotCertified
  deriving stock (Show, Generic)
  deriving anyclass (NFData)

data SimplifierStage a where
  FloatDelay :: SimplifierStage Certified
  ForceDelay :: SimplifierStage Certified
  ForceCaseDelay :: SimplifierStage Certified
  CaseOfCase :: SimplifierStage NotCertified
  CaseReduce :: SimplifierStage Certified
  Inline :: SimplifierStage Certified
  CSE :: SimplifierStage Certified
  ApplyToCase :: SimplifierStage Certified
  Unknown :: SimplifierStage NotCertified

deriving instance Show a => Show (SimplifierStage a)

instance Generic a => Generic (SimplifierStage a)

instance (Generic a, NFData a) => NFData (SimplifierStage a) where
  rnf = undefined

data Yes = Yes

data No = No

-- this is much simpler, why did i go with something so complicated :(
-- data ImplTags = A | B | C
--
-- data NotImplTags = D
--
-- data Tags = Impl ImplTags | NotImpl NotImplTags

data CertifierImplements a where
  CertFloatDelay :: CertifierImplements Yes
  CertForceDelay :: CertifierImplements Yes
  CertCaseOfCase :: CertifierImplements No
  CertCaseReduce :: CertifierImplements Yes
  CertInline :: CertifierImplements Yes
  CertCSE :: CertifierImplements Yes
  CertApplyToCase :: CertifierImplements Yes
  CertUnknown :: CertifierImplements No

data Simplification name uni fun a
  = forall isCertified.
  Show isCertified =>
  Simplification
  { beforeAST :: Term name uni fun a
  , stage :: SimplifierStage isCertified
  , hints :: Certify.Hints
  , afterAST :: Term name uni fun a
  }

-- TODO2: we probably don't want this in memory so after MVP
-- we should consider serializing this to disk
newtype SimplifierTrace name uni fun a
  = SimplifierTrace
  { simplifierTrace
      :: [Simplification name uni fun a]
  }

initSimplifierTrace :: SimplifierTrace name uni fun a
initSimplifierTrace = SimplifierTrace []

allASTs :: SimplifierTrace name uni fun a -> [Term name uni fun a]
allASTs = \case
  SimplifierTrace [] -> []
  SimplifierTrace xs@(x : _) ->
    -- `SimplifierTrace` is in reverse order: the first item is the last pass run.
    afterAST x : map beforeAST xs
