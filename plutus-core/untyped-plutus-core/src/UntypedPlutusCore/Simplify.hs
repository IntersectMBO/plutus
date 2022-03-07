{-# LANGUAGE TemplateHaskell #-}
module UntypedPlutusCore.Simplify ( simplifyTerm, simplifyProgram, SimplifyOpts (..), soMaxSimplifierIterations, soInlineHints, defaultSimplifyOpts, InlineHints (..) ) where

import UntypedPlutusCore.Core.Type
import UntypedPlutusCore.Transform.ForceDelay
import UntypedPlutusCore.Transform.Inline

import Control.Monad
import Data.List
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Name
import PlutusCore.Quote

import Control.Lens.TH

data SimplifyOpts a = SimplifyOpts { _soMaxSimplifierIterations  :: Int, _soInlineHints :: InlineHints Name a }
  deriving stock (Show)

makeLenses ''SimplifyOpts

defaultSimplifyOpts :: SimplifyOpts a
defaultSimplifyOpts = SimplifyOpts
    { _soMaxSimplifierIterations = 12
    , _soInlineHints = mempty
    }

simplifyProgram
    :: forall uni fun m a
    . (PLC.ToBuiltinMeaning uni fun, MonadQuote m)
    => SimplifyOpts a
    -> Program Name uni fun a
    -> m (Program Name uni fun a)
simplifyProgram opts (Program a v t) = Program a v <$> simplifyTerm opts t

simplifyTerm
    :: forall uni fun m a
    . (PLC.ToBuiltinMeaning uni fun, MonadQuote m)
    => SimplifyOpts a
    -> Term Name uni fun a
    -> m (Term Name uni fun a)
simplifyTerm opts = simplifyNTimes (_soMaxSimplifierIterations opts)
    where
        -- Run the simplifier @n@ times
        simplifyNTimes :: Int -> Term Name uni fun a -> m (Term Name uni fun a)
        simplifyNTimes n = foldl' (>=>) pure (map simplifyStep [1 .. n])
        -- generate simplification step
        simplifyStep :: Int -> Term Name uni fun a -> m (Term Name uni fun a)
        simplifyStep _ term = inline (_soInlineHints opts) (forceDelayCancel term)
