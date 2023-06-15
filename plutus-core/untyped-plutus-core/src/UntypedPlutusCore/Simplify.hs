{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeApplications #-}

module UntypedPlutusCore.Simplify (
    simplifyTerm,
    simplifyProgram,
    SimplifyOpts (..),
    soMaxSimplifierIterations,
    soInlineHints,
    defaultSimplifyOpts,
    InlineHints (..),
) where

import PlutusCore.Compiler.Types
import PlutusCore.Default.Builtins
import PlutusCore.Name
import UntypedPlutusCore.Core.Type
import UntypedPlutusCore.Transform.CaseOfCase
import UntypedPlutusCore.Transform.CaseReduce
import UntypedPlutusCore.Transform.FloatDelay
import UntypedPlutusCore.Transform.ForceDelay
import UntypedPlutusCore.Transform.Inline

import Control.Lens.TH
import Control.Monad
import Data.List
import Data.Typeable

data SimplifyOpts name a = SimplifyOpts
    { _soMaxSimplifierIterations :: Int
    , _soInlineHints             :: InlineHints name a
    }
    deriving stock (Show)

makeLenses ''SimplifyOpts

defaultSimplifyOpts :: SimplifyOpts name a
defaultSimplifyOpts =
    SimplifyOpts
        { _soMaxSimplifierIterations = 12
        , _soInlineHints = mempty
        }

simplifyProgram ::
    forall name uni fun m a.
    (Compiling m uni fun name) =>
    SimplifyOpts name a ->
    Program name uni fun a ->
    m (Program name uni fun a)
simplifyProgram opts (Program a v t) = Program a v <$> simplifyTerm opts t

simplifyTerm ::
    forall name uni fun m a.
    (Compiling m uni fun name) =>
    SimplifyOpts name a ->
    Term name uni fun a ->
    m (Term name uni fun a)
simplifyTerm opts = simplifyNTimes (_soMaxSimplifierIterations opts)
  where
    -- Run the simplifier @n@ times
    simplifyNTimes :: Int -> Term name uni fun a -> m (Term name uni fun a)
    simplifyNTimes n = foldl' (>=>) pure (map simplifyStep [1 .. n])
    -- generate simplification step
    simplifyStep :: Int -> Term name uni fun a -> m (Term name uni fun a)
    simplifyStep _ =
        floatDelay
            >=> pure . forceDelayCancel
            >=> pure . caseOfCase'
            >=> pure . caseReduce
            >=> inline (_soInlineHints opts)

    caseOfCase' :: Term name uni fun a -> Term name uni fun a
    caseOfCase' = case eqT @fun @DefaultFun of
        Just Refl -> caseOfCase
        Nothing   -> id
