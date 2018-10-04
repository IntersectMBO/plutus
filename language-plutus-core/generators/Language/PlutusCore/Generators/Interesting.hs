-- | Sample generators used for tests.
module Language.PlutusCore.Generators.Interesting
    ( genNatRoundtrip
    , genListSum
    , genIfIntegers
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Generators
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Nat
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Meta

import           Control.Monad.Morph
import           Hedgehog                                 hiding (Size, Var)
import qualified Hedgehog.Gen                             as Gen
import qualified Hedgehog.Range                           as Range

-- | Generate an 'Integer', turn it into a Scott-encoded PLC @Nat@ (see 'getBuiltinNat'),
-- turn that @Nat@ into the corresponding PLC @integer@ using a fold (see 'getBuiltinFoldNat')
-- defined in terms of generic fix (see 'getBuiltinFix') and return the result
-- along with the original 'Integer'
genNatRoundtrip :: GenT Quote (TermOf (TypedBuiltinValue size Integer))
genNatRoundtrip = do
    let size = 1
        typedIntSized = TypedBuiltinSized (SizeValue size) TypedBuiltinSizedInt
    TermOf _ nv <- Gen.filter ((>= 0) . _termOfValue) $ genTypedBuiltinDef typedIntSized
    term <- lift $ do
        t <- getBuiltinIntegerToNat nv
        Apply () <$> getBuiltinNatToInteger size <*> pure t
    return . TermOf term $ TypedBuiltinValue typedIntSized nv

-- | Generate a list of 'Integer's, turn it into a Scott-encoded PLC @List@ (see 'getBuiltinList'),
-- sum elements of the list (see 'getBuiltinSum') and return it along with the sum of the original list.
genListSum :: GenT Quote (TermOf (TypedBuiltinValue size Integer))
genListSum = do
    size <- genSizeIn 1 8
    let typedIntSized = TypedBuiltinSized (SizeValue size) TypedBuiltinSizedInt
    intSized <- lift $ typedBuiltinToType typedIntSized
    ps <- Gen.list (Range.linear 0 10) $ genTypedBuiltinLoose typedIntSized
    term <- lift $ do
        builtinSum <- getBuiltinSum size
        list <- getListToBuiltinList intSized $ map _termOfTerm ps
        return $ Apply () builtinSum list
    let haskSum = sum $ map _termOfValue ps
    return . TermOf term $ TypedBuiltinValue typedIntSized haskSum

-- | Generate a @boolean@ and two @integer@s and check whether @if b then i1 else i2@
-- means the same thing in Haskell and PLC. Terms are generated using 'genTermLoose'.
genIfIntegers :: GenT Quote (TermOf (TypedBuiltinValue size Integer))
genIfIntegers = do
    size <- genSizeDef
    let typedIntSized = TypedBuiltinSized (SizeValue size) TypedBuiltinSizedInt
    intSized <- lift $ typedBuiltinToType typedIntSized
    TermOf b bv <- genTermLoose TypedBuiltinBool
    TermOf i iv <- genTermLoose typedIntSized
    TermOf j jv <- genTermLoose typedIntSized
    builtinConst <- lift getBuiltinConst
    builtinUnit  <- lift getBuiltinUnit
    builtinIf    <- lift getBuiltinIf
    let builtinConstSpec =
            Apply () $ mkIterInst builtinConst [intSized, builtinUnit]
        term = mkIterApp
            (TyInst () builtinIf intSized)
            [b, builtinConstSpec i, builtinConstSpec j]
        value = if bv then iv else jv
    return $ TermOf term $ TypedBuiltinValue typedIntSized value
