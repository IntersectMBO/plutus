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
import           PlutusPrelude                            hiding (list)

import           Control.Monad.Morph
import           Hedgehog                                 hiding (Size, Var)
import qualified Hedgehog.Gen                             as Gen
import qualified Hedgehog.Range                           as Range

-- | Convert an 'Integer' to a @nat@. TODO: convert PLC's @integer@ to @nat@ instead.
getBuiltinIntegerToNat :: Integer -> Quote (Term TyName Name ())
getBuiltinIntegerToNat n
    | n < 0     = error $ "getBuiltinIntegerToNat: negative argument: " ++ show n
    | otherwise = go n where
          go 0 = getBuiltinZero
          go m = Apply () <$> getBuiltinSucc <*> go (m - 1)

-- | Convert a @nat@ to an 'Integer'. TODO: this should be just @Quote (Term TyName Name ())@.
getBuiltinNatToInteger :: Natural -> Term TyName Name () -> Quote (Term TyName Name ())
getBuiltinNatToInteger s n = do
    builtinFoldNat <- getBuiltinFoldNat
    let int = Constant () . BuiltinInt () s
    return $
         mkIterApp (TyInst () builtinFoldNat $ TyBuiltin () TyInteger)
         [ Apply () (Constant () $ BuiltinName () AddInteger) $ int 1
          , int 0
          , n
          ]

-- | Convert a Haskell list of 'Term's to a PLC @list@.
getListToBuiltinList :: Type TyName () -> [Term TyName Name ()] -> Quote (Term TyName Name ())
getListToBuiltinList ty ts = do
    builtinNil  <- getBuiltinNil
    builtinCons <- getBuiltinCons
    return $ foldr
        (\x xs -> foldl' (Apply ()) (TyInst () builtinCons ty) [x, xs])
        (TyInst () builtinNil ty)
        ts

-- | Generate an 'Integer', turn it into a Scott-encoded PLC @Nat@ (see 'getBuiltinNat'),
-- turn that @Nat@ into the corresponding PLC @integer@ using a fold (see 'getBuiltinFoldNat')
-- defined in terms of generic fix (see 'getBuiltinFix') and return the result
-- along with the original 'Integer'
genNatRoundtrip :: GenT Quote (TermOf (TypedBuiltinValue size Integer))
genNatRoundtrip = do
    let size = 1
        typedIntSized = TypedBuiltinSized (SizeValue size) TypedBuiltinSizedInt
    TermOf _ nv <- Gen.filter ((>= 0) . _termOfValue) $ genTypedBuiltinDef typedIntSized
    term <- lift $ getBuiltinIntegerToNat nv >>= getBuiltinNatToInteger size
    return . TermOf term $ TypedBuiltinValue typedIntSized nv

-- | Generate a list of 'Integer's, turn it into a Scott-encoded PLC @List@ (see 'getBuiltinList'),
-- sum elements of the list (see 'getBuiltinSum') and return it along with the sum of the original list.
genListSum :: GenT Quote (TermOf (TypedBuiltinValue size Integer))
genListSum = do
    size <- genSizeIn 1 8
    let intSized      = TyBuiltin () TyInteger
        typedIntSized = TypedBuiltinSized (SizeValue size) TypedBuiltinSizedInt
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
    TermOf b bv <- genTermLoose TypedBuiltinBool
    TermOf i iv <- genTermLoose typedIntSized
    TermOf j jv <- genTermLoose typedIntSized
    builtinConst <- lift getBuiltinConst
    builtinUnit  <- lift getBuiltinUnit
    builtinIf    <- lift getBuiltinIf
    let builtinConstSpec =
            Apply () $ mkIterInst builtinConst [TyBuiltin () TyInteger, builtinUnit]
        term = mkIterApp
            (TyInst () builtinIf $ TyBuiltin () TyInteger)
            [b, builtinConstSpec i, builtinConstSpec j]
        value = if bv then iv else jv
    return $ TermOf term $ TypedBuiltinValue typedIntSized value
