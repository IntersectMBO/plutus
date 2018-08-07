{-# LANGUAGE OverloadedStrings #-}
module Evaluation.CkMachine where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.CkMachine
import           Evaluation.Generator

import qualified Data.ByteString.Lazy as BSL
import           Control.Monad.Reader
import           Control.Monad.Morph
import           Hedgehog hiding (Size, Var, annotate)
import qualified Hedgehog.Gen   as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog

parseRunCk :: BSL.ByteString -> Either ParseError CkEvalResult
parseRunCk = fmap (runCk . void) . parseScoped

blah = parseRunCk $ "(program 0.1.0 [(lam x [(con integer) (con 32)] x) (con 32 ! 123456)])"

test_constant :: TestTree
test_constant = testProperty "" . property $ do
    size <- forAll genSizeDef
    term <- forAll $ Constant () <$> genConstantSized size
    evaluateCk term === CkEvalSuccess term

main = defaultMain test_constant

-- As a first iteration we may consider generating well-typed rank-0 terms. Something like that:

-- data Typed v a = TypedBuiltinName
--     { _typedValue  :: v
--     , _typedScheme :: forall size. TypeScheme size a
--     }

-- data TypeScheme size a r where
--     TypeSchemeBuiltin :: TypedBuiltin size a -> TypeScheme size a a
--     TypeSchemeArrow   :: TypeScheme size a q -> TypeScheme size b r -> TypeScheme size (a -> b) r
--     TypeSchemeAllSize :: (size -> TypeScheme size a r) -> TypeScheme size a r

-- newtype Context = Context
--     { unContext :: DMap TypedBuiltinSized (Typed (Name ()))
--     }

-- type GenTyped = GenPlcT (Reader Context)

-- Here the only search that we need to perform is the search for things that return an appropriate @r@,
-- be them variables or functions. Better if we also take types of arguments into account, but it is
-- not required as we can always generate an argument out of thin air in a rank-0 setting (without @Void@).

-- This should allow us to generate terms like (likely less sensible, but still well-typed)

-- (\(f : (integer -> bytestring) -> bool) -> f $ \i -> intToByteString i)
--     (\g -> g 3 `equalsByteString` intToByteString 3)

-- which is a pretty good start.

-- exists a. Typed BuiltinName a r
-- exists a. Typed (Name ())   a r
