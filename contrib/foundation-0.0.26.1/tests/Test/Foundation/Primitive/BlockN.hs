{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeOperators             #-}

module Test.Foundation.Primitive.BlockN
    ( testBlockN
    ) where

import           Data.Proxy (Proxy(..))
import           Foundation hiding (singleton, replicate, cons, uncons, elem)
import           Basement.Nat
import           Basement.Types.OffsetSize
import qualified Basement.Block as B
import           Basement.Sized.Block
import           Basement.From
import           Foundation.Check

testBlockN = Group "BlockN"
     [ testWithDifferentN
     , Property "singleton" $ B.singleton (1 :: Int) === toBlock (singleton 1)
     ]

testWithDifferentN =
    Group "Multiple n" $ fmap (\(Foo p) -> testBlock p) ns

testBlock :: forall n . (KnownNat n, NatWithinBound (CountOf Int) n) => Proxy n -> Test
testBlock nProxy =
  Group ("n = " <> show size)
    [ Property "to/from block" $ block === (toBlock blockN)
    , Property "replicate" $ B.replicate size (7 :: Int) === toBlock (rep 7)
    , Property "length . cons" $ B.length (toBlock (cons 42 blockN)) === (size+1)
    , Property "elem" $ size == 0 || from size `elem` blockN
    ]
  where
    rep :: Int -> BlockN n Int
    rep = replicate

    size = natValCountOf nProxy
    block = createBlockSized size
    Just blockN = toBlockN block :: Maybe (BlockN n Int)

createBlockSized :: CountOf Int -> B.Block Int
createBlockSized n@(CountOf n') = B.create n (const n')

data Foo = forall a . (KnownNat a, NatWithinBound (CountOf Int) a) => Foo (Proxy a)

ns :: [Foo]
ns =
    [ Foo (Proxy :: Proxy 0)
    , Foo (Proxy :: Proxy 1)
    , Foo (Proxy :: Proxy 2)
    , Foo (Proxy :: Proxy 3)
    , Foo (Proxy :: Proxy 4)
    , Foo (Proxy :: Proxy 5)
    , Foo (Proxy :: Proxy 6)
    , Foo (Proxy :: Proxy 7)
    , Foo (Proxy :: Proxy 8)
    , Foo (Proxy :: Proxy 33)
    , Foo (Proxy :: Proxy 42)
    ]
