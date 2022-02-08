{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-orphans -Wno-missing-signatures #-}
import Data.RandomAccessList.SkewBinary qualified as B
import Data.Semigroup
import Data.Word
import GHC.Exts
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

instance Arbitrary a => Arbitrary (B.RAList a) where
    arbitrary = fromList <$> arbitrary

hundred :: B.RAList Word64
hundred = foldr B.Cons B.Nil [1..100]

prop_null x = not $ B.null $ B.Cons x B.Nil

prop_cons1 x = B.Cons x hundred /= hundred
prop_cons2 x xs = B.Cons x xs /= xs

unit_null1 = not (B.null hundred) @? "list is empty"
unit_null2 = B.null B.Nil @? "list not empty"

unit_head1 = B.head hundred @?= 1
unit_head2 = B.head (B.Cons 0 hundred) @?= 0
unit_head3 = B.head (foldr B.Cons hundred [200.. 300]) @?= 200
unit_head4 = (B.head (B.tail hundred) == B.head hundred + 1) @? "head mismatch"

unit_tail1 = B.head (B.tail (B.tail hundred)) == 3 @?  "tail broken"
unit_tail2 = B.tail (B.Cons 1 hundred) == hundred @? "tail is not inverse of cons"
unit_tail3 = B.null (B.tail (B.Cons () B.Nil)) @? "tail is not inverse of cons"
unit_tail4 = (tailN 150 (applyN (B.Cons 0) 100 hundred) == tailN 50 hundred) @? "tail/cons broken"
    where
      tailN :: Word64 -> B.RAList a -> B.RAList a
      tailN = applyN B.tail

applyN :: (a->a) -> Word64 -> a -> a
applyN f n = appEndo $ stimes n $ Endo f

unit_ix1 = B.unsafeIndexZero hundred 0 == B.head hundred @? "index error"
unit_ix2 = B.unsafeIndexZero (B.Cons 1 (B.Cons 2 B.Nil)) 1 @?= (2 :: Int)
unit_ix3 = all (\x -> B.unsafeIndexZero hundred (x-1) == x) [1..100] @? "index wrong"
prop_ix1 x y = B.unsafeIndexZero (B.Cons x (B.Cons y B.Nil)) 0 == x
prop_ix2 x y = B.unsafeIndexZero (B.Cons x (B.Cons y B.Nil)) 1 == y
prop_ix3 xs =
    not (B.null xs) ==>
    B.unsafeIndexZero xs 0 == B.head xs

unit_ixzero1 = B.unsafeIndexZero hundred 0 == B.head hundred @? "index error"
unit_ixzero2 = B.unsafeIndexZero (B.Cons 1 (B.Cons 2 B.Nil)) 1 @?= (2 :: Int)
unit_ixzero3 = all (\x -> B.unsafeIndexZero hundred (x-1) == x) [1..100] @? "index wrong"
prop_ixzero1 x y = B.unsafeIndexZero (B.Cons x (B.Cons y B.Nil)) 0 == x
prop_ixzero2 x y = B.unsafeIndexZero (B.Cons x (B.Cons y B.Nil)) 1 == y
prop_ixzero3 xs =
    not (B.null xs) ==>
    B.unsafeIndexZero xs 0 == B.head xs

prop_fail1 (NonZero i) = total $ B.unsafeIndexZero (applyN (B.Cons ()) i B.Nil) i
prop_fail2 (NonZero i) = total $ B.unsafeIndexZero (B.Nil :: B.RAList ()) i

prop_constail :: Eq a => Word64 -> Word64 -> a -> B.RAList a -> Bool
prop_constail reps skips x xs =
    applyN (applyN B.tail skips . applyN (B.Cons x) skips) reps xs == xs

-- needed by QuickCheck TH
$(pure [])

main :: IO ()
main = defaultMain $
    testGroup "Data.RandomAccessList.SkewBinary"
    [ testProperty "prop_null" $(monomorphic 'prop_null)
    , testCase "unit_null1" unit_null1
    , testCase "unit_null2" unit_null2
    , testProperty "prop_cons1" $(monomorphic 'prop_cons1)
    , testProperty "prop_cons2" $(monomorphic 'prop_cons2)
    , testCase "unit_head1" unit_head1
    , testCase "unit_head2" unit_head2
    , testCase "unit_head3" unit_head3
    , testCase "unit_head4" unit_head4
    , testCase "unit_tail1" unit_tail1
    , testCase "unit_tail2" unit_tail2
    , testCase "unit_tail3" unit_tail3
    , testCase "unit_tail4" unit_tail4
    , testCase "unit_ix1" unit_ix1
    , testCase "unit_ix2" unit_ix2
    , testCase "unit_ix3" unit_ix3
    , testProperty "prop_ix1" $(monomorphic 'prop_ix1)
    , testProperty "prop_ix2" $(monomorphic 'prop_ix2)
    , testProperty "prop_ix3" $(monomorphic 'prop_ix3)
    , testCase "unit_ixzero1" unit_ixzero1
    , testCase "unit_ixzero2" unit_ixzero2
    , testCase "unit_ixzero3" unit_ixzero3
    , testProperty "prop_ixzero1" $(monomorphic 'prop_ixzero1)
    , testProperty "prop_ixzero2" $(monomorphic 'prop_ixzero2)
    , testProperty "prop_ixzero3" $(monomorphic 'prop_ixzero3)
    , testProperty "prop_fail1" (expectFailure $(monomorphic 'prop_fail1))
    , testProperty "prop_fail2" (expectFailure $(monomorphic 'prop_fail2))
    -- with word64, quickcheck tends to generate super-long skew binary lists, leading to OOM.
    -- this tones down a bit the default max size from 100 to 10
    ,   localOption (QuickCheckMaxSize 10) $
        testProperty "prop_constail" $(monomorphic 'prop_constail)
    ]
