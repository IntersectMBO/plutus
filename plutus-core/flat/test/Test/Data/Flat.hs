{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.Data.Flat
  ( module Test.Data
  )
where

import PlutusCore.Flat
-- import           Flat.Encoder
-- import           Flat.Decoder
import Test.Data
import Test.Data2.Flat ()
-- import           Data.Word
-- import           Data.Foldable
-- import           Data.Int
-- import           GHC.Generics

{-
Compilation times:
           encoderS specials cases |
| 7.10.3 | NO                      | 0:44 |
| 7.10.3 | YES                     | 0:39 |
| 8.0.1  | NO                      | 1:30 |
| 8.0.1  | YES                     | 1:30 |
| 8.0.2  | NO                      | 4:18 |
| 8.0.2  | YES                     | 4:18 |
-}
-- GHC 8.0.2 chokes on this
-- instance Flat A0
-- instance Flat B0
-- instance Flat C0
-- instance Flat D0
-- instance Flat E0
#if MIN_VERSION_base(4,9,0) && ! MIN_VERSION_base(4,16,0)
deriving instance Generic (a, b, c, d, e, f, g, h)

deriving instance Generic (a, b, c, d, e, f, g, h, i)
#endif

instance {-# OVERLAPPABLE #-}( Flat a
                             , Flat b
                             , Flat c
                             , Flat d
                             , Flat e
                             , Flat f
                             , Flat g
                             , Flat h) => Flat (a, b, c, d, e, f, g, h)

instance {-# OVERLAPPABLE #-}( Flat a
                             , Flat b
                             , Flat c
                             , Flat d
                             , Flat e
                             , Flat f
                             , Flat g
                             , Flat h
                             , Flat i) => Flat (a, b, c, d, e, f, g, h, i)

instance Flat N

instance Flat Unit

instance Flat a => Flat (List a)

instance Flat a => Flat (Tree a)

instance Flat Direction

instance Flat Words

instance Flat Ints

instance Flat Void

instance Flat N3

instance Flat Un

instance Flat a => Flat (ListS a)

instance Flat A

instance Flat B

instance Flat D2

instance Flat D4

instance Flat a => Flat (Phantom a)

-- Slow to compile
instance Flat Various
-- Custom instances
-- instance {-# OVERLAPPING #-} Flat (Tree (N,N,N)) --where
--   size (Node t1 t2) = 1 + size t1 + size t2
--   size (Leaf a) = 1 + size a
-- -57%
-- instance {-# OVERLAPPING #-} Flat [N] -- where size = foldl' (\s n -> s + 1 + size n) 1
-- instance {-# OVERLAPPING #-} Flat (N,N,N) -- where
-- {-# INLINE size #-}
-- size (n1,n2,n3) = size n1 + size n2 + size n3
-- -50%
-- instance {-# OVERLAPPING #-} Flat (N,N,N) where
--    {-# INLINE encode #-}
--    encode (n1,n2,n3) = wprim $ (Step 9) (encodeN n1 >=> encodeN n2 >=> encodeN n3)
-- {-# INLINE encodeN #-}
-- encodeN = \case
--     One -> eBitsF 2 0
--     Two ->  eBitsF 2 1
--     Three -> eBitsF 2 2
--     Four -> eBitsF 3 6
--     Five -> eBitsF 3 7
-- instance (Flat a, Flat b, Flat c) => Flat (RR a b c)
-- instance Flat a => Flat (Perfect a)
-- instance Flat a => Flat (Fork a)
-- instance Flat a => Flat (Nest a)
--instance   Flat a => Flat (Stream a) where decode = Stream <$> decode <*> decode
-- instance Flat Expr
--instance (Flat a,Flat (f a),Flat (f (f a))) => Flat (PerfectF f a)
-- instance Flat a => Flat (Stream a)
{-
              |
    |
One Two               |
                Three     |
                      Four Five
 -}
-- instance {-# OVERLAPPABLE #-} Flat a => Flat (Tree a) where
--   encode (Node t1 t2) = eFalse <> encode t1 <> encode t2
--   encode (Leaf a) = eTrue <> encode a
-- instance {-# OVERLAPPING #-} Flat (Tree N) where
--   encode (Node t1 t2) = eFalse <> encode t1 <> encode t2
--   encode (Leaf a) = eTrue <> encode a
-- -- -34% (why?)
-- instance Flat N where
--   {-# INLINE encode #-}
--   encode = \case
--     One -> eBits 2 0
--     Two -> eBits 2 1
--     Three -> eBits 2 2
--     Four -> eBits 3 6
--     Five -> eBits 3 7
-- instance  {-# OVERLAPPING #-}  Flat (Tree N)
-- where
--  {-# INLINE decode #-}
--  decode = do
--    tag <- dBool
--    if tag
--      then Leaf <$> decode
--      else Node <$> decode <*> decode
-- instance Flat N
-- where
--  {-# INLINE decode #-}
--  decode = do
--    tag <- dBool
--    if tag
--      then do
--       tag <- dBool
--       if tag
--         then do
--          tag <- dBool
--          if tag
--            then return Five
--            else return Four
--         else return Three
--      else do
--       tag <- dBool
--       if tag
--         then return Two
--         else return One
-- {-# INLINE size #-}
-- size n s = s + case n of
--   One -> 2
--   Two -> 2
--   Three -> 2
--   Four -> 3
--   Five -> 3
-- instance Flat N where
-- instance {-# OVERLAPPING #-} Flat (Tree N) -- where
-- --   {-# INLINE encode #-}
--   encode (Node t1 t2) = Writer $ \s -> do
--     !s1 <- runWriter eFalse s
--     !s2 <- runWriter (encode t1) s1
--     s3 <- runWriter (encode t2) s2
--     return s3
-- encode (Leaf a) = Writer $ \s -> do
--   s1 <- runWriter eTrue s
--   runWriter (encode a) s1
--   size (Node t1 t2) = 1 + size t1 + size t2
--   size (Leaf a) = 1 + size a
--instance Flat N



