{-# LANGUAGE FlexibleInstances #-}

module Test.Data.Flat
  ( module Test.Data
  )
where

import PlutusCore.Flat
import PlutusCore.Flat.Decoder.Prim (dBool)
import PlutusCore.Flat.Encoder (eBits16, eFalse, eTrue, mempty)
import Prelude hiding (mempty)

import Test.Data
import Test.Data2.Flat ()

instance
  {-# OVERLAPPABLE #-}
  ( Flat a
  , Flat b
  , Flat c
  , Flat d
  , Flat e
  , Flat f
  , Flat g
  , Flat h
  )
  => Flat (a, b, c, d, e, f, g, h)
  where
  encode (a, b, c, d, e, f, g, h) = encode a <> encode b <> encode c <> encode d <> encode e <> encode f <> encode g <> encode h
  decode = (,,,,,,,) <$> decode <*> decode <*> decode <*> decode <*> decode <*> decode <*> decode <*> decode
  size (a, b, c, d, e, f, g, h) n = size a (size b (size c (size d (size e (size f (size g (size h n)))))))

instance
  {-# OVERLAPPABLE #-}
  ( Flat a
  , Flat b
  , Flat c
  , Flat d
  , Flat e
  , Flat f
  , Flat g
  , Flat h
  , Flat i
  )
  => Flat (a, b, c, d, e, f, g, h, i)
  where
  encode (a, b, c, d, e, f, g, h, i) = encode a <> encode b <> encode c <> encode d <> encode e <> encode f <> encode g <> encode h <> encode i
  decode = (,,,,,,,,) <$> decode <*> decode <*> decode <*> decode <*> decode <*> decode <*> decode <*> decode <*> decode
  size (a, b, c, d, e, f, g, h, i) n = size a (size b (size c (size d (size e (size f (size g (size h (size i n))))))))

instance Flat N where
  encode One = eBits16 2 0
  encode Two = eBits16 2 1
  encode Three = eBits16 2 2
  encode Four = eBits16 3 6
  encode Five = eBits16 3 7
  decode = do
    tag <- dBool
    if tag
      then do
        tag2 <- dBool
        if tag2
          then do
            tag3 <- dBool
            if tag3 then pure Five else pure Four
          else pure Three
      else do
        tag2 <- dBool
        if tag2 then pure Two else pure One
  size One n = n + 2
  size Two n = n + 2
  size Three n = n + 2
  size Four n = n + 3
  size Five n = n + 3

instance Flat Unit where
  encode Unit = mempty
  decode = pure Unit
  size _ = id

instance Flat a => Flat (List a) where
  encode (C x xs) = eFalse <> encode x <> encode xs
  encode N = eTrue
  decode = do
    tag <- dBool
    if tag then pure N else C <$> decode <*> decode
  size (C x xs) n = 1 + size x (size xs n)
  size N n = 1 + n

instance Flat a => Flat (Tree a) where
  encode (Node l r) = eFalse <> encode l <> encode r
  encode (Leaf x) = eTrue <> encode x
  decode = do
    tag <- dBool
    if tag then Leaf <$> decode else Node <$> decode <*> decode
  size (Node l r) n = 1 + size l (size r n)
  size (Leaf x) n = 1 + size x n

instance Flat Direction where
  encode North = eBits16 2 0
  encode South = eBits16 2 1
  encode Center = eBits16 2 2
  encode East = eBits16 3 6
  encode West = eBits16 3 7
  decode = do
    tag <- dBool
    if tag
      then do
        tag2 <- dBool
        if tag2
          then do
            tag3 <- dBool
            if tag3 then pure West else pure East
          else pure Center
      else do
        tag2 <- dBool
        if tag2 then pure South else pure North
  size North n = n + 2
  size South n = n + 2
  size Center n = n + 2
  size East n = n + 3
  size West n = n + 3

instance Flat Words where
  encode (Words a b c d) = encode a <> encode b <> encode c <> encode d
  decode = Words <$> decode <*> decode <*> decode <*> decode
  size (Words a b c d) n = size a (size b (size c (size d n)))

instance Flat Ints where
  encode (Ints a b c d) = encode a <> encode b <> encode c <> encode d
  decode = Ints <$> decode <*> decode <*> decode <*> decode
  size (Ints a b c d) n = size a (size b (size c (size d n)))

instance Flat Void where
  encode _ = error "Void"
  decode = error "Void"
  size _ = id

instance Flat N3 where
  encode N1 = eFalse
  encode N2 = eTrue <> eFalse
  encode N3 = eTrue <> eTrue
  decode = do
    tag <- dBool
    if tag
      then do
        tag2 <- dBool
        if tag2 then pure N3 else pure N2
      else pure N1
  size N1 n = n + 1
  size _ n = n + 2

instance Flat Un where
  encode (Un b) = encode b
  decode = Un <$> decode
  size (Un b) = size b

instance Flat a => Flat (ListS a) where
  encode Nil = eFalse
  encode (Cons x xs) = eTrue <> encode x <> encode xs
  decode = do
    tag <- dBool
    if tag then Cons <$> decode <*> decode else pure Nil
  size Nil n = 1 + n
  size (Cons x xs) n = 1 + size x (size xs n)

instance Flat A where
  encode (A b) = eFalse <> encode b
  encode (AA i) = eTrue <> encode i
  decode = do
    tag <- dBool
    if tag then AA <$> decode else A <$> decode
  size (A b) n = 1 + size b n
  size (AA i) n = 1 + size i n

instance Flat B where
  encode (B a) = eFalse <> encode a
  encode (BB c) = eTrue <> encode c
  decode = do
    tag <- dBool
    if tag then BB <$> decode else B <$> decode
  size (B a) n = 1 + size a n
  size (BB c) n = 1 + size c n

instance Flat D2 where
  encode (D2 b n) = encode b <> encode n
  decode = D2 <$> decode <*> decode
  size (D2 b n) s = size b (size n s)

instance Flat D4 where
  encode (D4 a b c d) = encode a <> encode b <> encode c <> encode d
  decode = D4 <$> decode <*> decode <*> decode <*> decode
  size (D4 a b c d) n = size a (size b (size c (size d n)))

instance Flat a => Flat (Phantom a) where
  encode Phantom = mempty
  decode = pure Phantom
  size _ = id

-- Slow to compile
instance Flat Various where
  encode (V1 x) = eBits16 2 0 <> encode x
  encode (V2 a b) = eBits16 3 2 <> encode a <> encode b
  encode (VF a b c) = eBits16 3 3 <> encode a <> encode b <> encode c
  encode (VW a b c d e) = eBits16 2 2 <> encode a <> encode b <> encode c <> encode d <> encode e
  encode (VI a b c d e) = eBits16 3 6 <> encode a <> encode b <> encode c <> encode d <> encode e
  encode (VII a b c) = eBits16 3 7 <> encode a <> encode b <> encode c
  decode = do
    tag <- dBool
    if tag
      then do
        tag2 <- dBool
        if tag2
          then do
            tag3 <- dBool
            if tag3
              then VII <$> decode <*> decode <*> decode
              else VI <$> decode <*> decode <*> decode <*> decode <*> decode
          else VW <$> decode <*> decode <*> decode <*> decode <*> decode
      else do
        tag2 <- dBool
        if tag2
          then do
            tag3 <- dBool
            if tag3
              then VF <$> decode <*> decode <*> decode
              else V2 <$> decode <*> decode
          else V1 <$> decode
  size (V1 x) n = 2 + size x n
  size (V2 a b) n = 3 + size a (size b n)
  size (VF a b c) n = 3 + size a (size b (size c n))
  size (VW a b c d e) n = 2 + size a (size b (size c (size d (size e n))))
  size (VI a b c d e) n = 3 + size a (size b (size c (size d (size e n))))
  size (VII a b c) n = 3 + size a (size b (size c n))

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
-- instance   Flat a => Flat (Stream a) where decode = Stream <$> decode <*> decode
-- instance Flat Expr
-- instance (Flat a,Flat (f a),Flat (f (f a))) => Flat (PerfectF f a)
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
-- instance Flat N
