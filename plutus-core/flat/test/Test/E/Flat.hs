module Test.E.Flat () where

import PlutusCore.Flat
import PlutusCore.Flat.Decoder.Prim (dBEBits8, dBool)
import PlutusCore.Flat.Encoder (eBits16, eFalse, eTrue, mempty, (<>))
import Test.E
import Prelude hiding (mempty, (<>))

-- t = putStrLn $ gen 4

-- Test only, incorrect instances
-- Not faster than generated ones (at least up to E16)
gen :: Int -> String
gen numBits =
  let dt = "E" ++ show n
      n = 2 ^ numBits
      cs = zip [1 ..] $ map ((\n -> dt ++ "_" ++ n) . show) [1 .. n]
      dec n c = unwords ["      ", n, "-> return", c]
   in unlines
        [ unwords ["instance Flat", dt, "where"]
        , "  size _ n = n+" ++ show numBits
        , "  encode a = case a of"
        , unlines $ map (\(n, c) -> unwords ["    ", c, "-> eBits16", show numBits, show n]) cs
        , "  decode = do"
        , "     tag <- dBEBits8 " ++ show numBits
        , "     case tag of"
        , unlines $ map (\(n, c) -> dec (show n) c) cs
        , dec "_" (snd $ last cs)
        ]

instance Flat S3 where
  encode S_1 = eFalse
  encode (S_2 b) = eTrue <> eFalse <> encode b
  encode (S_3 c) = eTrue <> eTrue <> encode c
  decode = do
    tag <- dBool
    if tag
      then do
        tag2 <- dBool
        if tag2 then S_3 <$> decode else S_2 <$> decode
      else pure S_1
  size S_1 n = 1 + n
  size (S_2 b) n = 2 + size b n
  size (S_3 c) n = 2 + size c n

instance Flat E2 where
  encode E2_1 = eFalse
  encode E2_2 = eTrue
  decode = do
    tag <- dBool
    if tag then pure E2_2 else pure E2_1
  size _ n = n + 1

instance Flat E3 where
  encode E3_1 = eFalse
  encode E3_2 = eTrue <> eFalse
  encode E3_3 = eTrue <> eTrue
  decode = do
    tag <- dBool
    if tag
      then do
        tag2 <- dBool
        if tag2 then pure E3_3 else pure E3_2
      else pure E3_1
  size E3_1 n = n + 1
  size _ n = n + 2

instance Flat E4 where
  encode E4_1 = eBits16 2 0
  encode E4_2 = eBits16 2 1
  encode E4_3 = eBits16 2 2
  encode E4_4 = eBits16 2 3
  decode = do
    tag <- dBEBits8 2
    case tag of
      0 -> pure E4_1
      1 -> pure E4_2
      2 -> pure E4_3
      _ -> pure E4_4
  size _ n = n + 2

instance Flat E8 where
  encode E8_1 = eBits16 3 0
  encode E8_2 = eBits16 3 1
  encode E8_3 = eBits16 3 2
  encode E8_4 = eBits16 3 3
  encode E8_5 = eBits16 3 4
  encode E8_6 = eBits16 3 5
  encode E8_7 = eBits16 3 6
  encode E8_8 = eBits16 3 7
  decode = do
    tag <- dBEBits8 3
    case tag of
      0 -> pure E8_1
      1 -> pure E8_2
      2 -> pure E8_3
      3 -> pure E8_4
      4 -> pure E8_5
      5 -> pure E8_6
      6 -> pure E8_7
      _ -> pure E8_8
  size _ n = n + 3

instance Flat E16 where
  encode x = eBits16 4 (fromIntegral (fromEnum x))
  decode = do
    tag <- dBEBits8 4
    pure (toEnum (fromIntegral tag))
  size _ n = n + 4

instance Flat E17 where
  encode x =
    let n = fromEnum x
     in if n < 15
          then eBits16 4 (fromIntegral n)
          else eBits16 5 (fromIntegral (n + 15))
  decode = do
    tag <- dBEBits8 4
    if tag < 15
      then pure (toEnum (fromIntegral tag))
      else do
        b <- dBool
        if b then pure E17_17 else pure E17_16
  size E17_16 n = n + 5
  size E17_17 n = n + 5
  size _ n = n + 4

instance Flat E32 where
  encode x = eBits16 5 (fromIntegral (fromEnum x))
  decode = do
    tag <- dBEBits8 5
    pure (toEnum (fromIntegral tag))
  size _ n = n + 5
