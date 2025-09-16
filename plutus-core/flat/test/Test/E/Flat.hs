{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE StandaloneDeriving #-}
module Test.E.Flat() where

import PlutusCore.Flat
import PlutusCore.Flat.Decoder ()
import PlutusCore.Flat.Encoder ()
import Test.E

-- t = putStrLn $ gen 4

-- Test only, incorrect instances
-- Not faster than generated ones (at least up to E16)
gen :: Int -> String
gen numBits =
    let dt = "E"++show n
        n = 2 ^ numBits
        cs = zip [1..] $ map ((\n -> dt ++ "_" ++ n) . show) [1 .. n]
        dec n c = unwords ["      ",n,"-> return",c]
    in unlines [
        unwords ["instance Flat",dt,"where"]
        ,"  size _ n = n+"++ show numBits
        ,"  encode a = case a of"
        ,unlines $ map (\(n,c) -> unwords ["    ",c,"-> eBits16",show numBits,show n]) cs
        ,"  decode = do"
        ,"     tag <- dBEBits8 " ++ show numBits
        ,"     case tag of"
        ,unlines $ map (\(n,c) -> dec (show n) c) cs
        ,dec "_" (snd $ last cs)
        ]


deriving instance Flat S3
deriving instance Flat E2
deriving instance Flat E3
deriving instance Flat E4
deriving instance Flat E8
deriving instance Flat E16
deriving instance Flat E17
deriving instance Flat E32

#ifdef ENUM_LARGE
deriving instance Flat E256
deriving instance Flat E258
#endif

-- fs =
--     [ flat E2_1,flat E3_1
--     , flat E4_1
--     , flat E8_1
--     , flat E16_1
--     , flat E32_1
--     , flat E256_255
--     , flat E256_254
--     , flat E256_253
--     , flat E256_256
--     ]


