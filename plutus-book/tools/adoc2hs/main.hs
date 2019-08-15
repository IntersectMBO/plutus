{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

import           Data.List          (isInfixOf, isPrefixOf, isSuffixOf)
import           Options.Generic
import           Pipes
import qualified Pipes.Prelude      as P
import           Pipes.Safe
import qualified Pipes.Safe.Prelude as S

main :: IO ()
main = do
    p <- getRecord "adoc2hs" :: IO Params
    let (prod, con) = fromParams p
    runSafeT $ runEffect $ prod >-> process >-> con

data Params = Params
    { source :: Maybe FilePath
    , target :: Maybe FilePath
    } deriving (Show, Generic)

instance ParseRecord Params

fromParams :: MonadSafe m
           => Params
           -> ( Proxy x' x () String m ()
              , Proxy () String y' y m ()
              )
fromParams p =
    let prod = case source p of
                Nothing -> P.stdinLn
                Just s  -> S.readFile s
        con  = case target p of
                Nothing -> P.stdoutLn
                Just t  -> S.writeFile t
    in  (prod, con)

data State = D | SH | H
    deriving (Show, Eq, Ord)

process :: Monad m => Pipe String String m ()
process = go D
  where
    go x = do
        s  <- await
        s' <- case x of
            D  -> if sh  s then return SH else            return D
            SH -> if sep s then return H  else            return D
            H  -> if sep s then return D  else yield s >> return H
        go s'

    sep = isPrefixOf "----"

    sh s =
        isPrefixOf "[" s &&
        isInfixOf "source" s &&
        isInfixOf "haskell" s &&
        isSuffixOf "]" s
