{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Webserver where

import           API                        (API)
import qualified Data.ByteString.UTF8       as BSU
import           Data.Pool                  (Pool, createPool)
import           Data.Proxy                 (Proxy (Proxy))
import           Database.PostgreSQL.Simple (Connection, close, connectPostgreSQL)
import           Network.Wai.Handler.Warp   as Warp (Settings, runSettings)
import           Servant                    (serve)
import qualified Server

import           Control.Exception          (bracket)
import qualified Data.ByteString            as BS

type DBConnectionString = BS.ByteString

initDB :: DBConnectionString -> IO ()
initDB connStr = bracket (connectPostgreSQL connStr) close $ \_conn -> do
  -- execute_ conn "CREATE TABLE IF NOT EXISTS messages (msg text not null)"
  return ()

initConnectionPool :: DBConnectionString -> IO (Pool Connection)
initConnectionPool connStr =
  createPool (connectPostgreSQL connStr)
             close
             2 -- stripes
             60 -- unused connections are kept open for a minute
             10 -- max. 10 connections open per stripe

run :: String -> FilePath -> Settings -> IO ()
run connStr staticPath settings = do
  let conn = BSU.fromString connStr
  pool <- initConnectionPool conn
  initDB conn
  let server = Server.handlers
  Warp.runSettings settings (serve (Proxy @API) (server pool staticPath))

miner :: String -> IO ()
miner connStr = bracket (connectPostgreSQL $ BSU.fromString connStr) close Server.miner
