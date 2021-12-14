-- | CSV parser as specified in RFC4180
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Foundation.Format.CSV.Parser
    ( file
    , recordC
    , record
    , record_
    , field
    ) where

import Basement.Imports hiding (throw)
import Foundation.Format.CSV.Types
import Basement.String (snoc)
import Foundation.Parser
import Foundation.Monad
import Foundation.Collection (Collection (elem))
import Foundation.Conduit
import Control.Monad (void)
import Data.Typeable (typeRep)
import Data.Proxy (Proxy(..))

recordC :: (Monad m, MonadThrow m) => Conduit String Row m ()
recordC = awaitForever $ recordC' . parse (record <* optional (elements crlf))
  where
    recordC' (ParseFailed err) = throw err
    recordC' (ParseOk rest v)  = leftover rest *> yield v
    recordC' (ParseMore more)  = do
        mm <- await
        case mm of
            Nothing -> throw (NotEnoughParseOnly :: ParseError String)
            Just b  -> recordC' (more b)

record_ :: forall row . (Typeable row, Record row) => Parser String row
record_ = do
    rs <- record
    case fromRow rs of
        Left err -> reportError $ Expected (show $ typeRep (Proxy @row)) err
        Right v  -> pure v

file :: Parser String CSV
file = do
    mh <- optional $ header <* elements crlf
    x <- record
    xs <- some $ elements crlf *> record
    void $ optional $ elements crlf
    pure $ fromList $ case mh of
        Nothing -> x : xs
        Just h  -> h : x : xs

header :: Parser String Row
header = do
    x <- name
    xs <- some $ element comma *> name
    pure $ fromList $ x : xs

record :: Parser String Row
record = do
    x <- field
    xs <- some $ element comma *> field
    pure $ fromList $ x : xs

name :: Parser String Field
name = field
{-# INLINE name #-}

field :: Parser String Field
field = escaped <|> nonEscaped

escaped :: Parser String Field
escaped = element dquote *> escaped'
  where
    escaped' = do
        x <- takeWhile (dquote /=)
        element dquote
        p <- peek
        if p == (Just dquote)
            then skip 1 >> descaped' (snoc x dquote)
            else pure (FieldString x Escape)
    descaped' acc = do
        x <- takeWhile (dquote /=)
        element dquote
        p <- peek
        if p == (Just dquote)
            then skip 1 >> descaped' (acc <> snoc x dquote)
            else pure (FieldString (acc <> x) DoubleEscape)

nonEscaped :: Parser String Field
nonEscaped = flip FieldString NoEscape <$> takeWhile (not . flip elem specials)
{-# INLINE nonEscaped #-}

comma :: Char
comma = ','
{-# INLINE comma #-}

cr :: Char
cr = '\r'
{-# INLINE cr #-}

dquote :: Char
dquote = '"'
{-# INLINE dquote #-}

lf :: Char
lf = '\n'
{-# INLINE lf #-}

crlf :: String
crlf = fromList [cr, lf]
{-# NOINLINE crlf #-}

{-
textdataQuoted :: String
textdataQuoted = textdata <> specials
{-# NOINLINE textdataQuoted #-}
-}

specials :: String
specials = ",\r\n"
{-# INLINE specials #-}

{-
textdata :: String
textdata = fromList $ [' '..'!'] <> ['#'..'+'] <> ['-'..'~']
{-# NOINLINE textdata #-}
-}
