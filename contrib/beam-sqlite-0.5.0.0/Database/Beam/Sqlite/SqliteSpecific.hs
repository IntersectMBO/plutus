{-# LANGUAGE OverloadedStrings #-}

-- | Postgres-specific types, functions, and operators
module Database.Beam.Sqlite.SqliteSpecific
    ( -- * Sqlite functions and aggregates
      sqliteGroupConcat
    , sqliteGroupConcatOver
    )
where

import           Database.Beam
import           Database.Beam.Backend.SQL
import           Database.Beam.Query.Internal
import           Database.Beam.Sqlite.Connection
import           Database.Beam.Sqlite.Syntax
#if !MIN_VERSION_base(4, 11, 0)
import           Data.Semigroup
#endif

-- | The SQLite @group_concat@ function.
-- Joins the value in each row of the first argument, using the second
-- argument as a delimiter. See 'sqliteGroupConcatOver' if you want to provide
-- explicit quantification.
sqliteGroupConcat
    :: ( BeamSqlBackendCanSerialize Sqlite a
       , BeamSqlBackendIsString Sqlite str
       , BeamSqlBackendIsString Sqlite str2 )
    => QExpr Sqlite s a
    -> QExpr Sqlite s str
    -> QAgg Sqlite s (Maybe str2)
sqliteGroupConcat v delim = _sqliteGroupConcatOver allInGroup_ v (Just delim)


-- | The SQLite @group_concat@ function.
-- Joins the value in each row of the first argument using ','.
-- See 'sqliteGroupConcat' if you want to change the delimiter.
-- Choosing a custom delimiter and quantification isn't allowed by SQLite.
sqliteGroupConcatOver
    :: ( BeamSqlBackendCanSerialize Sqlite a
       , BeamSqlBackendIsString Sqlite str )
    => Maybe SqliteAggregationSetQuantifierSyntax
    -> QExpr Sqlite s a
    -> QAgg Sqlite s (Maybe str)
sqliteGroupConcatOver quantifier v = _sqliteGroupConcatOver quantifier v Nothing

-- SQLite doesn't allow DISTINCT and a custom delimiter
_sqliteGroupConcatOver
    :: ( BeamSqlBackendCanSerialize Sqlite a
       , BeamSqlBackendIsString Sqlite str )
    => Maybe SqliteAggregationSetQuantifierSyntax
    -> QExpr Sqlite s a
    -> Maybe (QExpr Sqlite s str2)
    -> QAgg Sqlite s (Maybe str)
_sqliteGroupConcatOver quantifier (QExpr v) delim =
    QExpr $ \tbl -> SqliteExpressionSyntax $
    emit "group_concat" <>
    parens ( maybe mempty (\q -> fromSqliteAggregationSetQuantifier q <> emit " ") quantifier <>
             fromSqliteExpression (v tbl) <>
             maybe mempty (\(QExpr d) -> emit ", " <> fromSqliteExpression (d tbl)) delim)
