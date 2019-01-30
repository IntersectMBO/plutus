{-# LANGUAGE OverloadedStrings #-}
module TestLib where

import           Common

import           Language.PlutusCore.Quote
import           Language.PlutusIR

import           Data.Text.Prettyprint.Doc

goldenPir :: String -> Term TyName Name a -> TestNested
goldenPir name value = nestedGoldenVsDoc name $ pretty value

maybeDatatype :: Datatype TyName Name ()
maybeDatatype = runQuote $ do
    m <- freshTyName () "Maybe"
    a <- freshTyName () "a"
    match <- freshName () "match_Maybe"
    nothing <- freshName () "Nothing"
    just <- freshName () "Just"

    pure $
        Datatype ()
            (TyVarDecl () m (KindArrow () (Type ()) (Type ())))
            [
                TyVarDecl () a (Type ())
            ]
        match
        [
            VarDecl () nothing (TyApp () (TyVar () m) (TyVar () a)),
            VarDecl () just (TyFun () (TyVar () a) (TyApp () (TyVar () m) (TyVar () a)))
        ]

listDatatype :: Datatype TyName Name ()
listDatatype = runQuote $ do
    m <- freshTyName () "List"
    a <- freshTyName () "a"
    let ma = TyApp () (TyVar () m) (TyVar () a)
    match <- freshName () "match_List"
    nil <- freshName () "Nil"
    cons <- freshName () "Cons"

    pure $
        Datatype ()
            (TyVarDecl () m (KindArrow () (Type ()) (Type ())))
            [
                TyVarDecl () a (Type ())
            ]
        match
        [
            VarDecl () nil ma,
            VarDecl () cons (TyFun () (TyVar () a) (TyFun () ma ma))
        ]

treeForestDatatype :: (Datatype TyName Name (), Datatype TyName Name ())
treeForestDatatype = runQuote $ do
    tree <- freshTyName () "Tree"
    a <- freshTyName () "a"
    let treeA arg = TyApp () (TyVar () tree) (TyVar () arg)
    node <- freshName () "Node"
    matchTree <- freshName () "match_Tree"

    forest <- freshTyName () "Forest"
    a2 <- freshTyName () "a"
    let forestA arg = TyApp () (TyVar () forest) (TyVar () arg)
    nil <- freshName () "Nil"
    cons <- freshName () "Cons"
    matchForest <- freshName () "match_Forest"

    let treeDt = Datatype ()
          (TyVarDecl () tree (KindArrow () (Type ()) (Type ())))
          [
              TyVarDecl () a (Type ())
          ]
          matchTree
          [
              VarDecl () node (TyFun () (TyVar () a) (TyFun () (forestA a) (treeA a)))
          ]
    let forestDt = Datatype ()
          (TyVarDecl () forest (KindArrow () (Type ()) (Type ())))
          [
              TyVarDecl () a2 (Type ())
          ]
          matchForest
          [
              VarDecl () nil (forestA a2),
              VarDecl () cons (TyFun () (treeA a2) (TyFun () (forestA a2) (forestA a2)))
          ]
    pure (treeDt, forestDt)
