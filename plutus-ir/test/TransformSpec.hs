{-# LANGUAGE OverloadedStrings #-}
module TransformSpec where

import           Common
import           TestLib

import           Language.PlutusCore.Quote

import           Language.PlutusIR
import           Language.PlutusIR.MkPir
import           Language.PlutusIR.Transform.ThunkRecursions

transform :: TestNested
transform = testNested "transform" [
    thunkRecursions
    ]

thunkRecursions :: TestNested
thunkRecursions = testNested "thunkRecursions" [
    goldenPir "listFold" listFold,
    goldenPir "monoMap" monoMap
    ]

listFold :: Term TyName Name ()
listFold = runQuote $  do
    {-
    This implements foldl:

        foldl : (a -> b -> a) -> a -> [b] -> a
        foldl f acc lst = case lst of
            [] -> acc
            x:xs -> foldl f (f acc x) xs
    -}
    lb@(Datatype _ d _ destr _) <- listDatatype
    avd <- do
        a <- freshTyName () "a"
        pure $ TyVarDecl () a (Type ())
    bvd <- do
        b <- freshTyName () "b"
        pure $ TyVarDecl () b (Type ())

    let fty = mkIterTyFun () [ mkTyVar () avd, mkTyVar () bvd ] (mkTyVar () avd)
    let accTy = mkTyVar () avd
    let listBTy = TyApp () (mkTyVar () d) (mkTyVar () bvd)

    let foldTy =
            mkIterTyForall () [avd, bvd] $
            mkIterTyFun () [fty, accTy, listBTy]
            (mkTyVar () avd)

    fvd <- do
        fn <- freshName () "foldl"
        pure $ VarDecl () fn foldTy
    fld <- do
        f <- freshName () "f"
        acc <- freshName () "acc"
        lst <- freshName () "lst"
        x <- freshName () "x"
        xs <- freshName () "xs"
        pure $
            LamAbs () f fty $
            LamAbs () acc accTy $
            LamAbs () lst listBTy $
            -- match {a}
            mkIterApp () (TyInst () (Var () destr) (mkTyVar () avd))
            [
                -- lst
                Var () lst,
                -- Nil case
                -- acc
                Var () acc,
                -- Cons case
                -- \(x:b) (xs::[b]) -> foldl f (f acc x) xs
                LamAbs () x (mkTyVar () bvd) $
                LamAbs () xs listBTy $
                mkIterApp () (mkVar () fvd)
                [
                    Var () f,
                    mkIterApp () (Var () f)
                    [
                        Var () acc,
                        Var () x
                    ],
                    Var () xs
                ]
            ]

    pure $
        Let () Rec [ DatatypeBind () lb ] $
        Let () Rec [ TermBind () fvd fld ] $ mkVar () fvd

monoMap :: Term TyName Name ()
monoMap = runQuote $ thunkRecursionsTerm =<< do
    {-
    This implements a monomorphic map (which does not need to be thunked):

        map : (1 -> 1) -> List 1 -> List 1
        map f lst = case lst of
            [] -> []
            x:xs -> f x : map f xs
    -}
    lb@(Datatype _ d _ destr [nil, cons]) <- listDatatype

    let elemTy = TyInt () 1

    let fty = TyFun () elemTy elemTy
    let listTy = TyApp () (mkTyVar () d) elemTy

    let mapTy =
            mkIterTyFun () [fty, listTy]
            listTy

    fvd <- do
        fn <- freshName () "map"
        pure $ VarDecl () fn mapTy
    fld <- do
        f <- freshName () "f"
        lst <- freshName () "lst"
        x <- freshName () "x"
        xs <- freshName () "xs"
        pure $
            LamAbs () f fty $
            LamAbs () lst listTy $
            -- match {elemTy}
            mkIterApp () (TyInst () (Var () destr) elemTy)
            [
                -- lst
                Var () lst,
                -- Nil case
                -- nil
                mkVar () nil,
                -- Cons case
                -- \(x:b) (xs::[b]) -> f x : map f xs
                LamAbs () x elemTy $
                LamAbs () xs listTy $
                mkIterApp () (mkVar () cons)
                [
                    -- f x
                    Apply () (Var () f) (Var () x),
                    -- map f xs
                    mkIterApp () (mkVar () fvd)
                    [
                        Var () f,
                        Var () xs
                    ]
                ]
            ]

    pure $
        Let () Rec [ DatatypeBind () lb ] $
        Let () Rec [ TermBind () fvd fld ] $ mkVar () fvd
