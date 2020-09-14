{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -w #-}
module OldAnalysis.MkSymb where

import           Data.Either         (Either (..))
import           Data.List           (foldl', foldl1')
import           Data.SBV
import           Data.SBV.Either     as SE
import           Data.SBV.Tuple      as ST
import           Language.Haskell.TH as TH

nestClauses :: [Con] -> TypeQ
nestClauses [] = error "No constructors for type"
nestClauses [NormalC _ [(_, t)]] = return t -- Special case 1-tuples
nestClauses [NormalC _ params] =
  foldl' appT (tupleT (length params)) [return t | (_, t) <- params]
nestClauses list = appT (appT [t| Either |]
                              (nestClauses fHalf))
                        (nestClauses sHalf)
  where ll = length list
        (fHalf, sHalf) = splitAt (ll - (length list `div` 2)) list

mkNestedDec :: [TyVarBndr] -> TH.Name -> [Con] -> TH.Q TH.Dec
mkNestedDec tvs nName clauses =
  tySynD nName tvs $ nestClauses clauses

getTVName :: TyVarBndr -> TH.Name
getTVName (PlainTV name)    = name
getTVName (KindedTV name _) = name

addTVs :: [TyVarBndr] -> TypeQ -> TypeQ
addTVs tvs con = foldl' appT con $ map (varT . getTVName) tvs

mkSymDec :: [TyVarBndr] -> TH.Name -> TH.Name -> TH.Q TH.Dec
mkSymDec tvs sName nName =
  tySynD sName tvs [t| SBV $(foldl' appT (conT nName) $ map (varT . getTVName) tvs) |]

mkSubSymDec :: [TyVarBndr] -> TH.Name -> [Con] -> TH.Q TH.Dec
mkSubSymDec tvs ssName clauses =
  dataD (return [])
        ssName
        tvs Nothing [ normalC (let typeBaseName = nameBase name in
                               mkName ('S':'S':typeBaseName))
                              [ bangType (return pb)
                                         [t| SBV $(return param) |]
                               | (pb, param) <- params ]
                     | NormalC name params <- clauses ]
        []

nestFunClauses :: [Con] -> (ExpQ -> ExpQ) -> [ClauseQ]
nestFunClauses [] f = error "No constructors for type"
nestFunClauses [NormalC name params] f =
  [do names <- mapM (\x -> newName ('p':show x)) [1..(length params)]
      let tup = case names of
              [n] -> varE n -- Special-case 1-tuples
              _   -> tupE (map varE names)
      clause [ conP name [ varP n | n <- names ] ]
             (normalB (f tup)) []]
nestFunClauses list f = nestFunClauses fHalf (f . (\x -> [e| Left $(x) |])) ++
                        nestFunClauses sHalf (f . (\x -> [e| Right $(x) |]))
  where ll = length list
        (fHalf, sHalf) = splitAt (ll - (length list `div` 2)) list

addSymValToTVs :: [TyVarBndr] -> TypeQ -> TypeQ
addSymValToTVs [] ty = ty
addSymValToTVs tvs ty =
  do x <- [t| SymVal |]
     ForallT [] [AppT x (VarT $ getTVName tv) | tv <- tvs] <$> ty

mkNestFunc :: [TyVarBndr] -> String -> TH.Name -> TH.Name -> [Con] -> TH.Q [TH.Dec]
mkNestFunc tvs typeBaseName typeName typeNName clauses =
  do let nestFunName = "nest" ++ typeBaseName
     let nfName = mkName nestFunName
     signature <- sigD nfName (addSymValToTVs tvs
                                (appT (appT arrowT (addTVs tvs $ conT typeName))
                                            (addTVs tvs $ conT typeNName)))
     declaration <- funD nfName $ nestFunClauses clauses id
     return [signature, declaration]

unNestFunClauses :: [Con] -> (PatQ -> PatQ) -> [ClauseQ]
unNestFunClauses [] f = error "No constructors for type"
unNestFunClauses [NormalC name params] f =
  [do names <- mapM (\x -> newName ('p':show x)) [1..(length params)]
      let pat = case names of
              [n] -> varP n -- Special case 1-tuples
              _   -> tupP (map varP names)
      clause [f pat]
             (normalB (foldl' appE (conE name) [ varE n | n <- names ])) []]
unNestFunClauses list f = unNestFunClauses fHalf (f . (\x -> [p| Left $(x) |])) ++
                          unNestFunClauses sHalf (f . (\x -> [p| Right $(x) |]))
  where ll = length list
        (fHalf, sHalf) = splitAt (ll - (length list `div` 2)) list

mkUnNestFunc :: [TyVarBndr] -> String -> TH.Name -> TH.Name -> [Con] -> TH.Q [TH.Dec]
mkUnNestFunc tvs typeBaseName typeName typeNName clauses =
  do let unNestFunName = "unNest" ++ typeBaseName
     let unfName = mkName unNestFunName
     signature <- sigD unfName (appT (appT arrowT (addTVs tvs $ conT typeNName))
                                           (addTVs tvs $ conT typeName))
     declaration <- funD unfName $ unNestFunClauses clauses id
     return [signature, declaration]

mkSymCaseRec :: Name -> [Con] -> ExpQ
mkSymCaseRec func [] = error "No constructors for type"
mkSymCaseRec func [NormalC name params] =
  do paramNames <- mapM (\x -> newName ('p':show x)) [1..(length params)]
     let ssName = mkName ('S':'S':nameBase name)
     let pat = case paramNames of
             [n] -> varP n -- Special case 1-tuples
             _   -> tupP $ map varP paramNames
     let wrapping = [e| (\ $(pat) ->
                        $(varE func)
                        $(foldl' appE (conE ssName) $ map varE paramNames)) |]
     if length params > 1
     then [e| $(wrapping) . ST.untuple |]
     else if not (null params)
          then wrapping
          else [e| $(wrapping) . const () |]
mkSymCaseRec func list = [e| SE.either $(mkSymCaseRec func fHalf)
                                       $(mkSymCaseRec func sHalf) |]
  where ll = length list
        (fHalf, sHalf) = splitAt (ll - (length list `div` 2)) list

mkSymCase :: [TyVarBndr] -> String -> TH.Name -> TH.Name -> [Con] -> TH.Q [TH.Dec]
mkSymCase tvs typeBaseName sName ssName clauses =
  do let symCaseFunName = "symCase" ++ typeBaseName
     let scName = mkName symCaseFunName
     typeVar <- newName "a"
     func <- newName "f"
     signature <- sigD scName $ addSymValToTVs tvs
                                [t| SymVal $(varT typeVar) =>
                                    ($(addTVs tvs $ conT ssName)
                                     -> SBV $(varT typeVar))
                                 -> $(addTVs tvs $ conT sName)
                                 -> SBV $(varT typeVar) |]
     declaration <- funD scName
                    [clause [varP func]
                            (normalB (mkSymCaseRec func clauses)) []]
     return [signature, declaration]

mkSymConsts :: [TyVarBndr] -> TH.Name -> [Con] -> (ExpQ -> ExpQ) -> TH.Q [TH.Dec]
mkSymConsts tvs _ [] f = error "No constructors for type"
mkSymConsts tvs sName [NormalC name params] f =
  do let nestFunName = "s" ++ nameBase name
     let nfName = mkName nestFunName
     signature <- sigD nfName $ addSymValToTVs tvs
                                (foldl1' (\x y -> appT (appT arrowT y) x)
                                  (addTVs tvs(conT sName):
                                    reverse [ [t| SBV $(return param) |]
                                             | (_, param) <- params ]))
     declaration <- funD nfName
       [do names <- mapM (\x -> newName ('p':show x)) [1..(length params)]
           clause [ varP n | n <- names ]
                  (normalB (f (case names of
                                 (x:y:xs) -> [e| ST.tuple $(tupE (map varE names)) |]
                                 [n]      -> varE n -- Special case 1-tuples, SBV tuple doesn't support them properly
                                 []       -> [e| literal () |]))) []]
     return [signature, declaration]
mkSymConsts tvs sName list f =
  do rfHalf <- mkSymConsts tvs sName fHalf (f . (\x -> [e| sLeft $(x) |]))
     rsHalf <- mkSymConsts tvs sName sHalf (f . (\x -> [e| sRight $(x) |]))
     return (rfHalf ++ rsHalf)
  where ll = length list
        (fHalf, sHalf) = splitAt (ll - (length list `div` 2)) list

mkSymbolicDatatype :: TH.Name -> TH.Q [TH.Dec]
mkSymbolicDatatype typeName =
  do TyConI (DataD _ _ tvs _ clauses _) <- reify typeName
     let typeBaseName = nameBase typeName
     let sName = mkName ('S':typeBaseName)
     let nName = mkName ('N':typeBaseName)
     let ssName = mkName ('S':'S':typeBaseName)
     nestedDecl <- mkNestedDec tvs nName clauses
     symDecl <- mkSymDec tvs sName nName
     subSymDecl <- mkSubSymDec tvs ssName clauses
     nestFunc <- mkNestFunc tvs typeBaseName typeName nName clauses
     unNestFunc <- mkUnNestFunc tvs typeBaseName typeName nName clauses
     symCaseFunc <- mkSymCase tvs typeBaseName sName ssName clauses
     symConsts <- mkSymConsts tvs sName clauses id
     return (nestedDecl:symDecl:subSymDecl:
             (nestFunc ++ unNestFunc ++ symCaseFunc ++ symConsts))
