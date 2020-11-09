module Language.Marlowe.ACTUS.Agda.AgdaGen(genDefinition, genModule, ident, genImport) where

import           Agda.Syntax.Common                                    (NamedArg, MaybePlaceholder, ExpandedEllipsis(..), ImportDirective'(..), Using'(..), RawName(..), noPlaceholder, defaultNamedArg, defaultArgInfo, defaultArg)
import           Agda.Syntax.Position                                  (Range'(..))
import           Agda.Syntax.Literal                                   (Literal(..))
import           Agda.Syntax.Concrete                                  (Expr(..), OpApp(..), Declaration(..), WhereClause'(..), LHS(..), RHS'(..), Pattern(..), OpenShortHand(..))
import           Agda.Syntax.Concrete.Name                             (Name(..), QName(..), NameInScope(..), NamePart(..))
import           Data.List.NonEmpty                                    (NonEmpty(..))
import           Agda.Utils.List2                                      (List2(..))

paramName :: RawName -> Name
paramName nm = Name NoRange NotInScope $ Id nm :| []

ident :: String -> Expr
ident param = Ident $ QName $ paramName param where

genImport :: String -> Declaration
genImport name = Import NoRange (QName $ paramName name) Nothing DoOpen $ ImportDirective NoRange UseEverything [] [] Nothing

genDefinition :: Expr -> String -> String -> [String] -> [String] -> String -> [Declaration]
genDefinition expr name param1 params inputTypes outputType = 
    let fName = Name NoRange NotInScope $ Id name :| []
        toParamP param = IdentP $ QName $ paramName param
        toParam param = Ident $ QName $ paramName param
        lhsPattern = 
            RawAppP NoRange $ List2 (IdentP $ QName fName) (toParamP param1) (toParamP <$> params)
        lhs = LHS lhsPattern [] [] NoEllipsis
        rhs = RHS $ expr
        funsigChunk paramType cont = Fun NoRange (defaultArg (toParam paramType)) cont
        funsigTerminal = toParam outputType
        funsig = foldr funsigChunk funsigTerminal inputTypes
    in [TypeSig defaultArgInfo Nothing fName funsig, FunClause lhs rhs NoWhere False]

genModule :: String -> [Declaration] -> Declaration
genModule name declarations = 
    let moduleName = QName (Name NoRange NotInScope $ Id name :| [])
    in Module NoRange moduleName [] declarations