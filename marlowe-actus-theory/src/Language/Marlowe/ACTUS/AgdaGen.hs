


module Language.Marlowe.ACTUS.AgdaGen() where

import           Agda.Syntax.Common                                    (NamedArg, MaybePlaceholder, ExpandedEllipsis(..), noPlaceholder, defaultNamedArg)
import           Agda.Syntax.Position                                  (Range'(..))
import           Agda.Syntax.Literal                                   (Literal(..))
import           Agda.Syntax.Concrete                                  (Expr(..), OpApp(..), Declaration(..), WhereClause'(..), LHS(..), RHS'(..), Pattern(..))
import           Agda.Syntax.Concrete.Name                             (Name(..), QName(..), NameInScope(..), NamePart(..))
import           Data.List.NonEmpty                                    (NonEmpty(..))
import           Agda.Utils.List2                                      (List2(..))

genDefinition :: Expr -> String -> [String] -> [String] -> Declaration
genDefinition expr name params types = 
    let fName = Name NoRange NotInScope $ Id name :| []
        paramName = Name NoRange NotInScope $ Id "a" :| []
        lhsPattern = RawAppP NoRange $ List2 (IdentP $ QName fName) (IdentP $ QName paramName) []
        lhs = LHS lhsPattern [] [] NoEllipsis
        rhs = RHS $ expr
    in FunClause lhs rhs NoWhere False