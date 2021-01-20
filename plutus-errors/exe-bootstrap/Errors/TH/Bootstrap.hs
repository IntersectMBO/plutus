-- | (Re)generate ErrorCode instances for initial errors
{-# LANGUAGE TemplateHaskell #-}
module Errors.TH.Bootstrap (
    bootstrap
    ) where

import           Data.Foldable
import           Data.Map                     as M
import           ErrorCode
import           Language.Haskell.TH
import           Language.Haskell.TH.Datatype
import           Numeric.Natural

{- |
The purpose of this function is to help in the (re)-generation of 'HasErrorCode' instances
for Plutus-errors/data-constructors. The user can call this function as a script to
get the generated instances as Haskell code and paste/modify it accordingly next to the errors (for avoiding orphans).
The function works by assigning a unique number to each dataconstructor, starting counting from 1.
The function groups the data-constructors by their "parent" type-constructor,
so the order that they are given in the input list does not matter.
-}
bootstrap :: [Name] -> Q Exp
bootstrap constrs = do
    -- group data-constructors by their parent type-constructor
    groups <- groupConstrs constrs

    -- the first error-code to use for generating instances
    let startErrorCode = 1 :: Natural

    -- traverse the groups in ascending order to generate `HasErrorCode Group` instances,
    -- while threading an increasing number of a currently unused error-code.
    let (_, insts) = foldlWithKey mkInstanceAccIx
                     (startErrorCode, []) groups

    -- Haskell-prettyprint the instances
    let decs = StringL $ pprint insts
    [| putStr $(litE decs) |]

-- | An intermediate structure to group data-constructors by their parent type-constructor and number of tyvars
type Group = (ParentName,Int)

-- | Groups a list of (possibly-unrelated) dataconstructors by their parent typeconstructor
groupConstrs :: [Name] -> Q (Map Group [Name])
groupConstrs ns = foldlM groupByParent mempty ns
  where
    groupByParent :: Map Group [Name] -> Name -> Q (Map Group [Name])
    groupByParent acc d = do
        dataInfo <- reifyDatatype d
        pure $ M.insertWith (++) (datatypeName dataInfo, length $ datatypeVars dataInfo) [d] acc

-- Using a given errorcode index and a groupping, return
-- a new errorcode index and the HasErrorCode instance for that group.
mkInstanceAccIx :: (Natural, [Dec]) -> Group -> [Name] -> (Natural, [Dec])
mkInstanceAccIx (ix, insts) curGroup curConstrs =
    let newInst = mkInstance ix curGroup curConstrs
        newIx = ix + (fromIntegral $ length curConstrs)
    in (newIx, newInst:insts)

-- Create a haskell-syntax declaration corresponding to
-- `instance TyCons _dummyTyVars where errorCode DataCons = ix`
mkInstance :: Natural -> Group -> [Name] -> Dec
mkInstance ix (parentName, countTyVars) constrs =
    let -- fully applied (kind: *) error type
        appliedTy = genSaturatedTypeCon parentName countTyVars
        -- assign an unused errorcode to each data-constructor in the group
        constrsIxs = zip constrs [ix :: Natural ..]

        -- Constructs an rhs from a constructor's name & an error-code index
        mkRhs (cname, cix) = Clause [RecP cname []]
                             (NormalB $ ConE 'ErrorCode `AppE` (LitE $ IntegerL $ toInteger cix)) []
        -- Constructs a dummy catch-all code for convenience
        -- note: leads to unsafety because it turns the method to a total function
        defaultRhs = Clause [WildP] (NormalB $ ConE 'ErrorCode `AppE` (LitE $ IntegerL 0)) []

        -- errorCode fun. implementation
        errorCodeFun = FunD (mkName "errorCode") $
                           fmap mkRhs constrsIxs ++ [defaultRhs]

    in InstanceD Nothing [] (AppT (ConT $ mkName "HasErrorCode") appliedTy) [errorCodeFun]

-- Helper to generate a saturated (fully-applied) type constructor
-- by applying it to somne dummy type variable names.
genSaturatedTypeCon :: Name -> Int -> Type
genSaturatedTypeCon tn 0 = ConT tn
genSaturatedTypeCon tn ix =
    genSaturatedTypeCon tn (ix-1) `AppT` VarT (mkName $ dummyTyVars !! (ix-1))
  where
    dummyTyVars :: [String]
    dummyTyVars = fmap (\c -> '_':[c]) ['a'..'z'] -- NOTE: breaks for more than 26 tyvars!
