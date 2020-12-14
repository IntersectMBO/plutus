module StaticAnalysis.StaticTools (closeZipperContract, countSubproblems, getNextSubproblem, initSubproblems, zipperToContractPath) where

import Prelude
import Data.List (List(..), foldl, fromFoldable, length, snoc, toUnfoldable)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Marlowe.Semantics (Case(..), Contract(..), Observation(..))
import Simulation.Types (ContractPath, ContractPathStep(..), ContractZipper(..), RemainingSubProblemInfo)

splitArray :: forall a. List a -> List (List a /\ a /\ List a)
splitArray x = splitArrayAux Nil x

splitArrayAux :: forall a. List a -> List a -> List (List a /\ a /\ List a)
splitArrayAux _ Nil = Nil

splitArrayAux l (Cons h t) = Cons (l /\ h /\ t) (splitArrayAux (Cons h l) t)

expandChildren :: ContractZipper -> Contract -> RemainingSubProblemInfo
expandChildren _ Close = Nil

expandChildren zipper (Pay accId payee tok val cont) = Cons (PayZip accId payee tok val zipper /\ cont) Nil

expandChildren zipper (If obs cont1 cont2) = Cons (IfTrueZip obs zipper cont2 /\ cont1) (Cons (IfFalseZip obs cont1 zipper /\ cont2) Nil)

expandChildren zipper (When cases tim tcont) =
  snoc
    ( map (\(before /\ Case act cont /\ after) -> WhenCaseZip before act zipper after tim tcont /\ cont)
        (splitArray (fromFoldable cases))
    )
    (WhenTimeoutZip cases tim zipper /\ tcont)

expandChildren zipper (Let valId val cont) = Cons (LetZip valId val zipper /\ cont) Nil

expandChildren zipper (Assert obs cont) = Cons (AssertZip obs zipper /\ cont) Nil

closeZipperContract :: ContractZipper -> Contract -> Contract
closeZipperContract (PayZip accId payee tok val zipper) cont = closeZipperContract zipper (Pay accId payee tok val cont)

closeZipperContract (IfTrueZip obs zipper cont2) cont1 = closeZipperContract zipper (If obs cont1 cont2)

closeZipperContract (IfFalseZip obs cont1 zipper) cont2 = closeZipperContract zipper (If obs cont1 cont2)

closeZipperContract (WhenCaseZip bef act zipper aft tim timcont) cont =
  let
    thisCase = Case act cont

    cases = toUnfoldable (foldl (flip Cons) (Cons thisCase aft) bef)
  in
    closeZipperContract zipper (When cases tim timcont)

closeZipperContract (WhenTimeoutZip cases tim zipper) timcont = closeZipperContract zipper (When cases tim timcont)

closeZipperContract (LetZip valId val zipper) cont = closeZipperContract zipper (Let valId val cont)

closeZipperContract (AssertZip obs zipper) cont = closeZipperContract zipper (Assert obs cont)

closeZipperContract HeadZip cont = cont

zipperToContractPathAux :: ContractZipper -> ContractPath -> ContractPath
zipperToContractPathAux (PayZip _ _ _ _ zipper) p = zipperToContractPathAux zipper (Cons PayContPath p)

zipperToContractPathAux (IfTrueZip _ zipper _) p = zipperToContractPathAux zipper (Cons IfTruePath p)

zipperToContractPathAux (IfFalseZip _ _ zipper) p = zipperToContractPathAux zipper (Cons IfFalsePath p)

zipperToContractPathAux (WhenCaseZip bef _ zipper _ _ _) p = zipperToContractPathAux zipper (Cons (WhenCasePath (length bef)) p)

zipperToContractPathAux (WhenTimeoutZip _ _ zipper) p = zipperToContractPathAux zipper (Cons WhenTimeoutPath p)

zipperToContractPathAux (LetZip _ _ zipper) p = zipperToContractPathAux zipper (Cons LetPath p)

zipperToContractPathAux (AssertZip _ zipper) p = zipperToContractPathAux zipper (Cons AssertPath p)

zipperToContractPathAux HeadZip p = p

zipperToContractPath :: ContractZipper -> ContractPath
zipperToContractPath zipper = zipperToContractPathAux zipper Nil

nullifyAsserts :: Contract -> Contract
nullifyAsserts Close = Close

nullifyAsserts (Pay accId payee tok val cont) = Pay accId payee tok val (nullifyAsserts cont)

nullifyAsserts (If obs cont1 cont2) = If obs (nullifyAsserts cont1) (nullifyAsserts cont2)

nullifyAsserts (When cases timeout timCont) =
  When
    ( do
        Case act cont <- cases
        pure (Case act (nullifyAsserts cont))
    )
    timeout
    (nullifyAsserts timCont)

nullifyAsserts (Let valId val cont) = Let valId val (nullifyAsserts cont)

nullifyAsserts (Assert obs cont) = Assert TrueObs cont

initSubproblems :: Contract -> RemainingSubProblemInfo
initSubproblems c = Cons (HeadZip /\ c) Nil

countFix :: forall a. (a -> Maybe a) -> a -> Int
countFix fun a0 = countFix_tailrec fun a0 0
  where
  countFix_tailrec :: (a -> Maybe a) -> a -> Int -> Int
  countFix_tailrec f a acc = case f a of
    Nothing -> acc
    Just newA -> countFix_tailrec f newA (acc + 1)

countSubproblems :: (ContractZipper -> Contract -> Boolean) -> RemainingSubProblemInfo -> Int
countSubproblems _ Nil = 0

countSubproblems filterFun subproblemInfo = countFix fixpointFun (Nil /\ subproblemInfo)
  where
  fixpointFun :: (RemainingSubProblemInfo /\ RemainingSubProblemInfo) -> Maybe (RemainingSubProblemInfo /\ RemainingSubProblemInfo)
  fixpointFun (children /\ subproblems) = map (\((_ /\ _ /\ c) /\ a) -> (c /\ a)) $ getNextSubproblem filterFun subproblems children

getNextSubproblem ::
  (ContractZipper -> Contract -> Boolean) ->
  RemainingSubProblemInfo ->
  RemainingSubProblemInfo ->
  Maybe ((ContractZipper /\ Contract /\ RemainingSubProblemInfo) /\ RemainingSubProblemInfo)
getNextSubproblem _ Nil Nil = Nothing

getNextSubproblem f (Cons (zipper /\ contract) rest) Nil =
  if f zipper contract then
    Just ((zipper /\ contract /\ children) /\ rest)
  else
    getNextSubproblem f rest children
  where
  children = expandChildren zipper contract

getNextSubproblem f acc newChildren = getNextSubproblem f (acc <> newChildren) Nil
