module Reachability (startReachabilityAnalysis, updateWithResponse) where

import Data.Function (flip)
import Data.List (List(..), concatMap, foldl, fromFoldable, length, reverse, snoc, toUnfoldable)
import Data.Tuple.Nested (type (/\), (/\))
import Foreign.Generic (encode, encodeJSON)
import Global.Unsafe (unsafeStringify)
import Halogen (HalogenM)
import Halogen as H
import Marlowe.Semantics (AccountId, Case(..), Contract(..), Observation(..), Payee, Timeout, Token, Value, ValueId)
import Marlowe.Semantics as S
import Marlowe.Symbolic.Types.Response (Result(..))
import Network.RemoteData (RemoteData(..))
import Prelude (Unit, bind, discard, map, pure, unit, ($), (<<<), (+), (/=))
import Simulation.Types (Action, ChildSlots, ContractPathStep(..), ContractPath, Message(..), ReachabilityAnalysisData(..), State)
import WebSocket (WebSocketRequestMessage(..))

data ContractZipper
  = PayZip AccountId Payee Token Value ContractZipper
  | IfTrueZip Observation ContractZipper Contract
  | IfFalseZip Observation Contract ContractZipper
  | WhenCaseZip (List Case) S.Action ContractZipper (List Case) Timeout Contract -- First list is stored reversed for efficiency
  | WhenTimeoutZip (Array Case) Timeout ContractZipper
  | LetZip ValueId Value ContractZipper
  | AssertZip Observation ContractZipper
  | HeadZip

emptyContractPath :: ContractPath
emptyContractPath = Nil

splitArray :: forall a. List a -> List (List a /\ a /\ List a)
splitArray x = splitArrayAux Nil x

splitArrayAux :: forall a. List a -> List a -> List (List a /\ a /\ List a)
splitArrayAux _ Nil = Nil

splitArrayAux l (Cons h t) = Cons (l /\ h /\ t) (splitArrayAux (Cons h l) t)

foldBreadthContractWithZipperAuxStep :: ContractZipper /\ Contract -> List (ContractZipper /\ Contract)
foldBreadthContractWithZipperAuxStep (_ /\ Close) = Nil

foldBreadthContractWithZipperAuxStep (zipper /\ Pay accId payee tok val cont) = Cons (PayZip accId payee tok val zipper /\ cont) Nil

foldBreadthContractWithZipperAuxStep (zipper /\ If obs cont1 cont2) = Cons (IfTrueZip obs zipper cont2 /\ cont1) (Cons (IfFalseZip obs cont1 zipper /\ cont2) Nil)

foldBreadthContractWithZipperAuxStep (zipper /\ When cases tim tcont) =
  snoc
    ( map (\(before /\ Case act cont /\ after) -> WhenCaseZip before act zipper after tim tcont /\ cont)
        (splitArray (fromFoldable cases))
    )
    (WhenTimeoutZip cases tim zipper /\ tcont)

foldBreadthContractWithZipperAuxStep (zipper /\ Let valId val cont) = Cons (LetZip valId val zipper /\ cont) Nil

foldBreadthContractWithZipperAuxStep (zipper /\ Assert obs cont) = Cons (AssertZip obs zipper /\ cont) Nil

foldBreadthContractWithZipperAux :: forall b. (b -> ContractZipper -> Contract -> b) -> b -> List (ContractZipper /\ Contract) -> b
foldBreadthContractWithZipperAux f acc Nil = acc

foldBreadthContractWithZipperAux f acc list = foldBreadthContractWithZipperAux f newAcc thisLevel
  where
  thisLevel = concatMap foldBreadthContractWithZipperAuxStep list

  newAcc = foldl (\b (cz /\ c) -> f b cz c) acc thisLevel

foldBreadthContractWithZipper :: forall b. (b -> ContractZipper -> Contract -> b) -> b -> Contract -> b
foldBreadthContractWithZipper f acc c = foldBreadthContractWithZipperAux f acc (Cons (HeadZip /\ c) Nil)

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

checkContractForReachability :: forall m. String -> String -> HalogenM State Action ChildSlots Message m Unit
checkContractForReachability contract state = H.raise (WebsocketMessage msgString)
  where
  msgString = unsafeStringify <<< encode $ CheckForWarnings (encodeJSON true) contract state

expandSubproblem :: ContractZipper -> (ContractPath /\ Contract)
expandSubproblem z = zipperToContractPath z /\ closeZipperContract z (Assert FalseObs Close)

generateSubproblem :: List (Unit -> ContractPath /\ Contract) -> ContractZipper -> Contract -> List (Unit -> ContractPath /\ Contract)
generateSubproblem acc (z@(IfTrueZip _ _ _)) c
  | c /= Close = (Cons (\_ -> expandSubproblem z) acc)

generateSubproblem acc (z@(IfFalseZip _ _ _)) c
  | c /= Close = (Cons (\_ -> expandSubproblem z) acc)

generateSubproblem acc (z@(WhenCaseZip _ _ _ _ _ _)) c
  | c /= Close = (Cons (\_ -> expandSubproblem z) acc)

generateSubproblem acc _ _ = acc

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

generateSubproblems :: Contract -> List (Unit -> ContractPath /\ Contract)
generateSubproblems contract = reverse (foldBreadthContractWithZipper generateSubproblem Nil (nullifyAsserts contract))

startReachabilityAnalysis :: forall m. Contract -> S.State -> HalogenM State Action ChildSlots Message m ReachabilityAnalysisData
startReachabilityAnalysis contract state = do
  case subproblemList of
    Cons head tail -> do
      let
        path /\ subcontract = head unit
      checkContractForReachability (encodeJSON subcontract) (encodeJSON state)
      pure
        ( InProgress
            { currPath: path
            , currContract: subcontract
            , originalState: state
            , subproblems: tail
            , numSubproblems: 1 + length tail
            , numSolvedSubproblems: 0
            }
        )
    Nil -> pure AllReachable
  where
  subproblemList = generateSubproblems contract

updateWithResponse :: forall m. ReachabilityAnalysisData -> RemoteData String Result -> HalogenM State Action ChildSlots Message m ReachabilityAnalysisData
updateWithResponse (InProgress _) (Failure err) = pure (ReachabilityFailure err)

updateWithResponse (InProgress { currPath: path }) (Success (Error err)) = pure (ReachabilityFailure err)

updateWithResponse (InProgress { currPath: path }) (Success Valid) = pure (UnreachableSubcontract path)

updateWithResponse (InProgress { subproblems: Nil }) (Success (CounterExample _)) = pure AllReachable

updateWithResponse ( InProgress
    ( rad@{ originalState: state
    , subproblems: (Cons head tail)
    , numSolvedSubproblems: n
    }
  )
) (Success (CounterExample _)) = do
  let
    path /\ subcontract = head unit
  checkContractForReachability (encodeJSON subcontract) (encodeJSON state)
  pure
    ( InProgress
        ( rad
            { currPath = path
            , currContract = subcontract
            , subproblems = tail
            , numSolvedSubproblems = n + 1
            }
        )
    )

updateWithResponse rad _ = pure rad
 -- ToDo: nullify assertions