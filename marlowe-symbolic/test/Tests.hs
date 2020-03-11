{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}

module Tests (runTests) where

import           Control.Exception                     (SomeException, catch)
import           Data.Maybe                            (isJust)
import           Language.Marlowe
import           Language.Marlowe.Analysis.FSSemantics
import           Language.Marlowe.Semantics
import           Ledger                                (pubKeyHash)
import qualified OldAnalysis.FSSemantics               as OldAnalysis
import           System.IO.Unsafe                      (unsafePerformIO)
import           Test.QuickCheck

partyGen :: Gen Party
partyGen = oneof [ return $ Role "alice"
                 , return $ Role "bob"
                 , return $ PK (pubKeyHash "6361726f6c")
                 ]

shrinkParty :: Party -> [Party]
shrinkParty (PK _)         = [Role "alice", Role "bob"]
shrinkParty (Role "bob")   = [Role "alice"]
shrinkParty (Role "alice") = []
shrinkParty _              = []

accountIdGen :: Gen AccountId
accountIdGen = do accName <- oneof [ return 0
                                   , return 1
                                   ]
                  owner <- partyGen
                  return $ AccountId accName owner

shrinkAccountId :: AccountId -> [AccountId]
shrinkAccountId (AccountId 1 owner) = AccountId 0 owner
                                      :[AccountId 1 x | x <- shrinkParty owner]
shrinkAccountId (AccountId 0 owner) = [AccountId 0 x | x <- shrinkParty owner]
shrinkAccountId _ = []

payeeGen :: Gen Payee
payeeGen = oneof [ Account <$> accountIdGen
                 , Party <$> partyGen
                 ]

shrinkPayee :: Payee -> [Payee]
shrinkPayee (Account accId) = [Account x | x <- shrinkAccountId accId]
shrinkPayee (Party party)   = [Party x | x <- shrinkParty party]

tokenGen :: Gen Token
tokenGen = oneof [ return $ Token "" ""
                 , return $ Token "424954" "434f494e"
                 ]

shrinkToken :: Token -> [Token]
shrinkToken (Token "" "") = []
shrinkToken (Token _ _)   = [Token "" ""]

simpleIntegerGen :: Gen Integer
simpleIntegerGen = frequency [ (1, return (-100))
                             , (1, return (-1))
                             , (2, return 0)
                             , (64, return 1)
                             , (32, return 2)
                             , (16, return 4)
                             , (8, return 8)
                             , (4, return 16)
                             , (2, return 32)
                             ]

shrinkSimpleInteger :: Integer -> [Integer]
shrinkSimpleInteger 0 = []
shrinkSimpleInteger v = [0, v `quot` 2]

choiceIdGen :: Gen ChoiceId
choiceIdGen = do choName <- oneof [ return "first"
                                  , return "second"
                                  ]
                 chooser <- partyGen
                 return $ ChoiceId choName chooser

shrinkChoiceId :: ChoiceId -> [ChoiceId]
shrinkChoiceId (ChoiceId "second" chooser) = ChoiceId "first" chooser
                                            :[ChoiceId "second" x | x <- shrinkParty chooser]
shrinkChoiceId (ChoiceId "first" chooser) = [ChoiceId "first" x | x <- shrinkParty chooser]
shrinkChoiceId _ = []

valueIdGen :: Gen ValueId
valueIdGen = oneof [ return "alpha"
                   , return "beta"
                   ]

shrinkValueId :: ValueId -> [ValueId]
shrinkValueId "beta"  = ["alpha"]
shrinkValueId "alpha" = []
shrinkValueId _       = []

valueGenSized :: Int -> Gen Value
valueGenSized s
  | s > 0 = oneof [ AvailableMoney <$> accountIdGen <*> tokenGen
                  , Constant <$> simpleIntegerGen
                  , NegValue <$> valueGenSized (s - 1)
                  , AddValue <$> valueGenSized (s `quot` 2) <*> valueGenSized (s `quot` 2)
                  , SubValue <$> valueGenSized (s `quot` 2) <*> valueGenSized (s `quot` 2)
                  , ChoiceValue <$> choiceIdGen <*> valueGenSized (s - 1)
                  , return SlotIntervalStart
                  , return SlotIntervalEnd
                  , UseValue <$> valueIdGen
                  ]
  | otherwise = oneof [ AvailableMoney <$> accountIdGen <*> tokenGen
                      , Constant <$> simpleIntegerGen
                      , return SlotIntervalStart
                      , return SlotIntervalEnd
                      , UseValue <$> valueIdGen
                      ]

shrinkValue :: Value -> [Value]
shrinkValue (Constant x) = [Constant y | y <- shrinkSimpleInteger x]
shrinkValue SlotIntervalStart = [Constant 0]
shrinkValue SlotIntervalEnd = [Constant 0, SlotIntervalStart]
shrinkValue (AvailableMoney accId tok) =
  Constant 0:([AvailableMoney x tok | x <- shrinkAccountId accId]
               ++ [AvailableMoney accId y | y <- shrinkToken tok])
shrinkValue (UseValue valId) = Constant 0:[UseValue x | x <- shrinkValueId valId]
shrinkValue (ChoiceValue choId val) =
  Constant 0:val:([ChoiceValue x val | x <- shrinkChoiceId choId]
                   ++ [ChoiceValue choId y | y <- shrinkValue val])
shrinkValue (NegValue val) = Constant 0:val:[NegValue x | x <- shrinkValue val]
shrinkValue (AddValue val1 val2) =
  Constant 0:val1:val2:([AddValue x val2 | x <- shrinkValue val1]
                         ++ [AddValue val1 y | y <- shrinkValue val2])
shrinkValue (SubValue val1 val2) =
  Constant 0:val1:val2:([SubValue x val2 | x <- shrinkValue val1]
                         ++ [SubValue val1 y | y <- shrinkValue val2])

observationGenSized :: Int -> Gen Observation
observationGenSized s
  | s > 0 = oneof [ AndObs <$> observationGenSized (s `quot` 2)
                           <*> observationGenSized (s `quot` 2)
                  , OrObs <$> observationGenSized (s `quot` 2)
                          <*> observationGenSized (s `quot` 2)
                  , NotObs <$> observationGenSized (s - 1)
                  , ChoseSomething <$> choiceIdGen
                  , ValueGE <$> valueGenSized (s `quot` 2)
                            <*> valueGenSized (s `quot` 2)
                  , ValueGT <$> valueGenSized (s `quot` 2)
                            <*> valueGenSized (s `quot` 2)
                  , ValueLT <$> valueGenSized (s `quot` 2)
                            <*> valueGenSized (s `quot` 2)
                  , ValueLE <$> valueGenSized (s `quot` 2)
                            <*> valueGenSized (s `quot` 2)
                  , ValueEQ <$> valueGenSized (s `quot` 2)
                            <*> valueGenSized (s `quot` 2)
                  , return TrueObs
                  , return FalseObs
                  ]
  | otherwise = oneof [ ChoseSomething <$> choiceIdGen
                      , return TrueObs
                      , return FalseObs
                      ]

shrinkObservation :: Observation -> [Observation]
shrinkObservation FalseObs = []
shrinkObservation TrueObs = [FalseObs]
shrinkObservation (ChoseSomething choId) =
  FalseObs:TrueObs:[ChoseSomething x | x <- shrinkChoiceId choId]
shrinkObservation (ValueGE lhs rhs) =
  FalseObs:TrueObs:([ValueGE x rhs | x <- shrinkValue lhs]
                     ++ [ValueGE lhs y | y <- shrinkValue rhs])
shrinkObservation (ValueGT lhs rhs) =
  FalseObs:TrueObs:([ValueGT x rhs | x <- shrinkValue lhs]
                     ++ [ValueGT lhs y | y <- shrinkValue rhs])
shrinkObservation (ValueLT lhs rhs) =
  FalseObs:TrueObs:([ValueLT x rhs | x <- shrinkValue lhs]
                     ++ [ValueLT lhs y | y <- shrinkValue rhs])
shrinkObservation (ValueLE lhs rhs) =
  FalseObs:TrueObs:([ValueLE x rhs | x <- shrinkValue lhs]
                     ++ [ValueLE lhs y | y <- shrinkValue rhs])
shrinkObservation (ValueEQ lhs rhs) =
  FalseObs:TrueObs:([ValueEQ x rhs | x <- shrinkValue lhs]
                     ++ [ValueEQ lhs y | y <- shrinkValue rhs])
shrinkObservation (AndObs lhs rhs) =
  FalseObs:TrueObs:lhs:rhs:([AndObs x rhs | x <- shrinkObservation lhs]
                             ++ [AndObs lhs y | y <- shrinkObservation rhs])
shrinkObservation (OrObs lhs rhs) =
  FalseObs:TrueObs:lhs:rhs:([OrObs x rhs | x <- shrinkObservation lhs]
                             ++ [OrObs lhs y | y <- shrinkObservation rhs])
shrinkObservation (NotObs subObs) =
  FalseObs:TrueObs:subObs:[NotObs x | x <- shrinkObservation subObs]

boundListGenAux :: Int -> Integer -> Gen [Bound]
boundListGenAux s lb
  | s > 0 = do inc1 <- simpleIntegerGen
               inc2 <- simpleIntegerGen
               let tlb = lb + inc1
                   thb = tlb + inc2
               rest <- boundListGenAux (s - 1) thb
               return (Bound tlb thb:rest)
  | otherwise = return []

listLengthGen :: Gen Int
listLengthGen = frequency [ (1, return 0)
                          , (8, return 1)
                          , (4, return 2)
                          , (1, return 3)
                          ]

boundListGen :: Gen [Bound]
boundListGen = do len <- listLengthGen
                  firstBound <- simpleIntegerGen
                  boundListGenAux len firstBound

actionGenSized :: Int -> Gen Action
actionGenSized s =
  oneof [ Deposit <$> accountIdGen <*> partyGen <*> tokenGen <*> valueGenSized (s - 1)
        , Choice <$> choiceIdGen <*> boundListGen
        , Notify <$> observationGenSized (s - 1)
        ]

shrinkAction :: Action -> [Action]
shrinkAction (Deposit accId party tok val) =
  Notify FalseObs
  : [Deposit accId party tok v | v <- shrinkValue val]
  ++ [Deposit x party tok val | x <- shrinkAccountId accId]
  ++ [Deposit accId y tok val | y <- shrinkParty party]
  ++ [Deposit accId party z val | z <- shrinkToken tok]
shrinkAction (Choice choId boundList) =
  Notify FalseObs
  : [Choice choId b | b <- shrinkList (const []) boundList]
  ++ [Choice x boundList | x <- shrinkChoiceId choId]
shrinkAction (Notify obs) =
  [Notify x | x <- shrinkObservation obs]

caseRelGenSized :: Int -> Integer -> Gen (Case Contract)
caseRelGenSized s bn = Case <$> actionGenSized s <*> contractRelGenSized s bn

shrinkCase :: Case Contract -> [Case Contract]
shrinkCase (Case act cont) = [Case act x | x <- shrinkContract cont]
                              ++ [Case y cont | y <- shrinkAction act]

contractRelGenSized :: Int -> Integer -> Gen Contract
contractRelGenSized s bn
  | s > 0 = oneof [ return Close
                  , Pay <$> accountIdGen <*> payeeGen <*> tokenGen
                        <*> valueGenSized (s `quot` 4)
                        <*> contractRelGenSized (s - 1) bn
                  , If <$> observationGenSized (s `quot` 4)
                       <*> contractRelGenSized (s `quot` 3) bn
                       <*> contractRelGenSized (s `quot` 3) bn
                  , do timeOutDelta <- simpleIntegerGen
                       numCases <- listLengthGen
                       let newTimeout = bn + timeOutDelta
                           ns = if numCases > 0 then s `quot` numCases else s - 1
                       When <$> vectorOf numCases (caseRelGenSized ns bn)
                            <*> (return $ Slot newTimeout)
                            <*> contractRelGenSized ns newTimeout
                  ]
  | otherwise = return Close

contractGenSized :: Int -> Gen Contract
contractGenSized s = do iniBn <- simpleIntegerGen
                        contractRelGenSized s iniBn

contractGen :: Gen Contract
contractGen = sized contractGenSized

shrinkContract :: Contract -> [Contract]
shrinkContract Close = []
shrinkContract (Pay accId payee tok val cont) =
  Close:cont:([Pay accId payee tok val c | c <- shrinkContract cont]
              ++ [Pay accId payee tok v cont | v <- shrinkValue val]
              ++ [Pay x payee tok val cont | x <- shrinkAccountId accId]
              ++ [Pay accId y tok val cont | y <- shrinkPayee payee]
              ++ [Pay accId payee z val cont | z <- shrinkToken tok])
shrinkContract (If obs cont1 cont2) =
  Close:cont1:cont2:([If obs x cont2 | x <- shrinkContract cont1]
                      ++ [If obs cont1 y | y <- shrinkContract cont2]
                      ++ [If z cont1 cont2 | z <- shrinkObservation obs])
shrinkContract (When [] (Slot tim) cont) =
  Close:cont:([When [] (Slot tim) x | x <- shrinkContract cont]
              ++ [When [] (Slot y) cont | y <- shrinkSimpleInteger tim])
shrinkContract (When l (Slot tim) cont) =
  Close:cont:([When nl (Slot tim) cont | nl <- shrinkList shrinkCase l]
              ++ [When l (Slot tim) x | x <- shrinkContract cont]
              ++ [When l (Slot y) cont | y <- shrinkSimpleInteger tim])

noFalsePositivesForContract :: Contract -> Property
noFalsePositivesForContract cont =
  unsafePerformIO (do res <- catch (wrapLeft $ warningsTrace cont)
                                   (\exc -> return $ Left (Left (exc :: SomeException)))
                      return (case res of
                                Left err -> counterexample (show err) False
                                Right answer ->
                                   tabulate "Has counterexample" [show (isJust answer)]
                                   (case answer of
                                      Nothing ->
                                         tabulate "Is empty contract" [show (cont == Close)]
                                                  True
                                      Just (is, li, warns) ->
                                         counterexample ("Trace: " ++ show (is, li)) $
                                         tabulate "Number of warnings" [show (length warns)]
                                                  (warns =/= []))))

wrapLeft :: IO (Either a b) -> IO (Either (Either c a) b)
wrapLeft r = do tempRes <- r
                return (case tempRes of
                          Left x  -> Left (Right x)
                          Right y -> Right y)


prop_noFalsePositives :: Property
prop_noFalsePositives = forAllShrink contractGen shrinkContract noFalsePositivesForContract

sameAsOldImplementation :: Contract -> Property
sameAsOldImplementation cont =
  unsafePerformIO (do res <- catch (wrapLeft $ warningsTrace cont)
                                   (\exc -> return $ Left (Left (exc :: SomeException)))
                      res2 <- catch (wrapLeft $ OldAnalysis.warningsTrace cont)
                                    (\exc -> return $ Left (Left (exc :: SomeException)))
                      return (case (res, res2) of
                                 (Right Nothing, Right Nothing) ->
                                    label "No counterexample" True
                                 (Right (Just _), Right Nothing) ->
                                    label "Old version couldn't see counterexample" True
                                 (Right (Just _), Right (Just _)) ->
                                    label "Both versions found counterexample" True
                                 (Left _, Left _) ->
                                    label "Both solvers failed" True
                                 (Left _, _) ->
                                    label "Solver for new version failed" True
                                 (_, Left _) ->
                                    label "Solver for old version failed" True
                                 problems -> counterexample (show problems) False))

runManuallySameAsOldImplementation :: Property
runManuallySameAsOldImplementation =
  forAllShrink contractGen shrinkContract sameAsOldImplementation

------------------
return []

runTests :: IO Bool
runTests = $forAllProperties (quickCheckWithResult (stdArgs {maxSuccess = 100}))


