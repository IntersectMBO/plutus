{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE InstanceSigs       #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}

module Spec.DynamicLogic.RegistryModel where

import           Control.Concurrent
import           Control.Exception            (ErrorCall, try)
import           Data.List
import           Test.QuickCheck
import           Test.QuickCheck.Monadic
import           Test.Tasty                   hiding (after)
import           Test.Tasty.QuickCheck        (testProperty)

import           Spec.DynamicLogic.Registry
import           Test.QuickCheck.DynamicLogic
import           Test.QuickCheck.StateModel


data RegState = RegState{
    tids :: [Var ThreadId],
    regs :: [(String,Var ThreadId)],
    dead :: [Var ThreadId]
  }
  deriving Show

deriving instance Show (Action RegState a)
deriving instance Eq (Action RegState a)

instance StateModel RegState where
  data Action RegState a where
    Spawn      ::                           Action RegState ThreadId
    WhereIs    :: String                 -> Action RegState (Maybe ThreadId)
    Register   :: String -> Var ThreadId -> Action RegState (Either ErrorCall ())
    Unregister :: String                 -> Action RegState (Either ErrorCall ())
    KillThread :: Var ThreadId           -> Action RegState ()
    -- not generated
    Successful :: Action RegState a      -> Action RegState a

  type ActionMonad RegState = IO

  arbitraryAction s =
    frequency
          [(max 1 $ 10-length (tids s),return $ Some Spawn),
           (max 1 $ 10-length (regs s),Some <$> (Register
             <$> probablyUnregistered s
             <*> elements (tids s))),
           (2*length (regs s),Some <$> (Unregister
             <$> probablyRegistered s)),
           (10,Some <$> (WhereIs
             <$> probablyRegistered s)),
           (max 1 $ 3-length (dead s),Some <$> (KillThread <$> elements (tids s)))
          ]

  shrinkAction s (Register name tid) =
    [Some (Unregister name)] ++
    [Some (Register name' tid) | name' <- shrinkName name] ++
    [Some (Register name tid') | tid'  <- shrinkTid s tid]
  shrinkAction _ (Unregister name) =
    [Some (WhereIs name)] ++ [Some (Unregister name') | name' <- shrinkName name]
  shrinkAction _ (WhereIs name) =
    [Some (WhereIs name') | name' <- shrinkName name]
  shrinkAction _ Spawn = []
  shrinkAction s (KillThread tid) =
    [Some (KillThread tid') | tid' <- shrinkTid s tid]
  shrinkAction s (Successful act) =
    Some act : [Some (Successful act') | Some act' <- shrinkAction s act]


  initialState :: RegState
  initialState = RegState [] [] []

  nextState s Spawn step =
    s{tids = step:tids s}
  nextState s (Register name tid) _step
    | positive s (Register name tid) =
        s{regs = (name,tid):regs s}
    | otherwise = s
  nextState s (Unregister name) _step =
    s{regs = filter ((/=name) . fst) (regs s)}
  nextState s (KillThread tid) _ =
    s{dead = tid:dead s, regs = filter ((/=tid) . snd) (regs s)}
  nextState s (Successful act) step = nextState s act step
  nextState s _  _ = s

  precondition s (Register _name step) = step `elem` tids s -- && positive s (Register name step)
  precondition s (KillThread tid)      = tid `elem` tids s
  precondition s (Successful act)      = precondition s act
  precondition _ _                     = True

  postcondition  s (WhereIs name)      env mtid =
    (env <$> lookup name (regs s)) == mtid
  postcondition _s Spawn                _         _   = True
  postcondition  s (Register name step) _         res =
    positive s (Register name step) == (res == Right ())
  postcondition _s (Unregister _name)   _         _   = True
  postcondition _s (KillThread _) _ _ = True
  postcondition _s (Successful (Register _ _)) _ res = res==Right ()
  postcondition s (Successful act) env res = postcondition s act env res

  monitoring (_s, s') act _ res =
    counterexample ("\nState: "++show s'++"\n") .
    tabulate "Registry size" [show $ length (regs s')] .
    case act of
      Register _ _ -> tabu "Register" [case res of Left _  -> "fails "++why _s act
                                                   Right() -> "succeeds"]
      Unregister _ -> tabu "Unregister" [case res of Left _ -> "fails"; Right() -> "succeeds"]
      WhereIs _    -> tabu "WhereIs" [case res of Nothing -> "fails"; Just _ -> "succeeds"]
      _            -> id

  perform _ Spawn _
    = forkIO (threadDelay 10000000)
  perform _ (Register name tid) env
    = try $ register name (env tid)
  perform _ (Unregister name) _
    = try $ unregister name
  perform _ (WhereIs name) _
    = whereis name
  perform _ (KillThread tid) env
    = do killThread (env tid)
         threadDelay 1000
  perform s (Successful act) env =
    perform s act env

positive :: RegState -> Action RegState a -> Bool
positive s (Register name tid) =
     name `notElem` map fst (regs s)
  && tid  `notElem` map snd (regs s)
  && tid  `notElem` dead s
positive s (Unregister name) =
     name `elem` map fst (regs s)
positive _s _ = True

instance DynLogicModel RegState where
  restricted (Successful _) = True
  restricted _              = False

why :: RegState -> Action RegState a -> String
why s (Register name tid) =
  unwords $ ["name already registered" | name `elem` map fst (regs s)] ++
            ["tid already registered"  | tid  `elem` map snd (regs s)] ++
            ["dead thread"             | tid  `elem` dead s]
why _ _ = "(impossible)"

arbitraryName :: Gen String
arbitraryName = elements allNames

probablyRegistered :: RegState -> Gen String
probablyRegistered s = oneof $ map (return . fst) (regs s) ++ [arbitraryName]

probablyUnregistered :: RegState -> Gen String
probablyUnregistered s = elements $ allNames ++ (allNames \\ map fst (regs s))

shrinkName :: String -> [String]
shrinkName name = [n | n <- allNames, n < name]

allNames :: [String]
allNames = ["a", "b", "c", "d", "e"]

shrinkTid :: RegState -> Var ThreadId -> [Var ThreadId]
shrinkTid s tid = [ tid' | tid' <- tids s, tid' < tid ]

tabu :: String -> [String] -> Property -> Property
tabu tab xs = tabulate tab xs . foldr (.) id [classify True (tab++": "++x) | x <- xs]

prop_Registry :: Actions RegState -> Property
prop_Registry s = monadicIO $ do
  _ <- run cleanUp
  monitor $ counterexample "\nExecution\n"
  _ <- runActions s
  assert True

cleanUp :: IO [Either ErrorCall ()]
cleanUp = sequence
  [try (unregister name) :: IO (Either ErrorCall ())
   | name <- allNames++["x"]]

propTest :: DynLogic RegState -> Property
propTest d = forAllScripts d prop_Registry

-- Generate normal test cases

normalTests :: DynPred s
normalTests _ = passTest ||| afterAny normalTests

loopingTests :: DynPred s
loopingTests _ = afterAny loopingTests

canSpawn :: RegState -> DynLogic RegState
canSpawn _ = after Spawn done

canRegisterA :: DynPred RegState
canRegisterA s
  | null (tids s) = after Spawn canRegisterA
  | otherwise     = after (Successful $ Register "a" (head (tids s))) done

-- test that the registry never contains more than k processes

regLimit :: Int -> DynPred RegState
regLimit k s | length (regs s) > k = ignore   -- fail? yes, gets stuck at this point
             | otherwise           = passTest ||| afterAny (regLimit k)

-- test that we can register a pid that is not dead, if we unregister the name first.

canRegisterUndead :: RegState -> DynLogic RegState
canRegisterUndead s
  | null aliveTs = ignore
  | otherwise    = after (Successful (Register "x" (head aliveTs))) done
  where aliveTs = tids s \\ dead s

canRegister :: DynPred RegState
canRegister s
  | length (regs s) == 5 = ignore  -- all names are in use
  | null (tids s) = after Spawn canRegister
  | otherwise     = forAllQ (elementsQ (allNames \\ map fst (regs s)),
                             elementsQ (tids s)) $ \(name,tid) ->
                      after (Successful $ Register name tid)
                      done

canRegisterName :: String -> RegState -> DynLogic RegState
canRegisterName name s = forAllQ (elementsQ availableTids) $ \tid ->
                           after (Successful $ Register name tid) done
  where availableTids = tids s \\ map snd (regs s)

canReregister :: RegState -> DynLogic RegState
canReregister s
  | null (regs s) = ignore
  | otherwise     = forAllQ (elementsQ $ map fst (regs s)) $ \name ->
                      after (Unregister name) (canRegisterName name)

canRegisterName' :: String -> RegState -> DynLogic RegState
canRegisterName' name s = forAllQ (elementsQ availableTids) $ \tid ->
                            after (Successful $ Register name tid) done
  where availableTids = (tids s \\ map snd (regs s)) \\ dead s

canReregister' :: DynPred RegState
canReregister' s
  | null (regs s) = toStop $
                      if null availableTids then after Spawn canReregister'
                      else after (Register "a" (head availableTids)) canReregister'
  | otherwise     = forAllQ (elementsQ $ map fst (regs s)) $ \name ->
                      after (Unregister name) (canRegisterName' name)
  where availableTids = (tids s \\ map snd (regs s)) \\ dead s

tests :: TestTree
tests = testGroup "registry model example"
          [ testProperty "prop_Registry" prop_Registry ]

