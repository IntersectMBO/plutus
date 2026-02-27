{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Common where

import Data.ByteString.Lazy qualified as BSL
import Data.Csv qualified as CSV
import Data.Foldable (toList)
import Data.List (intercalate)
import Data.Text qualified as T
import Data.Vector qualified as V

data StackFrame
  = MkStackFrame
  { varName :: T.Text
  -- ^ The variable name.
  , startVal :: Integer
  -- ^ The resource value when it starts to be evaluated.
  , valSpentCalledFun :: Integer
  -- ^ The resource spent on evaluating the functions it called.
  }
  deriving stock (Show)

data ProfileEvent
  = MkProfileEvent Integer Transition T.Text

data Transition
  = Enter
  | Exit

-- | Represent one of the "folded" flamegraph lines, which include fns it's in and resource spent.
data StackVal
  = MkStackVal [T.Text] Integer
  deriving stock (Eq)

instance Show StackVal where
  show (MkStackVal fns duration) =
    intercalate
      "; "
      -- reverse to make the functions in the order correct for flamegraphs.
      (reverse (map T.unpack fns))
      <> " "
      <> show duration

data LogRow = LogRow String [Integer]

instance CSV.FromRecord LogRow where
  parseRecord v | V.length v == 0 = fail "empty"
  parseRecord v =
    LogRow
      <$> CSV.parseField (V.unsafeHead v)
      <*> traverse CSV.parseField (V.toList $ V.unsafeTail v)

processLog :: Int -> BSL.ByteString -> [StackVal]
processLog valIx content =
  let lEvents = case CSV.decode CSV.NoHeader content of
        Left e -> error e
        Right es -> es
   in getStacks (map (parseProfileEvent valIx) $ toList lEvents)

parseProfileEvent :: Int -> LogRow -> ProfileEvent
parseProfileEvent valIx (LogRow str vals) =
  let val = vals !! (valIx - 1)
   in case words str of
        [transition, var] ->
          -- See Note [Profiling Marker]
          case transition of
            "->" -> MkProfileEvent val Enter (T.pack var)
            "<-" -> MkProfileEvent val Exit (T.pack var)
            badLog ->
              error $
                "parseProfileEvent: expecting \"entering\" or \"exiting\" but got "
                  <> show badLog
        invalid ->
          error $
            "parseProfileEvent: invalid log, expecting a form of [t1,t2,t3,transition,var] but got "
              <> show invalid

getStacks :: [ProfileEvent] -> [StackVal]
getStacks = go []
  where
    go
      :: [StackFrame]
      -> [ProfileEvent]
      -> [StackVal]
    go curStack ((MkProfileEvent startVal Enter varName) : tl) =
      go
        (MkStackFrame {varName, startVal, valSpentCalledFun = 0} : curStack)
        tl
    go
      (MkStackFrame {varName = curTopVar, startVal, valSpentCalledFun} : poppedStack)
      ((MkProfileEvent exitVal Exit var) : tl)
        | curTopVar == var =
            let diffVal = exitVal - startVal
                updateValSpent (hd@MkStackFrame {valSpentCalledFun} : tl) =
                  hd {valSpentCalledFun = valSpentCalledFun + diffVal} : tl
                updateValSpent [] = []
                updatedStack = updateValSpent poppedStack
                -- this is quadratic but it's fine because we have to do quadratic
                -- work anyway for fg and the input sizes are small.
                fnsEntered = map varName updatedStack
             in -- resource spent on this function is the total resource spent
                -- minus the resource spent on the function(s) it called.
                MkStackVal (var : fnsEntered) (diffVal - valSpentCalledFun) : go updatedStack tl
    go _ ((MkProfileEvent _ Exit _) : _) =
      error "getStacks; go: tried to exit but couldn't."
    go [] [] = []
    go stacks [] =
      error $
        "getStacks; go: stack " <> show stacks <> " isn't empty but the log is."
