
\subsection{Cardano.BM.Data.Aggregated}
\label{code:Cardano.BM.Data.Aggregated}

%if style == newcode
\begin{code}
{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE StandaloneDeriving #-}

module Cardano.BM.Data.Aggregated
  ( Aggregated (..)
  , Stats (..)
  , BaseStats (..)
  , EWMA (..)
  , Measurable (..)
  , showSI
  , showUnits
  , getInteger
  , getDouble
  , subtractMeasurable
  , meanOfStats
  , stdevOfStats
  , stats2Text
  , singletonStats
  , updateAggregation
  , ewma
  ) where

import           GHC.Generics (Generic)
import           Data.Aeson (FromJSON, ToJSON)
import           Data.Scientific (fromFloatDigits)
import           Data.Text (Text, pack)
import           Data.Word (Word64)

import qualified Cardano.BM.Data.Severity as S

\end{code}
%endif

\subsubsection{Measurable}\label{code:Measurable}\index{Measurable}
A |Measurable| may consist of different types of values.
Time measurements are strict, so are |Bytes| which are externally measured.
The real or integral numeric values are lazily linked, so we can decide later
to drop them.
\begin{code}
data Measurable = Microseconds {-# UNPACK #-} !Word64
                | Nanoseconds  {-# UNPACK #-} !Word64
                | Seconds      {-# UNPACK #-} !Word64
                | Bytes        {-# UNPACK #-} !Word64
                | PureD        !Double
                | PureI        !Integer
                | Severity     S.Severity
                deriving (Eq, Read, Generic, ToJSON, FromJSON)

\end{code}

|Measurable| can be transformed to an integral value.
\begin{code}
instance Ord Measurable where
    compare (Seconds a) (Seconds b)              = compare a b
    compare (Microseconds a) (Microseconds b)    = compare a b
    compare (Nanoseconds a) (Nanoseconds b)      = compare a b
    compare (Seconds a) (Microseconds b)         = compare (a * 1000 * 1000) b
    compare (Nanoseconds a) (Microseconds b)     = compare a (b * 1000)
    compare (Seconds a) (Nanoseconds b)          = compare (a * 1000 * 1000 * 1000) b
    compare (Microseconds a) (Nanoseconds b)     = compare (a * 1000) b
    compare (Microseconds a) (Seconds b)         = compare a (b * 1000 * 1000)
    compare (Nanoseconds a) (Seconds b)          = compare a (b * 1000 * 1000 * 1000)
    compare (Bytes a) (Bytes b)                  = compare a b
    compare (PureD a) (PureD b)                  = compare a b
    compare (PureI a) (PureI b)                  = compare a b
    compare (Severity a) (Severity b)            = compare a b
    compare (PureI a) (Seconds b)       | a >= 0 = compare a (toInteger b)
    compare (PureI a) (Microseconds b)  | a >= 0 = compare a (toInteger b)
    compare (PureI a) (Nanoseconds b)   | a >= 0 = compare a (toInteger b)
    compare (PureI a) (Bytes b)         | a >= 0 = compare a (toInteger b)
    compare (Seconds a)      (PureI b)  | b >= 0 = compare (toInteger a) b
    compare (Microseconds a) (PureI b)  | b >= 0 = compare (toInteger a) b
    compare (Nanoseconds a)  (PureI b)  | b >= 0 = compare (toInteger a) b
    compare (Bytes a)        (PureI b)  | b >= 0 = compare (toInteger a) b
    compare a@(PureD _) (PureI b)                = compare (getInteger a) b
    compare (PureI a) b@(PureD _)                = compare a (getInteger b)
    compare _a  _b                               = LT

\end{code}

|Measurable| can be transformed to an integral value.
\begin{code}
getInteger :: Measurable -> Integer
getInteger (Microseconds a) = toInteger a
getInteger (Nanoseconds a)  = toInteger a
getInteger (Seconds a)      = toInteger a
getInteger (Bytes a)        = toInteger a
getInteger (PureI a)        = a
getInteger (PureD a)        = round a
getInteger (Severity a)     = toInteger (fromEnum a)

\end{code}

|Measurable| can be transformed to a rational value.
\begin{code}
getDouble :: Measurable -> Double
getDouble (Microseconds a) = fromIntegral a
getDouble (Nanoseconds a)  = fromIntegral a
getDouble (Seconds a)      = fromIntegral a
getDouble (Bytes a)        = fromIntegral a
getDouble (PureI a)        = fromInteger a
getDouble (PureD a)        = a
getDouble (Severity a)     = fromIntegral (fromEnum a)

\end{code}

It is a numerical value, thus supports functions to operate on numbers.
\index{Measurable!instance of Num}
\begin{code}
instance Num Measurable where
    (+) (Microseconds a) (Microseconds b) = Microseconds (a+b)
    (+) (Nanoseconds a)  (Nanoseconds b)  = Nanoseconds  (a+b)
    (+) (Seconds a)      (Seconds b)      = Seconds      (a+b)
    (+) (Bytes a)        (Bytes b)        = Bytes        (a+b)
    (+) (PureI a)        (PureI b)        = PureI        (a+b)
    (+) (PureD a)        (PureD b)        = PureD        (a+b)
    (+) a                _                = a

    (*) (Microseconds a) (Microseconds b) = Microseconds (a*b)
    (*) (Nanoseconds a)  (Nanoseconds b)  = Nanoseconds  (a*b)
    (*) (Seconds a)      (Seconds b)      = Seconds      (a*b)
    (*) (Bytes a)        (Bytes b)        = Bytes        (a*b)
    (*) (PureI a)        (PureI b)        = PureI        (a*b)
    (*) (PureD a)        (PureD b)        = PureD        (a*b)
    (*) a                _                = a

    abs (Microseconds a) = Microseconds (abs a)
    abs (Nanoseconds a)  = Nanoseconds  (abs a)
    abs (Seconds a)      = Seconds      (abs a)
    abs (Bytes a)        = Bytes        (abs a)
    abs (PureI a)        = PureI        (abs a)
    abs (PureD a)        = PureD        (abs a)
    abs a                = a

    signum (Microseconds a) = Microseconds (signum a)
    signum (Nanoseconds a)  = Nanoseconds  (signum a)
    signum (Seconds a)      = Seconds      (signum a)
    signum (Bytes a)        = Bytes        (signum a)
    signum (PureI a)        = PureI        (signum a)
    signum (PureD a)        = PureD        (signum a)
    signum a                = a

    negate (Microseconds a) = Microseconds (negate a)
    negate (Nanoseconds a)  = Nanoseconds  (negate a)
    negate (Seconds a)      = Seconds      (negate a)
    negate (Bytes a)        = Bytes        (negate a)
    negate (PureI a)        = PureI        (negate a)
    negate (PureD a)        = PureD        (negate a)
    negate a                = a

    fromInteger = PureI

subtractMeasurable :: Measurable -> Measurable -> Measurable
subtractMeasurable (Microseconds a) (Microseconds b) = Microseconds (a-b)
subtractMeasurable (Nanoseconds a)  (Nanoseconds b)  = Nanoseconds  (a-b)
subtractMeasurable (Seconds a)      (Seconds b)      = Seconds      (a-b)
subtractMeasurable (Bytes a)        (Bytes b)        = Bytes        (a-b)
subtractMeasurable (PureI a)        (PureI b)        = PureI        (a-b)
subtractMeasurable (PureD a)        (PureD b)        = PureD        (a-b)
subtractMeasurable a                _                = a
\end{code}

Pretty printing of |Measurable|. \index{Measurable!instance of Show}
\begin{code}
instance Show Measurable where
    show v@(Microseconds a) = show a ++ showUnits v
    show v@(Nanoseconds a)  = show a ++ showUnits v
    show v@(Seconds a)      = show a ++ showUnits v
    show v@(Bytes a)        = show a ++ showUnits v
    show v@(PureI a)        = show a ++ showUnits v
    show v@(PureD a)        = show a ++ showUnits v
    show v@(Severity a)     = show a ++ showUnits v

showUnits :: Measurable -> String
showUnits (Microseconds _) = " µs"
showUnits (Nanoseconds _)  = " ns"
showUnits (Seconds _)      = " s"
showUnits (Bytes _)        = " B"
showUnits (PureI _)        = ""
showUnits (PureD _)        = ""
showUnits (Severity _)     = ""

-- show in S.I. units
showSI :: Measurable -> String
showSI (Microseconds a) = show (fromFloatDigits ((fromIntegral a) / (1000::Float) / (1000::Float))) ++
                          showUnits (Seconds a)
showSI (Nanoseconds a)  = show (fromFloatDigits ((fromIntegral a) / (1000::Float) / (1000::Float) / (1000::Float))) ++
                          showUnits (Seconds a)
showSI v@(Seconds a)    = show a ++ showUnits v
showSI v@(Bytes a)      = show a ++ showUnits v
showSI v@(PureI a)      = show a ++ showUnits v
showSI v@(PureD a)      = show a ++ showUnits v
showSI v@(Severity a)   = show a ++ showUnits v

\end{code}

\subsubsection{Stats}\label{code:Stats}\index{Stats}
A |Stats| statistics is strictly computed.
\begin{code}
data BaseStats = BaseStats {
    fmin   :: !Measurable,
    fmax   :: !Measurable,
    fcount :: {-# UNPACK #-} !Word64,
    fsum_A :: {-# UNPACK #-} !Double,
    fsum_B :: {-# UNPACK #-} !Double
    } deriving (Show, Generic, ToJSON, FromJSON)

instance Eq BaseStats where
    (BaseStats mina maxa counta sumAa sumBa) == (BaseStats minb maxb countb sumAb sumBb) =
        mina == minb && maxa == maxb && counta == countb &&
        abs (sumAa - sumAb) < 1.0e-4 &&
        abs (sumBa - sumBb) < 1.0e-4

data Stats = Stats {
    flast  :: !Measurable,
    fold   :: !Measurable,
    fbasic :: !BaseStats,
    fdelta :: !BaseStats,
    ftimed :: !BaseStats
    } deriving (Show, Eq, Generic, ToJSON, FromJSON)

\end{code}

\begin{code}
meanOfStats :: BaseStats -> Double
meanOfStats = fsum_A

\end{code}

\begin{code}
stdevOfStats :: BaseStats -> Double
stdevOfStats s =
    calculate (fcount s)
  where
    calculate :: Word64 -> Double
    calculate n =
        if n >= 2
        then sqrt $ (fsum_B s) / (fromInteger $ fromIntegral (n - 1))
        else 0

\end{code}

\index{Stats!instance of Semigroup}
\todo[inline]{|instance Semigroup Stats| disabled for the moment, because not needed.}
We use a parallel algorithm to update the estimation of mean and variance from two sample statistics.
(see \url{https://en.wikipedia.org/wiki/Algorithms_for_calculating_variance#Parallel_algorithm})

\begin{spec}
instance Semigroup Stats where
    (<>) a b = let counta = fcount a
                   countb = fcount b
                   newcount = counta + countb
                   delta = fsum_A b - fsum_A a
               in
               Stats { flast  = flast b  -- right associative
                     , fmin   = min (fmin a) (fmin b)
                     , fmax   = max (fmax a) (fmax b)
                     , fcount = newcount
                     , fsum_A = fsum_A a + (delta / fromInteger newcount)
                     , fsum_B = fsum_B a + fsum_B b + (delta * delta) * (fromInteger (counta * countb) / fromInteger newcount)
                     }

\end{spec}

\label{code:stats2Text}\index{stats2Text}
\begin{code}
stats2Text :: Stats -> Text
stats2Text (Stats slast _ sbasic sdelta stimed) =
    pack $
        "{ last=" ++ show slast ++
        ", basic-stats=" ++ showStats' (sbasic) ++
        ", delta-stats=" ++ showStats' (sdelta) ++
        ", timed-stats=" ++ showStats' (stimed) ++
        " }"
  where
    showStats' :: BaseStats -> String
    showStats' s =
        ", { min=" ++ show  (fmin s) ++
        ", max=" ++ show (fmax s) ++
        ", mean=" ++ show (meanOfStats s) ++ showUnits (fmin s) ++
        ", std-dev=" ++ show (stdevOfStats s) ++
        ", count=" ++ show (fcount s) ++
        " }"

\end{code}

\subsubsection{Exponentially Weighted Moving Average (EWMA)}\label{code:EWMA}\index{EWMA}
Following \url{https://en.wikipedia.org/wiki/Moving_average#Exponential_moving_average} we calculate
the exponential moving average for a series of values $ Y_t $ according to:

$$
S_t =
\begin{cases}
  Y_1,       & t = 1 \\
  \alpha \cdot Y_t + (1 - \alpha) \cdot S_{t-1},    & t > 1
\end{cases}
$$
\begin{code}
data EWMA = EmptyEWMA { alpha :: !Double }
          | EWMA { alpha :: !Double
                 , avg   :: !Measurable
                 } deriving (Show, Eq, Generic, ToJSON, FromJSON)

\end{code}

\subsubsection{Aggregated}\label{code:Aggregated}\index{Aggregated}
\begin{code}
data Aggregated = AggregatedStats !Stats
                | AggregatedEWMA !EWMA
                deriving (Eq, Generic, ToJSON, FromJSON)

\end{code}

\index{Aggregated!instance of Semigroup}
\todo[inline]{|instance Semigroup Aggregated| disabled for the moment, because not needed.}
\begin{spec}
instance Semigroup Aggregated where
    (<>) (AggregatedStats a) (AggregatedStats b) =
        AggregatedStats (a <> b)
    (<>) a _ = a

\end{spec}

\label{code:singletonStats}\index{singletonStats}
\begin{code}
singletonStats :: Measurable -> Aggregated
singletonStats a =
    let stats = Stats { flast  = a
                      , fold   = Nanoseconds 0
                      , fbasic = BaseStats
                                 { fmin   = a
                                 , fmax   = a
                                 , fcount = 1
                                 , fsum_A = getDouble a
                                 , fsum_B = 0 }
                      , fdelta = BaseStats
                                 { fmin   = 0
                                 , fmax   = 0
                                 , fcount = 1
                                 , fsum_A = 0
                                 , fsum_B = 0 }
                      , ftimed = BaseStats
                                 { fmin   = Nanoseconds 0
                                 , fmax   = Nanoseconds 0
                                 , fcount = 1
                                 , fsum_A = 0
                                 , fsum_B = 0 }
                      }
    in
    AggregatedStats stats

\end{code}

\index{Aggregated!instance of Show}
\begin{code}
instance Show Aggregated where
    show (AggregatedStats astats) =
        "{ stats = " ++ show astats ++ " }"
    show (AggregatedEWMA a) = show a

\end{code}

\subsubsection{Update aggregation}\label{code:updateAggregation}\index{updateAggregation}
We distinguish an unitialized from an already initialized aggregation. The latter is properly initialized.
\\
We use Welford's online algorithm to update the estimation of mean and variance of the sample statistics.
(see \url{https://en.wikipedia.org/wiki/Algorithms_for_calculating_variance#Welford's_Online_algorithm})

\begin{code}
updateAggregation :: Measurable -> Aggregated -> Word64 -> Either Text Aggregated
updateAggregation v (AggregatedStats s) tstamp =
    Right $ AggregatedStats $! Stats { flast  = v
                                     , fold = mkTimestamp
                                     , fbasic = updateBaseStats 1 v (fbasic s)
                                     , fdelta = updateBaseStats 2 deltav (fdelta s)
                                     , ftimed = updateBaseStats 2 timediff (ftimed s)
                                     }
  where
    deltav = subtractMeasurable v (flast s)
    mkTimestamp = Nanoseconds $ tstamp
    timediff = Nanoseconds $ fromInteger $ (getInteger mkTimestamp) - (getInteger $ fold s)

updateAggregation v (AggregatedEWMA e) _ =
    let !eitherAvg = ewma e v
    in
        AggregatedEWMA <$> eitherAvg

updateBaseStats :: Word64 -> Measurable -> BaseStats -> BaseStats
updateBaseStats startAt v s =
    let newcount = fcount s + 1 in
    if (startAt > newcount)
    then s {fcount = fcount s + 1}
    else
        let newcountRel = newcount - startAt + 1
            newvalue = getDouble v
            delta = newvalue - fsum_A s
            dincr = (delta / fromIntegral newcountRel)
            delta2 = newvalue - fsum_A s - dincr
            (minim, maxim) =
                if startAt == newcount
                then (v, v)
                else (min v (fmin s), max v (fmax s))
        in
        BaseStats { fmin   = minim
                  , fmax   = maxim
                  , fcount = newcount
                  , fsum_A = fsum_A s + dincr
                  , fsum_B = fsum_B s + (delta * delta2)
                  }

\end{code}

\subsubsection{Calculation of EWMA}\label{code:ewma}\index{ewma}
Following \url{https://en.wikipedia.org/wiki/Moving_average#Exponential_moving_average} we calculate
the exponential moving average for a series of values $ Y_t $ according to:

$$
S_t =
\begin{cases}
  Y_1,       & t = 1 \\
  \alpha \cdot Y_t + (1 - \alpha) \cdot S_{t-1},    & t > 1
\end{cases}
$$
\\
The pattern matching below ensures that the |EWMA| will start with the first value passed in,
and will not change type, once determined.
\begin{code}
ewma :: EWMA -> Measurable -> Either Text EWMA
ewma (EmptyEWMA a) v = Right $ EWMA a v
ewma (EWMA a s@(Microseconds _)) y@(Microseconds _) =
    Right $ EWMA a $ Microseconds $ round $ a * (getDouble y) + (1 - a) * (getDouble s)
ewma (EWMA a s@(Seconds _)) y@(Seconds _) =
    Right $ EWMA a $ Seconds $ round $ a * (getDouble y) + (1 - a) * (getDouble s)
ewma (EWMA a s@(Bytes _)) y@(Bytes _) =
    Right $ EWMA a $ Bytes $ round $ a * (getDouble y) + (1 - a) * (getDouble s)
ewma (EWMA a (PureI s)) (PureI y) =
    Right $ EWMA a $ PureI $ round $ a * (fromInteger y) + (1 - a) * (fromInteger s)
ewma (EWMA a (PureD s)) (PureD y) =
    Right $ EWMA a $ PureD $ a * y + (1 - a) * s
ewma _ _ = Left "EWMA: Cannot compute average on values of different types"

\end{code}
