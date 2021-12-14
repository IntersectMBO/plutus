
\subsection{Cardano.BM.Counters}
\label{code:Cardano.BM.Counters}

The platform is chosen on which we compile this library.

Currently, we mainly support |Linux| with its 'proc' filesystem,
but also partially support |Windows|.

\begin{code}
{-# LANGUAGE CPP #-}

module Cardano.BM.Counters
    (
      readCounters
    , getMonoClock
    ) where

import           Cardano.BM.Data.Counter
import           Cardano.BM.Data.SubTrace

readCounters :: SubTrace -> IO [Counter]
readCounters _ = error "Not implemented on this platform"

getMonoClock :: IO [Counter]
getMonoClock = error "Not implemented on this platform"

\end{code}
