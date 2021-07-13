
\subsection{Cardano.BM.Data.Observable}
\label{code:Cardano.BM.Data.Observable}

%if style == newcode
\begin{code}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}

module Cardano.BM.Data.Observable
  (
    ObservableInstance (..)
  )
  where

import           Data.Aeson (FromJSON (..), ToJSON)

import           GHC.Generics (Generic)

\end{code}
%endif

\subsubsection{ObservableInstance}\label{code:ObservableInstance}\index{ObservableInstance}
\label{code:MonotonicClock}\index{ObservableInstance!MonotonicClock}
\label{code:MemoryStats}\index{ObservableInstance!MemoryStats}
\label{code:ProcessStats}\index{ObservableInstance!ProcessStats}
\label{code:NetStats}\index{ObservableInstance!NetStats}
\label{code:IOStats}\index{ObservableInstance!IOStats}
\label{code:SysStats}\index{ObservableInstance!SysStats}
\label{code:GhcRtsStats}\index{ObservableInstance!GhcRtsStats}
\begin{code}
data ObservableInstance = MonotonicClock
                        | MemoryStats
                        | ProcessStats
                        | NetStats
                        | IOStats
                        | SysStats
                        | GhcRtsStats
                          deriving (Generic, Eq, Show, FromJSON, ToJSON, Read)

\end{code}
