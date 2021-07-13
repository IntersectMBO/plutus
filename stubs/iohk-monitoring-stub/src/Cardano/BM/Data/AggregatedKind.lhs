
\subsection{Cardano.BM.Data.AggregatedKind}
\label{code:Cardano.BM.Data.AggregatedKind}

%if style == newcode
\begin{code}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}

module Cardano.BM.Data.AggregatedKind
  ( AggregatedKind (..)
  )
  where

import           Data.Aeson (FromJSON, ToJSON)
import           GHC.Generics (Generic)

\end{code}
%endif

\subsubsection{AggregatedKind}\label{code:AggregatedKind}\index{AggregatedKind}
\label{code:StatsAK}\index{AggregatedKind!StatsAK}
\label{code:EwmaAK}\index{AggregatedKind!EwmaAK}
This identifies the type of Aggregated.
\begin{code}
data AggregatedKind = StatsAK
                    | EwmaAK { alpha :: !Double }
                        deriving (Generic, Eq, Show, FromJSON, ToJSON, Read)

\end{code}
