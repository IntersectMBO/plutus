
\subsection{Cardano.BM.Data.Trace}
\label{code:Cardano.BM.Data.Trace}

%if style == newcode
\begin{code}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cardano.BM.Data.Trace
  ( Trace
  )
  where

import           Cardano.BM.Data.LogItem (LogObject(..), LoggerName)
import           Control.Tracer

\end{code}
%endif

\subsubsection{Trace}\label{code:Trace}\index{Trace}
A |Trace m a| is a |Tracer| containing the context name and a |LogObject a|.
\begin{code}

type Trace m a = Tracer m (LoggerName, LogObject a)
\end{code}
