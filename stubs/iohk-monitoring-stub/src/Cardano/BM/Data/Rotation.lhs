
\subsection{Cardano.BM.Data.Rotation}
\label{code:Cardano.BM.Data.Rotation}

%if style == newcode
\begin{code}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE LambdaCase         #-}

module Cardano.BM.Data.Rotation
  ( RotationParameters (..)
  )
  where

import           Data.Aeson (FromJSON (..), ToJSON)

import           GHC.Generics (Generic)
import           GHC.Word (Word64)

\end{code}
%endif

\subsubsection{RotationParameters}\label{code:RotationParameters}\index{RotationParameters}
\label{code:rpLogLimitBytes}\index{RotationParameters!rpLogLimitBytes}
\label{code:rpMaxAgeHours}\index{RotationParameters!rpMaxAgeHours}
\label{code:rpKeepFilesNum}\index{RotationParameters!rpKeepFilesNum}
\begin{code}
data RotationParameters = RotationParameters
    { rpLogLimitBytes :: !Word64  -- max size of file in bytes
    , rpMaxAgeHours   :: !Word    -- hours
    , rpKeepFilesNum  :: !Word    -- number of files to keep
    } deriving (Generic, Show, Eq, Ord, FromJSON, ToJSON)

\end{code}
