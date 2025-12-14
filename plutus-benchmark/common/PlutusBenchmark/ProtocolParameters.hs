{-# LANGUAGE NumericUnderscores #-}

module PlutusBenchmark.ProtocolParameters (max_tx_size, max_tx_ex_steps, max_tx_ex_mem)
where

-- Protocol parameters (June 2023)

{-| This is the "maximum transaction size".  We're just comparing the size of
the script with this, so our results may be a little optimistic if the
transaction includes other stuff (I'm not sure exactly what "maximum
transaction size" means). -}
max_tx_size :: Integer
max_tx_size = 16384

max_tx_ex_steps :: Integer
max_tx_ex_steps = 10_000_000_000

max_tx_ex_mem :: Integer
max_tx_ex_mem = 14_000_000
