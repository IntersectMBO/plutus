{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
module Tutorial.Solutions1 where

-- Solutions to E2 and E4*
-- (Rest of the solutions can be found in Tutorial.Solutions2 because of
--  TH staging restrictions)

import Tutorial.TH               (tricky)
import Language.PlutusTx.Prelude (lt, minus)
import Language.Haskell.TH

{-
    E2. 

    >>> $$(trickier 1) 1
    -8
    >>> $$(trickier 2) 1
    424
    >>> $$(trickier 3) 0
    -76403960

-}
trickier :: Int -> Q (TExp (Int -> Int))
trickier i = if $$lt i 1 then tricky else [|| \k -> $$(tricky) ($$(trickier ($$minus i 1)) k)  ||]


-- E3*. `trickier n` inlines the `tricky` function n times. In `trickierLight`
--      we bind `tricky` to a local name and use recursion instead. Note that
--      this only results in smaller code for n >= 10 (see Solutions2.hs)
trickierLight :: Int -> Q (TExp (Int -> Int))
trickierLight i = [|| 
  \(j :: Int) ->
    let
      trk = $$(tricky)
      go k = if $$lt k (1 :: Int) then trk j else trk (go ($$minus k 1))
      
  in go i ||]
