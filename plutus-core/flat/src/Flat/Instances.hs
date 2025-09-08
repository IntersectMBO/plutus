
-- |Flat Instances for common data types from the packages on which `flat` has a dependency.
module Flat.Instances
  ( module X
  )
where

import Flat.Instances.Array ()
import Flat.Instances.Base ()
import Flat.Instances.ByteString ()
import Flat.Instances.Containers as X
import Flat.Instances.DList ()
import Flat.Instances.Mono as X
import Flat.Instances.Text as X
import Flat.Instances.Unordered ()
