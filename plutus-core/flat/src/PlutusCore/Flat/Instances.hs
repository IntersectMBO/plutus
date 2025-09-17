
-- |Flat Instances for common data types from the packages on which `flat` has a dependency.
module PlutusCore.Flat.Instances
  ( module X
  )
where

import PlutusCore.Flat.Instances.Array ()
import PlutusCore.Flat.Instances.Base ()
import PlutusCore.Flat.Instances.ByteString ()
import PlutusCore.Flat.Instances.Containers as X
import PlutusCore.Flat.Instances.DList ()
import PlutusCore.Flat.Instances.Mono as X
import PlutusCore.Flat.Instances.Text as X
import PlutusCore.Flat.Instances.Unordered ()
