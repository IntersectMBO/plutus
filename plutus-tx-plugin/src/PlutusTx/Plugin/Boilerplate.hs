{-| Insert necessary or recommended GHC flags and extensions via a driver plugin.
See https://plutus.cardano.intersectmbo.org/docs/using-plinth/extensions-flags-pragmas -}
module PlutusTx.Plugin.Boilerplate where

import GHC.Driver.Flags qualified as GHC
import GHC.LanguageExtensions qualified as GHC
import GHC.Plugins qualified as GHC

{-| Unfortunately, it seems like the `Strict` extension set by the driver plugin cannot be
unset via @LANGUAGE NoStrict@. So we add a plugin flag to allow users to do so. -}
optNoStrict :: GHC.CommandLineOption
optNoStrict = "no-strict"

boilerplateOpts :: [GHC.CommandLineOption]
boilerplateOpts = [optNoStrict]

removeBoilerplateOpts :: [GHC.CommandLineOption] -> [GHC.CommandLineOption]
removeBoilerplateOpts = filter (`notElem` boilerplateOpts)

addFlagsAndExts :: [GHC.CommandLineOption] -> GHC.HscEnv -> IO GHC.HscEnv
addFlagsAndExts opts env = pure env {GHC.hsc_dflags = dflags}
  where
    dflags = setStrict . unsetFlags $ GHC.hsc_dflags env

    unsetFlags :: GHC.DynFlags -> GHC.DynFlags
    unsetFlags =
      flip
        (foldl GHC.gopt_unset)
        [ GHC.Opt_IgnoreInterfacePragmas
        , GHC.Opt_OmitInterfacePragmas
        , GHC.Opt_FullLaziness
        , GHC.Opt_SpecConstr
        , GHC.Opt_Specialise
        , GHC.Opt_Strictness
        , GHC.Opt_UnboxStrictFields
        , GHC.Opt_UnboxSmallStrictFields
        ]

    setStrict :: GHC.DynFlags -> GHC.DynFlags
    setStrict =
      if optNoStrict `elem` opts then id else (`GHC.xopt_set` GHC.Strict)
