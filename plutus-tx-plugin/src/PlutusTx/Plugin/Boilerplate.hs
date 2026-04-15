{-| Insert necessary or recommended GHC flags and extensions via a driver plugin.
See https://plutus.cardano.intersectmbo.org/docs/using-plinth/extensions-flags-pragmas -}
module PlutusTx.Plugin.Boilerplate where

import PlutusTx.Compiler.Compat qualified as Compat

import GHC.Driver.Flags qualified as GHC
import GHC.Hs qualified as GHC
import GHC.LanguageExtensions qualified as GHC
import GHC.Plugins qualified as GHC
import GHC.Tc.Types qualified as GHC
import GHC.Types.SourceText qualified as GHC

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

-- | Add INLINEABLE to all bindings that carry no user-written inline pragma.
addInlineables :: GHC.TcGblEnv -> GHC.TcM GHC.TcGblEnv
addInlineables env = pure env {GHC.tcg_binds = binds'}
  where
    binds = GHC.tcg_binds env
    binds' = Compat.modifyBinds (map addInlineable) binds

addInlineableABE :: GHC.ABExport -> GHC.ABExport
addInlineableABE abe = case abe of
  GHC.ABE {GHC.abe_poly = v}
    | needsInlineable v -> abe {GHC.abe_poly = GHC.setInlinePragma v inlineable}
  _ -> abe

addInlineable :: GHC.LHsBindLR GHC.GhcTc GHC.GhcTc -> GHC.LHsBindLR GHC.GhcTc GHC.GhcTc
addInlineable (GHC.L loc bind) = GHC.L loc $ case bind of
  b@GHC.FunBind {GHC.fun_id = GHC.L idLoc v}
    | needsInlineable v ->
        b {GHC.fun_id = GHC.L idLoc (GHC.setInlinePragma v inlineable)}
  b@GHC.VarBind {GHC.var_id = v}
    | needsInlineable v ->
        b {GHC.var_id = GHC.setInlinePragma v inlineable}
  GHC.PatSynBind x psb@GHC.PSB {GHC.psb_id = GHC.L idLoc v}
    | needsInlineable v ->
        GHC.PatSynBind x psb {GHC.psb_id = GHC.L idLoc (GHC.setInlinePragma v inlineable)}
  GHC.XHsBindsLR as ->
    GHC.XHsBindsLR
      as
        { GHC.abs_exports = addInlineableABE <$> GHC.abs_exports as
        , GHC.abs_binds = Compat.modifyBinds (map addInlineable) (GHC.abs_binds as)
        }
  other -> other

-- | Return true if the @Id@ carries no user-written inline pragma.
needsInlineable :: GHC.Id -> Bool
needsInlineable = GHC.isDefaultInlinePragma . GHC.idInlinePragma

inlineable :: GHC.InlinePragma
inlineable =
  GHC.InlinePragma
    { GHC.inl_src = GHC.NoSourceText
    , GHC.inl_inline = GHC.Inlinable GHC.NoSourceText
    , GHC.inl_sat = Nothing
    , GHC.inl_act = GHC.AlwaysActive
    , GHC.inl_rule = GHC.FunLike
    }
