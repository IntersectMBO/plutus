{ system ? builtins.currentSystem
, config ? { allowUnfreePredicate = (import ./lib.nix {}).unfreePredicate;
             packageOverrides = (import ./lib.nix {}).packageOverrides;
           }
, localPackages ? import ./. { inherit config system; rev = "in-nix-shell"; }
}:
localPackages.dev.withDevTools (localPackages.haskellPackages.shellFor {
    packages = p: (map (x: p.${x}) localPackages.localLib.plutusPkgList);
})
