{ system ? builtins.currentSystem
, config ? {}
, localPackages ? import ./. { inherit config system; }
}:
localPackages.dev.withDevTools (localPackages.haskellPackages.shellFor {
    packages = p: (map (x: p.${x}) localPackages.localLib.plutusHaskellPkgList);
})
