{ localPackages ? import ./default.nix { rev = "in-nix-shell"; }
}:
localPackages.dev.withDevTools (localPackages.haskellPackages.shellFor {
    packages = p: (map (x: p.${x}) localPackages.localLib.plutusPkgList);
})
