workspace(name = "plutus")

load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

git_repository(
    name = "io_tweag_rules_haskell",
    remote = "https://github.com/tweag/rules_haskell.git",
    commit = "e134749dbdd926515be1d30495dafd8c72c26a61",
)

load("@io_tweag_rules_haskell//haskell:repositories.bzl", "haskell_repositories")

haskell_repositories()

http_archive(
    name = "io_tweag_rules_nixpkgs",
    strip_prefix = "rules_nixpkgs-0.3.1",
    urls = ["https://github.com/tweag/rules_nixpkgs/archive/v0.3.1.tar.gz"],
)

load(
    "@io_tweag_rules_nixpkgs//nixpkgs:nixpkgs.bzl",
    "nixpkgs_package",
)

nixpkgs_package(
    name = "ghc",
    attribute_path = "ghc",
    nix_file_content = """
      let
        localLib = import ./lib.nix;
        localPackages = import ./. { pkgsGenerated = <pkgsGenerated>; 
                                     requiredOverlay = <requiredOverlay>;
                                     errorOverlayPath = <errorOverlay>; };
        pkgs = localPackages.pkgs;
        plutusPkgs = map (x: localPackages.localPackages.${x}) localLib.plutusPkgList;
        haskellLib = pkgs.haskell.lib;
        packageInputs = map haskellLib.getBuildInputs plutusPkgs;
        haskellInputs = pkgs.lib.filter
          (input: pkgs.lib.all (p: input.outPath != p.outPath) plutusPkgs)
          (pkgs.lib.concatMap (p: p.haskellBuildInputs) packageInputs);
        ghc = localPackages.haskellPackages.ghcWithPackages (p: 
          haskellInputs
        );
      in
        pkgs // { inherit ghc; }
      """,
    nix_file_deps = [
        "@//:lib.nix",
        "@//:default.nix",
    ],
    repositories = { 
      "pkgsGenerated" : "//:pkgs/default.nix",
      "requiredOverlay" : "//:nix/overlays/required.nix",
      "errorOverlay" : "//:nix/overlays/force-error.nix",
    }
)

nixpkgs_package(
    name = "happy",
    attribute_path = "haskellPackages.happy",
    # For vector example. Just use `attribute_path = haskell.compiler.ghc822`
    # when no extra packages needed.
    nix_file_content = """
      let
        localPackages = import ./. { pkgsGenerated = <pkgsGenerated>; requiredOverlay = <requiredOverlay>; };
        pkgs = localPackages.pkgs;
      in
        pkgs
      """,
    nix_file_deps = [
        "@//:lib.nix",
        "@//:default.nix",
    ],
    repositories = { 
      "pkgsGenerated" : "//:pkgs/default.nix",
      "requiredOverlay" : "//:nix/overlays/required.nix",
      "errorOverlay" : "//:nix/overlays/force-error.nix",
    }
)

nixpkgs_package(
    name = "alex",
    attribute_path = "haskellPackages.alex",
    # For vector example. Just use `attribute_path = haskell.compiler.ghc822`
    # when no extra packages needed.
    nix_file_content = """
      let
        localPackages = import ./. { pkgsGenerated = <pkgsGenerated>; 
                                     requiredOverlay = <requiredOverlay>;
                                     errorOverlayPath = <errorOverlay>; };
        pkgs = localPackages.pkgs;
      in
        pkgs
      """,
    nix_file_deps = [
        "@//:lib.nix",
        "@//:default.nix",
    ],
    repositories = { 
      "pkgsGenerated" : "//:pkgs/default.nix",
      "requiredOverlay" : "//:nix/overlays/required.nix",
      "errorOverlay" : "//:nix/overlays/force-error.nix",
    }
)

register_toolchains("//:ghc")
