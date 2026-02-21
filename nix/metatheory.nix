{ inputs, self, pkgs, lib, agda-tools }:

let

  # plutus-metatheory as an agda-package
  metatheory-agda-package = agda-tools.agda-packages.mkDerivation {
    name = "plutus-metatheory";
    pname = "plutus-metatheory";
    src = lib.cleanSource (self + /plutus-metatheory);
    buildInputs = [ agda-tools.agda-stdlib ];
    # The everythingFile is the compilation target for Agda, and is assumed
    # to transitively reference all other .agda files in the project.
    everythingFile = "./src/index.lagda.md";
    meta = { };
  };

  # Tarball of the Agda library sources for distribution as an artifact.
  metatheory-agda-library = pkgs.stdenv.mkDerivation {
    name = "metatheory-agda-library";
    src = lib.cleanSource (self + /plutus-metatheory);
    nativeBuildInputs = [ pkgs.gnutar ];
    buildPhase = "#";
    installPhase = ''
      mkdir -p $out plutus-metatheory
      find src -name '*agda*' -exec cp -p --parents -t plutus-metatheory {} \;
      cp plutus-metatheory.agda-lib plutus-metatheory
      tar -czvf $out/plutus-metatheory.tar.gz plutus-metatheory
    '';
  };

  # Developer helper: generates MAlonzo Haskell code from the metatheory.
  # Used in: `nix/shell.nix` pre-commit hook and common tools.
  generate-malonzo-code = pkgs.writeShellScriptBin "generate-malonzo-code" ''
    cd "$(git rev-parse --show-toplevel)/plutus-metatheory"
    agda-with-stdlib --compile --ghc-dont-call-ghc src/Main.lagda.md
  '';

  # Agda executable wrapper that includes both stdlib and the metatheory package.
  agda-with-stdlib-and-metatheory = pkgs.stdenv.mkDerivation {
    name = "agda-with-stdlib-and-metatheory";
    phases = "installPhase";
    OLD_AGDA = agda-tools.agda-packages.agda.withPackages [
      agda-tools.agda-stdlib
      metatheory-agda-package
    ];
    installPhase = ''
      mkdir -p $out/bin
      cp $OLD_AGDA/bin/agda $out/bin/agda-with-stdlib-and-metatheory
    '';
  };

  # We use a separate derivation to cache the slow Agda call, which makes it
  # easier to iterate on the site build.
  metatheory-agda-html = pkgs.stdenv.mkDerivation {
    name = "plutus-metatheory-doc";
    src = lib.cleanSource (self + /plutus-metatheory);
    buildInputs = [ agda-tools.agda-with-stdlib ];
    dontInstall = true;

    # Jekyll requires the _layouts folder to be in the same directory as the
    # source folder, so we copy it there to avoid issues.
    buildPhase = ''
      mkdir $out
      cp -R ${self + /plutus-metatheory/html/_layouts} $out
      agda-with-stdlib --html --html-highlight=auto --html-dir="$out" "src/index.lagda.md"
    '';
  };

  # This evaluates to a derivation that builds the AGDA metatheory
  # documentation site using Jekyll. The derivation also checks for broken links
  # in the generated HTML.
  #
  # This script can be useful if you are developing locally: it builds the site
  # then checks for broken links and finally serves the site on localhost.
  #
  # > cd plutus-metatheory
  # > agda --html --html-highlight=auto --html-dir=html "src/index.lagda.md"
  # > cp -R html/_layouts/ html/_site/
  # > jekyll build --disable-disk-cache -s html -d html/_site
  # > linkchecker html/_site --output failures
  # > python3 -m http.server --directory html/_site 8002
  metatheory-site = pkgs.runCommand "plutus-metatheory-site"
    {
      buildInputs = [
        pkgs.jekyll
        inputs.nixpkgs-2405.legacyPackages.${pkgs.stdenv.hostPlatform.system}.linkchecker
      ];
    } ''
    mkdir "$out"

    # Prevent Jekyll from writing to the source directory by disabling its disk cache
    jekyll build \
      --disable-disk-cache \
      -s ${metatheory-agda-html} \
      -d "$out"

    # Agda generates HTML files with href attributes containing absolute
    # file:///nix/store/* URLs. All HTML files are located in the top-level
    # build directory. The following command fixes all broken URLs.
    find "$out" -name "*.html" | xargs sed -i -E \
      's|href=\"file:///nix/store/.{32}-plutus-metatheory-site/([^\"]+)\"|href=\"\1\"|g'

    if ! linkchecker "$out/index.html" --output failures; then
      echo "Broken links found and printed above"
      exit 1
    fi
  '';
in

{
  inherit
    metatheory-agda-package
    metatheory-agda-library
    metatheory-site
    generate-malonzo-code
    agda-with-stdlib-and-metatheory;
}

