# This file evaluates to a derivation that builds the AGDA metatheory
# documentation site using Jekyll. The derivation also checks for broken links
# in the generated HTML.
{ repoRoot, inputs, pkgs, system, lib }:

let

  # This script can be useful if you are developing locally: it builds the site
  # then checks for broken links and finally serves the site on localhost.
  local-development = ''
    cd plutus-metatheory
    agda --html --html-highlight=auto --html-dir=html "src/index.lagda.md"
    cp -R html/_layouts/ html/_site/
    jekyll build --disable-disk-cache -s html -d html/_site
    linkchecker html/_site --output failures
    python3 -m http.server --directory html/_site 8002
  '';

  # We use two separate derivations to cache the slow Agda call, which makes it
  # easier to iterate on the site build.
  plutus-metatheory-agda-html = pkgs.stdenv.mkDerivation {
    name = "plutus-metatheory-doc";
    src = lib.cleanSource (inputs.self + /plutus-metatheory);
    buildInputs = [ repoRoot.nix.agda-with-stdlib ];
    dontInstall = true;

    # Jekyll requires the _layouts folder to be in the same directory as the
    # source folder, so we copy it there to avoid issues.
    buildPhase = ''
      mkdir $out
      cp -R ${inputs.self + /plutus-metatheory/html/_layouts} $out
      agda --html --html-highlight=auto --html-dir="$out" "src/index.lagda.md"
    '';
  };

  plutus-metatheory-site = pkgs.runCommand "plutus-metatheory-site"
    {
      buildInputs = [ pkgs.jekyll pkgs.linkchecker ];
    }
    ''
      mkdir "$out"

      # Prevent Jekyll from writing to the source directory by disabling its disk cache
      jekyll build \
        --disable-disk-cache \
        -s ${plutus-metatheory-agda-html} \
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

plutus-metatheory-site
