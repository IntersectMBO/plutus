{ stdenv, lib, ruby, bundlerApp, makeWrapper, defaultGemConfig,
  # Optional dependencies, can be null
  epubcheck, kindlegen,
  # For the update shell
  mkShell, bundix,
  # For mathematical
  cmake, bison, flex, glib, pkgconfig, cairo, pango, gdk_pixbuf, libxml2, python3, patchelf
}:

bundlerApp {
  pname = "asciidoctor";
  gemdir = ./.;

  exes = [
    "asciidoctor"
    "asciidoctor-pdf"
    "asciidoctor-safe"
    "asciidoctor-epub3"
  ];

  postBuild = ''
      # Our nixpkgs is too old for bundlerApp to have buildInputs
      source ${makeWrapper}/nix-support/setup-hook

      wrapProgram "$out/bin/asciidoctor-epub3" \
        ${lib.optionalString (epubcheck != null) "--set EPUBCHECK ${epubcheck}/bin/epubcheck"} \
        ${lib.optionalString (kindlegen != null) "--set KINDLEGEN ${kindlegen}/bin/kindlegen"}
    '';

  gemConfig = defaultGemConfig // {
    asciidoctor-epub3 = attrs: {
      patches = [./pr-201.patch];
      # as per the source comments in nixpkgs, we need this to apply patches
      dontBuild = false;
    };
    mathematical = attrs: {
      buildInputs = [
        cmake
        bison
        flex
        glib
        pkgconfig
        cairo
        pango
        gdk_pixbuf
        libxml2
        python3
      ];

      # The ruby build script takes care of this
      dontUseCmakeConfigure = true;

      # For some reason 'mathematical.so' is missing cairo and glib in its RPATH, add them explicitly here
      postFixup = lib.optionalString stdenv.isLinux ''
        soPath="$out/${ruby.gemPath}/gems/mathematical-${attrs.version}/lib/mathematical/mathematical.so"
        ${patchelf}/bin/patchelf \
          --set-rpath "${lib.makeLibraryPath [ glib cairo ]}:$(${patchelf}/bin/patchelf --print-rpath "$soPath")" \
          "$soPath"
      '';
    };
  };

  meta = with lib; {
    description = "A faster Asciidoc processor written in Ruby";
    homepage = https://asciidoctor.org/;
    license = licenses.mit;
    maintainers = with maintainers; [ gpyh ];
    platforms = platforms.unix;
  };
}
