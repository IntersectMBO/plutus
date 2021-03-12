{ name ? "devcontainer"
, tag ? null
, extraContents ? [ ]
, extraCommands ? ""
, dockerTools
, bashInteractive
, cacert
, closureInfo
, coreutils
, curl
, direnv
, findutils
, gcc-unwrapped
, git
, glibc
, gnugrep
, gnused
, gnutar
, gzip
, iana-etc
, iproute
, less
, lib
, nix
, openssh
, procps
, shadow
, xz
, which
}:
let
  image = dockerTools.buildImage {
    inherit name tag;

    contents = [
      ./root
      coreutils
      procps
      gnugrep
      gnused
      less

      # add /bin/sh
      bashInteractive

      # runtime dependencies of nix
      cacert
      git
      gnutar
      gzip
      xz

      # for haskell binaries
      iana-etc

      # for user management
      shadow

      # for the vscode extension
      gcc-unwrapped
      iproute
      findutils
      # yes, it breaks without `which`!
      which
    ] ++ extraContents;

    extraCommands = ''
      # for /usr/bin/env
      mkdir usr
      ln -s ../bin usr/bin

      # make sure /tmp exists
      mkdir -m 1777 tmp

      # need a HOME
      mkdir -vp root

      # allow ubuntu ELF binaries to run. VSCode copies it's own.
      chmod +w lib64
      ln -s ${glibc}/lib64/ld-linux-x86-64.so.2 lib64/ld-linux-x86-64.so.2
      ln -s ${gcc-unwrapped.lib}/lib64/libstdc++.so.6 lib64/libstdc++.so.6
      chmod -w lib64

    '' + extraCommands;

    config = {
      Cmd = [ "/bin/bash" ];
      Env = [
        "BASH_ENV=/etc/profile.d/env.sh"
        "GIT_SSL_CAINFO=/etc/ssl/certs/ca-bundle.crt"
        "LD_LIBRARY_PATH=${gcc-unwrapped.lib}/lib64"
        "PAGER=less"
        "PATH=/usr/bin:/bin"
        "SSL_CERT_FILE=${cacert}/etc/ssl/certs/ca-bundle.crt"
        "USER=root"
      ];
    };
  };
in
image // { meta = nix.meta // image.meta; }
