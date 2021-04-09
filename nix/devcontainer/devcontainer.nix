{ name ? "devcontainer"
, tag ? null
, extraContents ? [ ]
, extraCommands ? ""
, nonRootUser ? "plutus"
, nonRootUserId ? "1000"
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
, runtimeShell
, shadow
, stdenv
, xz
, which
}:
let
  # I think we should be able to use buildLayeredImage, but for some reason it
  # produces a nonfunctional image
  image = dockerTools.buildImage {
    inherit name tag;

    contents = [
      # See: https://github.com/NixOS/nixpkgs/issues/118722
      (stdenv.mkDerivation {
        name = "wrapped";
        src = ./root;
        installPhase = "ln -s $src $out";
      })
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

      # allow ubuntu ELF binaries to run. VSCode copies it's own.
      chmod +w lib64
      ln -s ${glibc}/lib64/ld-linux-x86-64.so.2 lib64/ld-linux-x86-64.so.2
      ln -s ${gcc-unwrapped.lib}/lib64/libstdc++.so.6 lib64/libstdc++.so.6
      chmod -w lib64
    '' + extraCommands;

    runAsRoot = ''
      ${dockerTools.shadowSetup}
      groupadd --gid ${nonRootUserId} ${nonRootUser}
      useradd --uid ${nonRootUserId} --gid ${nonRootUserId} -m ${nonRootUser}

      # Because we map in the `./.cabal` folder from the users home directory,
      # (see: https://github.com/input-output-hk/plutus-starter/blob/main/.devcontainer/devcontainer.json)
      # and because docker won't let us map a volume not as root
      # (see: https://github.com/moby/moby/issues/2259 link), we have to make the
      # folder first and chown it ...
      mkdir /home/${nonRootUser}/.cabal
      chown ${nonRootUser}:${nonRootUser} /home/${nonRootUser}/.cabal
    '';

    config = {
      Cmd = [ "/bin/bash" ];
      User = nonRootUser;
      Env = [
        "BASH_ENV=/etc/profile.d/env.sh"
        "GIT_SSL_CAINFO=/etc/ssl/certs/ca-bundle.crt"
        "LD_LIBRARY_PATH=${gcc-unwrapped.lib}/lib64"
        "PAGER=less"
        "PATH=/usr/bin:/bin"
        "SSL_CERT_FILE=${cacert}/etc/ssl/certs/ca-bundle.crt"
        "USER=${nonRootUser}"
      ];
    };
  };
in
image // { meta = nix.meta // image.meta; }
