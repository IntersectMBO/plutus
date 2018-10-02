{ nixpkgs ? <nixpkgs>
, declInput ? {
    uri = "git@github.com:input-output-hk/plutus.git";
    rev = "refs/heads/master";
  }
, plutusPrsJSON ? ./simple-pr-dummy.json
}:

let
    pkgs = import nixpkgs {};

    plutusPrs = builtins.fromJSON (builtins.readFile plutusPrsJSON );

    mkGitSrc = { repo, branch ? "refs/heads/master"}: {
      type = "git";
      value = repo + " " + branch;
      emailresponsible = false;
    };

    mkJob = { name, description, nixexprinput ? "plutusSrc", nixexprpath, extraInputs }: {
      inherit name;
      value = {
        inherit description nixexprinput nixexprpath;

        inputs = {
          jobsetSrc = mkGitSrc {
            repo = declInput.uri;
            branch = declInput.rev;
          };

          nixpkgs = mkGitSrc {
            repo = "https://github.com/NixOS/nixpkgs-channels";
            branch = "refs/heads/nixos-18.09";
          };
        } // extraInputs;

        enabled = 1;
        hidden = false;
        checkinterval = 90;
        schedulingshares = 100;
        emailoverride = "";
        enableemail = false;
        keepnr = 3;
      };
    };

    mkPlutusJob = {
      name,
      description,
      plutusBranch
    }:
      mkJob {
        inherit name description;
        nixexprpath = "release.nix";
        extraInputs = {
          plutusSrc = mkGitSrc {
            repo = "https://github.com/input-output-hk/plutus.git";
            branch = plutusBranch;
          };
        };
      };

    plutusJobsetDefinition = pkgs.lib.listToAttrs (
      [
        (mkPlutusJob {
          name = "master";
          description = "Plutus Master Branch";
          plutusBranch = "refs/heads/master";
        })
      ]
      ++
      (pkgs.lib.mapAttrsToList
        (
          num:
          info: mkPlutusJob {
            name = "plutus-PR-${num}";
            description = info.title;
            plutusBranch = info.head.sha;
          }
        )
        plutusPrs
      )
    );

    jobsetDefinition = plutusJobsetDefinition;
in {
  jobsets = pkgs.runCommand "spec.json" {} ''
    cat <<EOF
    ${builtins.toXML declInput}
    EOF

    tee $out <<EOF
    ${builtins.toJSON jobsetDefinition}
    EOF
  '';
}
