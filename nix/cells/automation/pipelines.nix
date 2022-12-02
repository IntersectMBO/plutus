{ cell
, inputs
}:
let
  common =
    { config
    , ...
    }: {
      preset = {
        nix.enable = true;

        github.ci = {
          # Tullia tasks can run locally or on Cicero.
          # When no facts are present we know that we are running locally and vice versa.
          # When running locally, the current directory is already bind-mounted
          # into the container, so we don't need to fetch the source from GitHub
          # and we don't want to report a GitHub status.
          enable = config.actionRun.facts != { };
          repository = "input-output-hk/plutus";
        };
      };
    };
in
{
  ci = { config, lib, ... }: {
    imports = [ common ];

    preset.github.ci.revision = config.preset.github.lib.readRevision
      inputs.cells.cloud.library.actions.ci.input
      null;

    command.text = config.preset.github.status.lib.reportBulk {
      bulk.text = "nix eval .#__std.init --apply __attrNames --json | nix-systems -i";
      each.text = ''nix build -L .#"$1".automation.ciJobs.required'';
      skippedDescription = lib.escapeShellArg "No nix builder available for this system";
    };

    memory = 1024 * 8;
    nomad.resources.cpu = 10000;
  };

  publish-documents = { config, pkgs, lib, ... }: {
    imports = [ common ];

    preset.github.ci.revision = config.preset.github.lib.readRevision
      inputs.cells.cloud.library.actions.documents.input
      null;

    command.text =
      let
        documents = __mapAttrs (_: v: "${v}.pdf") {
          plutus-report = "plutus-report";
          plutus-core-spec = "plutus-core-specification";
          extended-utxo-spec = "extended-utxo-specification";
          unraveling-recursion-paper = "unraveling-recursion";
          system-f-in-agda-paper = "paper";
          eutxo-paper = "eutxo";
          utxoma-paper = "utxoma";
          eutxoma-paper = "eutxoma";
        };
      in
      ''
        set -x

        nix build -L ${lib.escapeShellArgs (map (k: ".#${k}") (__attrNames documents))}

        revision=$(${lib.escapeShellArg config.preset.github.ci.revision})
      '' + __concatStringsSep "\n" (lib.imap0
        (i: k: ''
          jq > ${lib.escapeShellArg k}.json --null-input \
            --arg revision "$revision" \
            --arg document ${lib.escapeShellArg k} \
            '{"plutus/document/\($document)": $revision}'

          http --multipart --ignore-stdin "$CICERO_WEB_URL/api/run/$NOMAD_JOB_ID/fact" \
            value@${lib.escapeShellArg k}.json \
            binary@result${
              lib.optionalString (i != 0) "-${toString i}"
            }/${lib.escapeShellArg documents.${k}}
        '')
        (__attrNames documents)
      );

    dependencies = with pkgs; [ jq httpie ];

    memory = 1024 * 4;

    nomad = {
      resources.cpu = 5000;

      templates = [
        {
          destination = "${config.env.HOME}/.netrc";
          data = ''
            machine cicero.ci.iog.io
            login cicero
            password {{with secret "kv/data/cicero/api"}}{{.Data.data.basic}}{{end}}
          '';
        }
      ];
    };
  };
}
