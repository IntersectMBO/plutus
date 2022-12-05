# This file specifies the cicero actions.  If you change this file, you
# _must_ re-create the job https://cicero.ci.iog.io/action/ for it to
# take any effect.

{ cell
, inputs
}:
let
  inherit (inputs.nixpkgs) lib system;
  inherit (inputs.cells) cloud;
  inherit (inputs.cells.plutus) library;
  inherit (library) pkgs;

  common =
    { config
    , ...
    }: {
      preset = {
        nix.enable = true;

        github = {
          # Tullia tasks can run locally or on Cicero.
          # When no facts are present we know that we are running locally and vice versa.
          # When running locally, the current directory is already bind-mounted
          # into the container, so we don't need to fetch the source from GitHub
          # and we don't want to report a GitHub status.
          ci.enable = config.actionRun.facts != { };
          ci.repository = "input-output-hk/plutus";
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
      bulk.text = ''
        nix eval .#__std.init --apply __attrNames --json | # all systems the flake declares
        nix-systems -i | # figure out which the current machine is able to build
        jq 'with_entries(select(.value))' # only keep those we can build
      '';
      each.text = ''nix build -L .#"$1".automation.ciJobs.required'';
      skippedDescription = lib.escapeShellArg "No nix builder available for this system";
    };

    memory = 1024 * 8;
    nomad.resources.cpu = 10000;
  };

  benchmark = { config, ... }:
    let
      fact = config.actionRun.facts.${cloud.library.actions.benchmark.input}.value.github_body;
      prNumber = toString fact.issue.number;

      # Script gets current commit from HEAD in git repo it's ran in
      runner = cell.library.plutus-benchmark-runner {
        PR_NUMBER = prNumber;
        BENCHMARK_NAME = lib.removePrefix "/benchmark " fact.comment.body;
        GITHUB_TOKEN = "/secrets/cicero/github/token";
      };
    in
    {
      # Not importing commn module defined above, because we don't need the github preset
      preset.nix.enable = true;

      # clone and checkout git repo at latest revision at the time the action is run
      # might be inaccurate if a commit was pushed in between comment creation and action run
      preset.git.clone = {
        enable = true;
        remote = "https://github.com/input-output-hk/plutus";
        # Tullia has some magic to get the revision when given a script like this
        ref.outPath = lib.getAttr "outPath" (pkgs.writeScript "get-pr-rev" ''
          ${lib.getExe pkgs.curl} \
            -H "Accept: application/vnd.github+json" \
            https://api.github.com/repos/input-output-hk/plutus/pulls/${prNumber} \
            | ${lib.getExe pkgs.jq} -r .base.sha
        '');
      };
      command.text = "${runner}/bin/plutus-benchmark-runner";
      nomad.templates = [
        {
          destination = "/secrets/cicero/github/token";
          data = ''{{with secret "kv/data/cicero/github"}}{{.Data.data.token}}{{end}}'';
        }
      ];

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
