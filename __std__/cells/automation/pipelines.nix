{
  cell,
  inputs
}:
let
  inherit (inputs.tullia) flakeOutputTasks taskSequence;
  inherit (inputs.nixpkgs.stdenv) system;

  common =
    { config
    , ...
    }: {
      preset = {
        # needed on top-level task to set runtime options
        nix.enable = true;

        github-ci = {
          # Tullia tasks can run locally or on Cicero.
          # When no facts are present we know that we are running locally and vice versa.
          # When running locally, the current directory is already bind-mounted
          # into the container, so we don't need to fetch the source from GitHub
          # and we don't want to report a GitHub status.
          enable = config.actionRun.facts != { };
          repo = "input-output-hk/plutus";
          sha = config.preset.github-ci.lib.getRevision "GitHub event" null;
        };
      };
    };

  ciTasks = __mapAttrs
    (_: flakeOutputTask: { ... }: {
      imports = [ common flakeOutputTask ];

      memory = 1024 * 8;
      nomad.resources.cpu = 10000;
    })
    (flakeOutputTasks [ system "ciJobs" ] { outputs.${system}.ciJobs = cell.ciJobs; });

  ciTasksSeq = taskSequence "ci/" ciTasks (__attrNames ciTasks);
in
if system == "x86_64-linux" then
  ciTasks // # for running tasks separately
  ciTasksSeq // # for running in an arbitrary sequence
  {
    "plutus/ci" = { lib, ... }: {
      imports = [ common ];
      after = __attrNames ciTasksSeq;
    };
  }
else {}
