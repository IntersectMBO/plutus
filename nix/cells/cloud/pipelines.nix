{ cell
, inputs
}:
/*
  This code needs to be separate from any of the cells it uses
  to prevent infinite recursion. Specifically the `flakeOutputTasks`
  call triggers the error when called with any attribute that relies
  on the cell that the pipelines are defined in.
  That is why this is currently located in a separate cloud cell
  and not the automation cell.
*/
let
  inherit (inputs.nixpkgs) lib system;
  inherit (inputs.tullia) flakeOutputTasks taskSequence;
  inherit (inputs.cells.automation) ciJobs;

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

  # Only build the required job, other jobs might change and become unavailable
  # This is necessary because cicero only evaluates the task list on master,
  # instead of the current branch
  ciJobsToBuild = lib.getAttrs [ "required" ] ciJobs;
  ciTasks =
    (__mapAttrs
      (_: flakeOutputTask: { ... }: {
        imports = [ common flakeOutputTask ];

        memory = 1024 * 8;
        nomad.resources.cpu = 10000;
      })
      (flakeOutputTasks [ system "automation" "ciJobs" ] {
        # Replicate flake output structure here, so that the generated nix build
        # commands reference the right output relative to the top-level of the flake.
        outputs.${system}.automation.ciJobs = ciJobsToBuild;
      }));

  ciTasksSeq = taskSequence "ci/" ciTasks (__attrNames ciTasks);
in
if system == "x86_64-linux" then
  ciTasks // # for running separately
  ciTasksSeq // # for running in an arbitrary sequence
  {
    "ci" = { ... }: {
      imports = [ common ];
      after = __attrNames ciTasksSeq;
    };
  }
else { }
