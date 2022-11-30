{ cell
, inputs
}: {
  "plutus/ci" = {
    task = "ci";
    io = ''
      // This is a CUE expression that defines what events trigger a new run of this action.
      // There is no documentation for this yet. Ask SRE if you have trouble changing this.

      let github = {
        #input: "${cell.library.actions.ci.input}"
        #repo: "input-output-hk/plutus"
      }

      #lib.merge
      #ios: [
        #lib.io.github_push & github,
        { #lib.io.github_pr, github, #target_default: false },
      ]
    '';
  };

  "plutus/benchmark" = {
    task = "benchmark";
    io = ''
      #lib.io.github_pr_comment & {
        #input: "${cell.library.actions.benchmark.input}"
        #repo: "input-output-hk/plutus"
        #comment: "^/benchmark .+"
      }
    '';
  };

  "plutus/publish-documents" = {
    task = "publish-documents";
    io = ''
      let push = {
        #lib.io.github_push
        #input: "${cell.library.actions.documents.input}"
        #repo: "input-output-hk/plutus"
        inputs: _final_inputs
      }

      _final_inputs: inputs
      inputs: {
        push.inputs

        "CI passed": match: {
          ok: true
          revision: push._revision
        }
      }
    '';
  };

}
