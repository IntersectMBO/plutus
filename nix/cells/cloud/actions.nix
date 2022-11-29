{ cell
, inputs
}: {
  /* "plutus/ci" = {
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
  };*/

  "plutus/benchmark" = {
    task = "benchmark";
    io = ''
      // Two inputs need to match: PR sync event & issue comment creation event

      // WIP: Currently inlining lib.io.github_pr_comment
      // #lib.io.github_pr_comment &
      //
      {
        #input:   string | *"GitHub PR comment to \(#repo)"
        #prInput: string | *"GitHub PR to \(#repo)"

        #repo:    =~"^[^/]+/[^/]+$"
        #comment: string


        _prRepo: #repo

        let pr = {
          #lib.io.github_pr
          #input: #prInput
          #repo:  _prRepo
          inputs: _final_inputs
        }

        _final_inputs: inputs
        inputs: {
          pr.inputs

          "\(#input)": match: {
            github_event: "issue_comment"
            github_body: {
              action: "created"

              repository: full_name: #repo

              issue: pull_request: {}

              comment: body: =~#comment
            }
          }
        }

        let _body = inputs["\(#input)"].value.github_body
        _repo:    _body.repository.full_name
        _comment: _body.comment.body
        _number:  _body.issue.number

        #target: "zeme-iohk/benchmarking"
        #input: "${cell.library.actions.benchmark.commentInput}"
        #prInput: "${cell.library.actions.benchmark.prInput}"
        #repo: "input-output-hk/plutus"
        #comment: "^/benchmark .+"
      }
    '';
  };

  /*"plutus/publish-documents" = {
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
  };*/

}
