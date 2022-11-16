{ cell
, inputs
}: {
  actions = {
    ci.input = "GitHub event";
    benchmark.commentInput = "GitHub comment";
    benchmark.prInput = "GitHub pr";
    documents.input = "GitHub push";
  };
}
