Criterion templates for use by benchmarking code.  `with-iterations.tpl` is used
to produce an extended version of Criterion's HTML report which includes the
total number of runs of each benchmark and the total execution time.  This will
only work with newer versions of Criterion due to a change in the JavaScript
library that it uses to render charts; use the `-t` option to point older
versions of Criterion at `default-old.tpl` to avoid problems in that case.