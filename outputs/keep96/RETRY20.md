# KEEP=96: all twenty unresolved entries now solver UNSAT

On 17 October 2026, a bounded 300-second / 2048-MiB retry resolved all twenty previously UNKNOWN entries as UNSAT. The run took approximately 10 minutes 47 seconds. Each attempt terminated normally; no timeout was counted as success.

The combined solver count is now 262 UNSAT and zero UNKNOWN. This is not a completed Lean proof. The twenty new certificates have been checked for file integrity against their saved hashes, but have not yet been independently replayed or kernel checked.

All twenty new compressed DRUP certificates are included in this commit, approximately 409 MB in total; none of these twenty is omitted. `retry20-certificate-index.json` lists their exact paths, sizes and hashes. Formula hashes, solver configuration and logs are recorded in each attempt and in `retry20-results.json`. Original pilot and survey tables are unchanged. `retry20-combined-results.json` provides the combined table; older certificates outside this retry may still be absent from Git.

A fresh clone can use the twenty attempt paths directly. The certificate must be checked against its matching formula before reuse. The KEEP=96 Lean branch can fetch this commit and import the retry evidence without rerunning these twenty solver searches. Do not replace its active progress state or edit sources being compiled.
