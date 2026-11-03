# Attempt record for milestone 120

All original evidence is retained. Later receipts supersede earlier status
labels without changing the original bytes.

1. Eleven bounded probes were run. Nine have native negative answers, one has
   a positive radius-three forest, and one full-Q9 probe is UNKNOWN. The selected
   four-outer-count contradiction alone was taken through a complete Lean proof.
   The initial nine-transition target and its weakened variants require no
   sum counter. The two asymmetric cap-4 negatives remain uncertified probes.
2. The selected original certificate has 5,956 deductions and 344,241 hints.
   Resolving its input core again produced 6,777 deductions and 358,021 hints.
   Both replay independently against the original encoding. The shorter original
   proof was selected. The core-generation record retains its original
   `UNSAT_TRIMMED_NOT_REPLAYED` label; `data/native-audit.json` records the later replay.
3. The first export generated 118 modules, with one segment per check group.
   Those sources were not compiled. A grouped export uses the identical proof
   with six segments per group, reducing the proof portion to 24 modules.
4. The first grouped check stopped after four successful modules, before
   invoking Lean on Check1: Check1 imports the next checkpoint's Data2, which
   had not yet been built. This was a dependency-order failure in the run plan.
   `logs/check-run-1793673913709244500.json` preserves that attempt. No mathematical
   source was altered to resolve it.
5. The corrected plan builds all Data modules before the Check modules. Its
   25-module run, including ActualOuter120, passed in
   `logs/check-run-1793674102295627900.json`. The separate ReferenceCoverage120
   run also passed, giving 26 checked modules and 11 printed theorem audits.
   Four already verified modules were reused with exact receipt checks.
6. One sharpness-input setup command was routed to the probe program before
   its input file existed, causing FileNotFoundError before a solver ran. The
   input was then written correctly. The resulting full-Q9 probe remains UNKNOWN.
   Tool calls reported as aborted before dispatch did not run and are not solver
   attempts. A review-script adaptation syntax error was corrected before that
   script was executed; the final script and audit are preserved.
7. The graph producer checks all retained edges. The independent reviewer
   checks saved keys, orientations, potential data and arithmetic, without
   repeating the full graph optimization. Historical reports written before
   proof completion retain their pending labels. Consult the final proof review
   and verification record for the completed proof status.

The two pre-existing proof batches, 104 and 115, were observed with their live
process commands and left unchanged. Neither has completed its final assembly.
The paper and editor source remain revision 116 with identical saved hashes.
