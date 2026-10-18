# Stage 2: independent census and minimal forbidden sets

Stage 1 passed: `outputs/window244/final-verification.json`, unconditional 244.
No bound 243/242 is claimed. Keep the completed Stage-1 Lean sources and data fixed.

## Running census

`survey_stage2.py` enumerates positive triples of sum at most nine, identifies
reversal-equivalent triples, and removes the known adjacent 1/<4 impossibilities.
This gives **24** triples (48 shape cases), not the 23 mentioned in the supplied
summary. In particular the legitimate candidate `(1,7,1)` is included; no claim
about its feasibility is made before running it. Retaining the complete enumeration
avoids relying on an undocumented omission in the previous census.

Each case has radius 3, seed 41, one worker, total 120 seconds including cycle
cuts. OR-Tools 9.15.6755 is used. Every actual solver invocation saves the model
text, parameters, log, status, elapsed time and SHA256s. Result and runner code
hashes are checkpointed. Existing 223 inputs are not overwritten.

```
python work/window244/survey_stage2.py --solver-packages /path/to/ortools/packages
```

State and evidence: `outputs/window244/stage2/survey.json` and per-case files.
The runner uses a lock and resumes saved cases. Normal running progress needs
no agent supervision. UNKNOWN is retained as UNKNOWN; all census outputs are
solver evidence, not Lean theorems.

## Subsequent obligations

1. Compare the completed independent census with the supplied 12/11 table.
2. Compute the minimum extra forbidden-pattern sets for bounds 243 and 242,
   including reversals and the already proved 222/223/322 restrictions.
   **Do not reuse the Stage-1 alpha truncation to 4/5:** newly forbidden patterns
   involving 4 or 5 can invalidate it. Use the true alpha range or justify a new
   compression above every forbidden entry, preserving parity and constraints.
3. Certify only necessary new patterns: explicit CNF, proof-logging solver,
   independent replay, generic semantic bridge, kernel checks and normalization.
4. Prove the stronger potential and aggregate consequence in Lean, with fresh
   source reconstruction and final axiom audit before reporting a better bound.
5. Do not extend radius for 233/242/324; new progress there needs a justified
   longer-window model or new invariant. No KEEP backpropagation work.

Only 244 is currently proved. Stop and report the original invalid-clause,
irreducible-memory, missing-shape, or three-working-day stagnation conditions.
