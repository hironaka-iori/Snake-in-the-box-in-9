# Guarded-cut independent review — 2026-10-31

Scope: `probe_guarded_cuts.py`, `continue_guarded.py`, both frozen `cut_probes` tails, and their exact source checkpoints. This review launches no SAT search and modifies neither the original merged checkpoints nor running guarded checkpoints.

## Result: PASS within the stated scope

The independent executable `review_guarded_20261031.py` rebuilt both original static formulas from the query builder, verified every induced-cycle manifest entry geometrically (200,298 entries per shape), reconstructed the project alpha rules, and checked equality with the source checkpoint clauses. It then rebuilt the 4,876 guarded-cut clauses and checked exact equality with the recorded additions. Both compressed source hashes match their probe receipts.

All positive-hint RUP steps were replayed independently from the reconstructed static formula:

| Shape | Static clauses after cut | Old prefix steps / hints | New tail steps / hints |
|---|---:|---:|---:|
| 0120 | 179,264 | 114,445 / 7,667,762 | 3,147 / 190,794 |
| 0123 | 178,839 | 100,548 / 6,927,242 | 2,407 / 113,273 |

Neither proof contains an empty clause. Both results are UNKNOWN. These are checked derivations within the local relaxation; they do not establish the desired triple threshold, a new global numerical bound, or a Lean-checked geometric bridge.

## Clause numbering and durable initialization

Let n be the original static count, delta=4876. Old static hint IDs 1..n remain unchanged. Every old learned-clause hint ID greater than n increases by delta. An old learned clause at position j therefore remains identified by n+delta+j. No old proof clause itself changes. The probe tail was generated with exactly this new static formula and the complete shifted prefix already installed, so concatenating it after that shifted prefix without another offset is correct.

On a new durable run, the code verifies the source checkpoint byte hash, reconstructs the cut, and compares it with the probe additions. On every resume it reconstructs the static formula, compares the complete ordered clause list and variable count, and restores integer vertex keys from JSON string keys. The solver's safe constructor verifies the entire stored prefix before using any learned clause. New tails are checked against static plus that verified prefix before saving. Static clauses are never designated reducible learned clauses. Original merged checkpoints are read-only in this runner.

The guarded-cut mathematical assumptions were reviewed separately: U contains the chosen root, every neighbor of every U vertex is present in the variable domain, and the endpoint flags describe true global endpoints there. The actual 46-vertex U has 252 crossing cube edges. The positive PB is algebraically equivalent to selected crossing edges + selected global endpoints in U >= 2*selected root, a necessary condition for a nontrivial global induced path.

## Defensive improvements, not observed counterexamples

1. `continue_guarded.py` currently trusts the geometric validity of `static8.json.gz` when rebuilding. Its equality and allowed-vertex checks do not themselves prove each listed cut is a cycle. The present manifests were independently validated in full here; add `verify_cycle(c)` during rebuilding to make this invariant explicit on future resumes.
2. Store source hashes of the query/encoding/rule/cut modules and the cycle manifest alongside the static formula hash. Exact formula reconstruction and RUP checking already protect the mathematical CNF inference from an accidentally changed proof prefix; explicit hashes improve provenance.
3. The existing terminal-SAT resume branch checks proof validity but does not recheck the saved model before returning. No current probe is SAT. If SAT occurs, revalidate the full CNF and local geometric score, preserve the local-only label, and perform an independent global-path check before making a construction claim.
4. The code uses Python `assert` for provenance and reconstruction guards. Run without `-O`, as the current commands do; explicit exceptions would prevent accidental guard removal in optimized mode.

No concrete soundness counterexample was found in either actual probe or the reviewed continuation logic. A local SAT model, if found, would remain a local-model result until connectivity and global induced-path conditions are independently proved.
