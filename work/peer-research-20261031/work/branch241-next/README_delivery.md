# Q9 window/share continuation — 2026-10-29

The new work follows the project's share/w3 window, CNF, lazy-cycle and certificate pipeline. It does not use Ramsey arguments. No new unconditional numerical upper bound has been proved. No Lean theorem or new SAT certificate is claimed.

## Strict mathematical progress

See branch241-next/math_findings.md for complete proofs. For selected x in a square-free subset of Q9,

    21*a(x) >= 21*alpha(x) + 2*e2(x) + e3(x) + V(x),
    V(x) = 12*C1(x) + 2*C2,1(x) + C2,2(x).

This yields a new valid global incidence inequality, and four small-scale positive window objectives. Complete pointwise integer scales are 1260 (adaptive) and 21 (uniform), with genuine induced-path witnesses showing minimality. These are ordinary mathematical proofs, not yet Lean formalizations or numerical improvements to a(9).

## Code and reproducibility

Extract the ZIP keeping branch241-next and branch241-audit as neighboring directories. branch241-audit contains ONLY the reference data/source needed by these scripts, not a complete Lean checkout. In branch241-next:

    python validate_fast.py
    python scan_bank.py
    python scan_cheap.py
    python local_coefficients.py
    python coefficient_identities.py
    python bonus_validation.py
    python encoding/validate_folded.py
    python encoding/validate_full_objective.py
    python encoding/build_pb_controls.py
    python encoding/github_query.py

All above use the Python standard library. PDF generation also requires ReportLab:

    python build_progress_pdf.py rendered

The bank scan is resumable and verifies input/engine/script hashes before reusing its checkpoint. If code or input changes, use --fresh explicitly. The scan checks all unordered pairs of each bank path before accepting it. Timings exclude reusable geometry setup and are machine dependent.

charge_fast.py replaces Fraction/set reconstruction with exact bitsets, integer arithmetic and incremental tail deletion. The validation has 193 square-free Q3 controls, 300 random Q4 sets, Q9 reference samples, and 17 pointwise incremental-versus-fresh checks. No random sample minimum is used as a universal bound.

cheap_folded.py emits fixed selected/forbidden units before using them to simplify objective gates; it preserves a constant offset. Do not forget that offset when imposing a cap. It optionally adds the stronger occupancy bonus. BinaryCNF uses carry-save/ripple binary addition and comparison, avoiding repeated high-weight literals and potentially enormous PB BDDs. Its 820 scalar assignment checks, known-bank positive/negative cap controls and independent unit propagation all passed.

## Actual GitHub geometric encoding

encoding/github_query.py loads the unchanged Encoding class from the supplied wincert.py via an AST containing only that class, avoiding the unused optional solver import. Its source SHA256 is recorded. It merges the original degree, endpoint-budget, no4/no6 clauses into the same variable namespace as the optimized objective, then adds the binary PB cap. The bank67 full positive control satisfies EVERY emitted clause.

The ready query encoding/github_window9_bonus_cap850.cnf.gz is for ONE nine-centre direction window. It is a free-window necessary-condition query, NOT an UNSAT result, universal window lower bound or upper-bound certificate. Unit propagation did not refute it. The threshold850 is exploratory. The two bank67_bonus_control_*.cnf.gz files instead FIX EVERY BASE VERTEX to the bank assignment and test exact/exact-minus-one caps; their triviality is deliberate and they are not upper-bound certificates.

Optional project-style search, only in an environment with working python-sat/CaDiCaL:

    python encoding/solve_window.py --cap 850 --centres 9 --max-rounds 10000

It adds valid cycle cuts, saves the final static CNF, and on UNSAT cold-solves before exporting DRUP. Such an export still needs independent checking and new Lean objective/gate semantics. LOCAL_SAT is only a local model (boundary pieces may remain), not automatically a global snake. The current Windows environment has no working SAT/Lean backend; the optional runner was attempted and reported solver unavailable. No install or workaround for blocked native libraries was attempted.

## Outputs and limits

131 bank paths and1703 long prefixes scanned; all supplied cycle-union controls retained. New cheap objectives and the occupancy bonus are checked pointwise, including64 independent random square-free local assignments for the full nine-centre bonus. Full per-bank results, exact integers, source hashes, raw CNF examples and all figure/PDF code are included.

The next proof-producing step is a complete window survey in the project's solver environment, followed by cold certificates, clause/gate soundness, a weighted-automaton bridge and full-product/Lean audits. A single-window UNSAT would still not finish that chain. Original proof sources, README, COLLABORATION and paper were not modified.
