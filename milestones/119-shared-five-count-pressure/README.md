# Milestone 119: actual counterexamples and full-cube count restrictions

A complete 148-edge snake contains a 012304 window with singleton counts
(3,6,3,4,6). Its total 22 disproves the proposed lower bound 23, even with
the first, third and fourth counts at most 4 and the other two at least 6.
Lean checks the complete induced path, window directions, exact counts and
counterexample. Nine axiom reports pass in 36.656 seconds. No mathematical
terminology was introduced, and no new long-snake lower bound is claimed.

Four local probes give four independently checked local forests. Six full-cube
probes give three complete snakes, two native contradictions and one UNKNOWN.
The complete snakes have 148,148 and 144 edges. The last realizes the exact
critical tuple (4,6,2,4,6). Boundary relaxation is therefore insufficient to
explain every surviving low-count state.

The two full-cube contradictions support total at least 23 under the respective
bounds [2,6..21,2,3,6..21] and [2,6..21,4,2,6..21]. Plain and tagged encoders
produce identical formulas. Separate native replay checks 19264 and 43795
deductions with 2240349 and 5045692 hints. Both concrete Lean contradictions,
sum semantics and actual-snake transfers remain pending. Their exact proofs
are preserved locally and in four verified transport archives.

The oriented 13-rule experiment reproduces the 117 removal set and both full
weight vectors before applying the new rules. They add credit on 449 and 446
suffix keys and remove no edges. Replacement cycles preserve both means and
ranges: 2915/6 with 1730/3, and 496 with 602. Integer comparisons remain 235 and 234.
All-edge potential inequalities were checked by the producer; the independent
review checks saved cycles, orientations, potential bytes and arithmetic.

The replacement cycles have no common five-centre direction shape. The next
single test is the full nine-transition word 012031043 from edge 18806, with
all six recorded counts constrained simultaneously and no extra sum cap.

At the process-verified snapshot,104 reports 162/791 contexts in each profile;
115 reports 232/1397 checked modules. Both drivers remain active and unchanged.
Their final assemblies remain pending. The maintained interval remains 191
through 235 edges, with the contributor proof and archived audit for 235 and its
complete independent rebuild pending. Conditional 234 and the optimum remain
unresolved. There are 1366 pending reference entries. Paper revision 116 is
unchanged; the next full revision is 126.

## Next test

Test the full-Q 9 realization of edge 18806, whose nine directions are
[0,1,2,0,3,1,0,4,3]. Its eight internal-centre bounds are
[[0,21],[0,21],[6,21],[3,3],[3,3],[6,21],[3,3],[3,3]].
The first two centres are unrestricted. The six recorded counts lie at
centres 3 through 8. Retain the entire interval [6,21] for each symbol 6.
Do not impose total 24: that would test only exact 6 values and could not
exclude the full bucket. The prepared case is data/next-edge-case.json.
It has not been searched in 119.

A positive full-cube result must pass connectedness and all-pairs induced-path
checks. An UNKNOWN result remains unresolved. A negative result needs a saved
certificate and independent encoding/proof checks before any exclusion is used.
Evaluate any viable restriction on both profiles. Do not duplicate or change
the active 104 and 115 proof batches. The new 119 native contradictions and the 117
count contradiction remain pending Lean work.

## Evidence and reproduction

- `lean/Counterexample119.lean` and `data/Counterexample119-audit.json`: the actual length148 counterexample and checked comparison arithmetic.
- `data/witness-audit.json` and `data/probe-audit.json`: four radius-four local forests.
- `data/full-probe-audit.json`: all six full-cube attempts and three ordered complete paths.
- `data/independent-full-witness-audit.json`: independent orders and all-pairs checks for the two initial complete paths.
- `data/negative-audit.json`: byte-identical plain-CNF rebuild and separate proof replay for both negative cases.
- `data/full-critical23/results.json` and `data/graph-audit.json`: conditional graph result and independent saved-cycle audit.
- `data/large-artifact-archives.json`: exact proof archive and original-byte hashes.
- `audit/graph-review.md`, `audit/full-witness-review.md` and `audit/cycle-review.md`: independent reviews with explicit scopes.

Run `scripts/verify_saved.py --verify` with the configured Python runtime.
After cloning, `scripts/verify_saved.py --restore-archives` restores missing
large original proof files without overwriting different bytes. Solver and
audit scripts refuse to overwrite earlier result files. No new global bound
or Lean-checked negative theorem follows from this milestone.
