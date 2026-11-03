# Milestone 138: exclusion of the competing cycle

The full nine-transition condition012301430 with counts(>=6,3,3,3,5,2)
at vertices3 through8 is excluded for arbitrary Q9 snakes. The complete
Lean chain passed, including coordinate normalization and the actual-snake
conclusion, with no parity or endpoint-location premise.

This removes one row of the saved seven-edge comparison cycle. The completed
four-cycle survives, so deletion alone leaves its profile's minimum at488.
The maintained snake-length interval remains191–235.

The next selected calculation combines this deletion with the proved24-window
allowance. Test uniform suffix credit83/3: the old four- and eighteen-cycle
means then meet at3011/6. A potential of mean at least3011/6 and range below
7753/6 would make the inherited comparison fall below235. The arithmetic is
Lean-checked; existence of such a potential and remaining graph hypotheses
are unresolved.

The stronger012301 upper-cap claim(3,3,3,5,2) has a completely replayed native
proof but awaits Lean. All attempts and exact evidence are retained.
Read MATHEMATICAL_NOTE.md, data/proof-completion.json and the two final source
reviews before using either result. The original import-wrapper failure is
superseded by lean/ActualBase138Minimal.lean.

The paper received a targeted update without new definitions. Source checks
passed; the built-in compiler failed before TeX, so the PDF is unverified.
