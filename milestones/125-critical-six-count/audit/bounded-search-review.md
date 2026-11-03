# Audit of the explicit-bound cap-22 search

The strengthened search `0120324-total22-positive` timed out after 60.062
seconds. It returned neither a model nor a complete contradiction. No
six-count floor of 23 follows from this run.

The independent audit rebuilt its complete 7,277-variable, 106,348-clause
formula. The window has directions $0120324$, the six-count total is capped
at 22, and the individual intervals are

$$
[1,21],\ [2,21],\ [1,21],\ [3,21],\ [1,21],\ [1,21].
$$

These are explicit additional constraints. The search-script comparison
matches the changes recorded in `data/bounded-search-provenance.json`:
the new interval vector, restriction to cap 22, and the separate attempt name.
The earlier two-attempt audit and its artifacts remain unchanged.

The formula retains all 126 corner occurrences over 100 distinct corners:
79 occur once, 16 twice and five three times. The eight original cycle seeds
again produce the same 35 distinct cuts under all 24 permutations of unused
coordinates 5 through 8. Every orbit image was checked to be a connected
induced cycle, and every permutation fixes the specified window and preserves
cube adjacency. The audit compared every generated clause with the saved CNF.

The proposed actual-snake justification uses positivity, the prefix pair
minima, a first/fourth-count exclusion and a suffix outer-sum bound. Its
intended statement applies to an actual $0120324$ window whose six-count total
is at most 22. It would justify the interval vector under that premise; it
would not itself rule out the window.

At the time this search audit was frozen, `ActualBounds125` had no successful
receipt. Its first check failed on an unresolved slice lemma and arithmetic
normalization. The failed log, source snapshot, checker snapshot and record
are pinned. The bridge is therefore recorded as
`PENDING_AFTER_FAILED_SOURCE_CHECK`. Any later successful theorem review must
be read separately from this preserved search checkpoint.

The native process was terminated with exit code 1. Its partial proof trace
contains 56,430,592 bytes, with the exact hash preserved. Neither SAT nor UNSAT
was printed. The audit therefore performed no model validation or completed
LRAT replay for this attempt.

No solver or compiler was invoked by the auditor. Evidence is saved in
`data/bounded-search-audit.json`, with 21 pinned files and SHA256
`04c478706d5369926dc0e5b4f85eb0f595f248807bd995443ff661ad1bb78d71`.
The repeatable auditor is `scripts/audit_bounded_search.py`.
