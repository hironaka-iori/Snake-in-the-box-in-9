# Bounded test of the proposed share floor 32 for shape 012034

The single cap-31 search returned **UNKNOWN** after 60.562 seconds. It returned no selected-vertex candidate. This supplies neither a counterexample to the proposed floor 32 nor a proof of that floor.

The test used the existing TaggedShare encoding with direction sequence `012034`, dimension 9, five centre bounds `[0,21]`, radius 4, share scale 12, and total integer share at most 31. The fixed path is `[0,1,3,7,6,14,30]`; its five centres are `[1,3,7,6,14]`. The formula contained 15,842 variables and 128,072 clauses. The backend was PySAT Cadical153, with 495 calls limited to 1,000 conflicts each. No additional cycle cut was required, since no candidate assignment was returned. The elapsed time includes solver creation and finishes at a conflict-budget boundary, accounting for the small excess over the requested 60 seconds.

The source implements independent checks on any returned assignment: all clauses, required induced path, selected vertices within the radius-four domain, selected degrees at most two, positive degree and at most two endpoints in the fully observed interior, connected components and cycles, all five singleton counts, and the five integer shares computed directly from empty squares and selected-neighbour counts. Cyclic candidates would be excluded and search would continue within the same time budget. None of these candidate-geometry checks was exercised in this run because the solver returned no candidate.

A satisfactory acyclic local configuration would be a local forest. It would not by itself show extension to a complete snake. Likewise, numerical UNSAT without a certificate and the required geometric argument would remain unproved. This run made neither claim and attempted no certificate generation or Lean expansion.

Files:

- `probe.py`: reproducible source, including the independent candidate census.
- `result.json`: solver status, timing, formula dimensions, solver statistics, formula fingerprint, and imported-source fingerprints.
- `README.md`: this scope report.

The existing case7302 share-20 proof sources and jobs were untouched. The bounded test stops here; no second cap or alternate solver was attempted.

Fingerprints:

- Probe source: `925fb7428638e07915f09bf595ab66419d7ddcc0a7c3a7f9a92b552089458d0f`.
- Result receipt: `79597cabf12d07abbb80fd478da19c9cf2fe982fc6d87b6c0eb2c2fc965225fc`.
- Initial CNF: `0eea4d75908899917e21ac1ddfc25304e963dcfb7cab5552b69273add34ec1ae`.

The imported TaggedShare, TaggedEncoding, and wincert source fingerprints in the receipt were checked against the current files after the run.
