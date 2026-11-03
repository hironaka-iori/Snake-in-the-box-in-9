# Milestone 135: a checked count of low-pair windows

A complete theorem for actual snakes has passed Lean: at most thirty-two
fitting canonical 012032 windows can have relevant pair sum at most nine.
The starts are counted once each; windows may overlap, and no path-length
parity assumption is imposed. The proof assigns windows through the checked
common-neighbour property and bounds each endpoint group by sixteen.

The proof includes endpoint normalization, parity and injective reindexing,
separation of differently labelled windows, the covered-union capacity, and
the disjoint partition between endpoints. Five modules and seventeen theorem
reports passed. All compiler attempts and exact dependencies are saved.
The sixteen statement uses the unselected common-neighbour assignment; it
does not assert the broader arbitrary Hamming-distance assignment statement.

The missing-degree identities for the stronger written proof also passed,
including the exceptional three-missing-pair count. Twelve per endpoint and
twenty-four in total remain pending. Next: construct maximal intervals and
combine their actual run-length bounds, degree sums and boundary conventions.

This occurrence theorem alone gives no new upper bound on snake length.
The fixed uniform-credit limitation from milestone 132 still applies.
The recorded interval remains 191–235, with incomplete independent rebuilding
of the contributor upper proof. Optimality and 196 remain open. The paper
remains at revision 126 and is due for its next full revision at milestone 136.
Ordinary notation is retained; no new named mathematical definitions are added.

## Saved material

- MATHEMATICAL_NOTE.md gives the statement, proof and limits for the length problem.
- lean/ contains the five checked modules.
- data/ retains successful receipts, a verification record and a checkpoint.
- logs/ preserves each compiler attempt with exact source and checker bytes.
- audit/ contains the statement review and process-backed batch observations.
- scripts/ verifies inputs, dependencies, proof axioms, saved files and staged bytes.

The successful finite pair-capacity proof from milestone 134 is reused by hash.
Its exhaustive computation is not repeated. The longer milestone 115 job
remains separate, and its incomplete state is not counted as a completed proof.
