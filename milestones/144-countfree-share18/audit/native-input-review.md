# Independent review of the count-free share18 input

Input review: `PASS_INPUT_RECONSTRUCTION_NO_COMPLETED_NATIVE_REPLAY`.

Native result: `TIMEOUT`, after 120.156 seconds. The saved process exit code is 1 following timeout termination. The 143,839,232-byte raw trace is incomplete historical evidence. This audit did not replay it, and neither a finite contradiction nor a share18 theorem is established by this attempt.

The exact input was independently reconstructed as 11,924 variables and 96,091 clauses. Its bytes match both saved input copies, with SHA-256 `ee9b49bb9c4ef3ff764febf44967d8a5008ddfcf4a1f324fd5eaae90170284a7`. The saved meanings, counters, totalizers and clause tags agree with the reconstruction. The 54,746-clause ordinary base encoding also matches the separate untagged encoder on 421 vertices.

The intended changes from milestone143 are cap 12 to cap 17, target 13 to target 18, updated provenance, a 120-second timeout and a 12-million-hint replay ceiling. The transition word `012034`, seven fixed window vertices, radius four, resolution 12, and five unrestricted singleton-square intervals `[0,21]` are unchanged. There are no added cycle cuts. The ordinary four- and six-cycle exclusions and endpoint budget of two remain part of the base input. No parity, prescribed total-path-length or endpoint-location restriction was introduced.

The share encoding retains 35 centre-neighbor incidences over 32 distinct neighbor vertices, preserving repeated contributions. It has 980 candidate empty-square variables, 18 threshold literals per incidence, 630 cap literals and 71 totalizers. The audit independently reconstructed the square and neighbor sets, all totalizer clauses, all `ceil(t*d/12)` thresholds and the cap17 clause. All saved source, native executable, certificate-file and log hashes matched. The audit's non-PASS branch records the terminal status without attempting a proof replay.

An eventual successful certificate would still require complete Lean replay and the actual-snake interpretation of the degree, endpoint, ordinary cycle and integer-share clauses. In particular, the one-direction totalizers require a justified satisfying assignment; repeated incidences must retain their multiplicity; saturation at 18 must be related to the assumption that the total share is at most 17. Reversed windows require reversing the path and the five-centre sum, as the reversed canonical word is `012342`.

The old case7302 completion record and the selected milestone143 evidence, including all preserved native certificate files, matched their earlier hashes before and after this audit. No older file was written. This preservation check is limited to the explicitly pinned files rather than the entire older directories.

The checker and receipt are `audit/review-native.py` and `data/native-input-review.json`. No solver, Lean compiler or graph search was invoked by the review. Any separate backend attempt requires its own result and audit; this report remains the record of the first native timeout.
