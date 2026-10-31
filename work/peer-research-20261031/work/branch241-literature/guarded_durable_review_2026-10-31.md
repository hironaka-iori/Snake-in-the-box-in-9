# Durable guarded checkpoint review — 2026-10-31

Independent review PASS for the two round-1 byte snapshots identified in `guarded_durable_review_2026-10-31.json`. Each compressed file was read once into memory before decoding; its byte SHA256 was recorded. Both path hashes were unchanged at the end of their checks. This receipt does not cover subsequent atomic replacements by the concurrent round-2 search.

| Shape | Round | Snapshot SHA256 prefix | Static clauses | Fully checked RUP steps | Unit hints |
|---|---:|---|---:|---:|---:|
| 0120 | 1 | 763e87450c617b11 | 179,264 | 163,271 | 10,236,882 |
| 0123 | 1 | 31d6cbc300eef74d | 178,839 | 144,910 | 9,366,194 |

Both statuses are UNKNOWN; neither proof contains an empty clause. The complete static CNF was independently rebuilt (including geometric validation of every retained cycle, alpha rules, and the guarded cut), compared clause-for-clause, and checked for exact variable-count and integer vertex-map agreement. Every stored learned step was replayed from that rebuilt formula; the resulting step/hint counts equal the stored receipt. No search was launched and no checkpoint was modified.

The updated `continue_guarded.py` now rejects optimized `-O` execution, geometrically checks retained cycle cuts, reconstructs static CNF and variable maps at each resume, and checks complete consistency and static satisfaction of a saved terminal SAT witness. These changes were reviewed and no soundness defect was found. A SAT result continues to be explicitly local; no connectivity or global snake claim follows from this check.

The reviewed round-1 snapshots predate the added `static_sha256` and `verification_sources_sha256` fields. The independent checker therefore computed the static hashes directly; it did not assume these fields already existed. The new source hashes currently record four modules and are refreshed rather than compared with previous receipts. This is provenance logging rather than a source lock. Full ordered CNF reconstruction and full RUP replay still check the actual current derivation. For stronger provenance, also record the builder, PB encoding, solver parent modules, cycle-manifest hash, and a per-round source-hash history.

No new numerical upper bound or Lean replay is claimed. This review covers the indicated round-1 snapshots and the updated runner source hash recorded in JSON, not the ongoing round-2 outputs.
