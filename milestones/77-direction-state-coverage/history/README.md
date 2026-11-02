# Numeric history interface and signature recognition

The interface in [NumericHistory.lean](lean/NumericHistory.lean) passed Lean 4.19.0 in 3.531 seconds. The successful receipt in `data/proof-audit.json` records nine theorem audits and exact source, object and log hashes. Only `propext`, `Classical.choice` and `Quot.sound` occur in the reported axiom lists.

The source imports the existing milestone75 history development and adds nine short declarations:

- A generic signature equivalence: if a stored word is the longest dictionary suffix of the actual past, and a signature's proper prefix belongs to the dictionary, then the signature is a suffix of the actual past followed by the new symbol exactly when it is a suffix of the stored word followed by that symbol. The signature itself need not belong to the dictionary.
- Decoding a dictionary entry at its first-occurrence index returns that entry.
- The numeric history index is the position of the stored history in the 75-entry dictionary; it is below 75 and decodes to that stored history, with any fallback value.
- Empty input has index zero.
- A nonempty stored history after appending a symbol ends in that symbol, both before and after numeric decoding.
- The listed-signature equivalence is instantiated for both the stored word and its numeric dictionary index.

The numeric index is defined as `prefixes.idxOf (run prefixes w)`. Membership in the dictionary follows from the existing longest-suffix theorem; this supplies the in-range proof needed to rule out a failed-lookup fallback. No direction-table or graph-state assumption is introduced.

## Check status

The two existing source and object files, `HistoryPrefix` and `ExactHistory`, match the successful milestone75 receipt before each attempt. Both bounded attempts terminated with a Lean memory-limit exception before producing theorem diagnostics: 256 MiB in 6.406 seconds and 512 MiB in 4.156 seconds. The exact diagnostics and command receipts are preserved in `logs/memory-256.log`, `logs/memory-512.log`, `data/memory-256.json` and `data/memory-512.json`.

[scripts/check.py](scripts/check.py) requires at least 1.5 GiB of available physical memory before starting. The final invocation imposes no Lean memory cap. An attempted command-line memory option was unsupported and its diagnostic is preserved. The checker runs one compiler, checks inherited source/object hashes, rejects disallowed proof shortcuts, audits every printed theorem's axioms and saves the new source/object/log hashes on success. It does not rebuild inherited support.

After memory became available, source diagnostics exposed a mismatch between the list Boolean-equality instances used by two lookup lemmas. The checked source uses the core lookup-range lemma and a direct induction for decoding. The earlier failed attempts are retained as diagnostics; the successful receipt identifies the current checked version.

## Scope

This module does not identify actual snake direction IDs, prove source/target state membership, select exclusion or share rules, replay a graph potential, or imply a numerical upper bound. The compiled milestone75 support and installed mathlib are reused; their full dependency closure is not rebuilt. No live certificate or file outside this history folder was changed.
