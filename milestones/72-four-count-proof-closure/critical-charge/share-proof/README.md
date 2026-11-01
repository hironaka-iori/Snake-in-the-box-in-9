# Share-120 theorem

Checkpoint: 1 November 2026. The proof and source audit pass for 99 generated or imported modules and 72 printed theorem audits. Existing local-window support is reused; no fresh rebuild of every inherited dependency is claimed.

Let six consecutive transitions of an arbitrary snake in Q9 use distinct directions. If its five internal singleton counts are (4,5,4,2,t), with 6 <= t <= 21, their total integer share is at least 120. The share is the sum over neighbours q of floor(12 e_0(q)/d_S(q)), using the established natural-number convention. This local theorem includes coordinate normalization.

The proof checks 59 batches of geometric clause meanings, counter and totalizer structure, and their composition. The 7,534-clause core is refuted by 713,670 LRAT hints. A newly compiled checker variant uses offset 8192 and 14-bit words. The final theorem combines the refutation with the arbitrary-snake share bridge. Its printed axioms are limited to propext, Classical.choice and Quot.sound. The source audit rejects sorry, admit, native_decide and sorryAx and checks source-to-core correspondence.

See data/proof-audit.json, data/export.json and data/bridge-source.json. The bridge is pinned to its exact contributor commit and source hash. The successful logs supersede earlier failed assembly attempts; completion records retain failed attempts as history. A grouping error in the first concatenation proof was fixed by composing prefixes in the same order as the data definitions. Fresh temporary output files avoid the Windows replacement error seen in one duplicate compiler run.

## Limits and effect

This is a local share theorem, not a new global bound. The integrated interval remains 191 <= a(9) <= 235. The complete arbitrary-snake finite-graph interpretation remains unfinished. In the ten-count-case model, admitting this theorem reduces the fixed-potential count obligations from 14,143 to 14,142, removing basis key 24473. The earlier eight-case model's minimum mean stays 480 when this share is added. Further critical cycles need other inequalities.

## Reproduction

The sources are retained under lean/, with large replay data also preserved in data/lean-sources.tar.gz. data/archive.json records the archive hash and compressed native formula/proof hashes. The inherited source dependencies are listed in scripts and build records; this is a repository-based replay, not a standalone Lean project.

From critical-charge/scripts: prepare_lean.py generates core and semantic batches; replay_share.py checks those batches; export_share.py generates the larger-offset sound checker and refutation modules. Existing Compose, Sat, Refuted and Geometry sources supply the proof assembly. complete_share.py checks the remaining dependency graph and reuses source-matched results. audit_share.py checks the completed evidence. Restore archived source files and native files before replay if they are absent.

The compact CNF/LRAT and archived Lean source bytes are preserved; Git must not normalize audited proof sources. The manuscript remains at revision 66 pending its scheduled full revision.
