# Round 182: an unused-coordinate extension and a stronger local certificate

The user requested a pause after this round. The round is complete; publish its saved results and pause without starting round 183.

Read [the mathematical argument](MATHEMATICAL_NOTE.md) for the proof and its limitations. The main results are:

- All four floor-14 local Boolean inputs now have complete native contradiction replays. The final 012301 replay added 211,501 checked clauses and 11,406,626 propagation hints.
- Lean checks that a canonical 012301 window in any snake of length at least seven must extend in one of its five unused coordinates. The degree exclusions and full canonical-window statement are included.
- A written cube-isometry argument reduces extension to the representative vertex 16. The corresponding floor-15 Boolean query returned UNSAT, and its complete native replay passed: 100,151 clauses and 4,348,019 propagation hints.
- Lean checks the arithmetic for the changed share cap and a limitation of the single-floor upgrade. In the retained profile (14,15,14,14), a cycle and walk force the loss-one comparison to be at least (235+21/42248). This remains above 235; changing only this floor cannot close the remaining low-loss cases through the current mean-and-range argument.

Three Lean modules passed, with nine theorem dependency reports. The full coordinate-isometry transfer, Boolean-counter semantics and local Lean contradiction chains remain unfinished. No new unconditional numerical bound or longer construction is claimed. The maintained project range is 191–235, with the archived upper-bound proof's complete independent rebuild still pending; 234 remains conditional.

## Evidence

| Item | Saved evidence | Status |
| --- | --- | --- |
| Final floor-14 replay | `data/012301-extended-replay.json` | Complete native replay |
| Actual-path extension theorem | `data/ExtensionDirection182-audit.json` | Lean passed |
| Cap truncation arithmetic | `data/ShareTruncation182-audit.json` | Lean passed |
| Floor-15 query with either extension | `data/012301-floor15.json` | Proof-size stop; no conclusion |
| Floor-15 query with extension 16 | `data/012301-floor15-fixed16.json` | Native UNSAT |
| Fixed-extension floor-15 replay | `data/012301-floor15-fixed16-replay.json` | Complete native replay |
| Reweighted cycle and walk | `data/single15-witnesses.json` | Original source rows reconstructed |
| Limitation of that comparison | `data/SingleFloorObstruction182-audit.json` | Lean passed |

The fixed-extension solver record retains the label assigned immediately after solving. Its separate replay record establishes completion of native replay. None of these native receipts is a Lean contradiction certificate.

The stronger unrestricted query reached the 128 MiB raw-proof limit after about 87.48 seconds. Its incomplete proof is preserved and is never treated as a refutation. The fixed-extension query completed in about 27.22 seconds with a 37,061,374-byte raw proof. The search change uses the written symmetry reduction; these timings are individual observations, without a general performance claim.

## Files and resource limits

The `lean/`, `build/`, `logs/` and `data/` directories contain source, accepted objects, receipts and failed-attempt evidence. `certificates/` stores compressed inputs, changed-cap meanings and proof files. `cache/` retains large uncompressed files locally and is excluded from publication. `source-before/` preserves the manuscripts before this round's update.

The streamed solver and native replay retain the 1 GiB startup requirement, 256 MiB private limit and 768 MiB free-memory reserve. Solver searches are limited to 90 seconds and 128 MiB raw proof; native replay is limited to 240 seconds. Core Lean retains its existing 60-second resource profile. Several Lean attempts stopped before startup or under the free-memory reserve; two initial source attempts exposed an XOR-notation rewrite error. These are archived separately from the accepted corrected sources. No guard was weakened.

The full manuscript and short explanation are updated in their existing editor files and mirrored to `paper/`. Author order and hyperlink settings are preserved. Continue only after a new user instruction.
