# Replay migration to checker v3: progress

Goal: free disk by replacing the old window replays `LocalWindowUnsat.<W>` (Q: 237 set, R: 236
set, K: 235 set) by drop-in v3 modules (`work/final_lean/LratV3.lean`), then re-audit 235/236/237.

## How to resume (after a container restart)

1. `pgrep -af migrate_v3` — if nothing runs, restart the driver; it skips every window with a
   `swap` line in `data/manifest.jsonl` and reuses staged files in `/home/user/v3stage`
   (`src/` sources not yet built, `lib/` built .olean not yet swapped):

   ```sh
   cd milestones/34-replay-migration/scripts
   setsid nohup python3 migrate_v3.py run --jobs 2 --stop-at <UNIX TIME> @../data/order.tsv >> /home/user/v3stage/run.log 2>&1 &
   python3 migrate_v3.py status
   ```

   A window whose gen was interrupted has a partial `/home/user/v3stage/work/<W>/`; `gen` starts it
   again from the core (`core_lrat` reuses a finished `.lrat` + `.lrat.json` there).
2. A swap is a copy + atomic rename of the .olean, then deletions, then the `swap` line. If the
   container died inside one (staged .olean still in `/home/user/v3stage/lib`, no `swap` line), the
   restarted driver verifies and swaps the window again; `verify` loads the production module
   first, so if its old Data/Check files are already gone, delete
   `work/final_lean/.lake/build/lib/lean/LocalWindowUnsat/<W>/`, `<W>.ilean` and
   `work/final_lean/LocalWindowUnsat/<W>{.lean,/}` by hand, check the production .olean equals the
   staged one (`cmp`), and append the `swap` line by hand.
3. `python3 stale.py LocalWindowDirUnsatR4b LocalWindowDirUnsatR4 LocalWindowDirUnsatK6` lists what
   `guarded_lake_build.py --direct --trust-mtime` would rebuild.

## Pilot (done, 10 Nov 05:50 UTC)

Windows Q012304A26432 (197 hints), Q01234A4244 (992,594), R012301A34324 (1,004,317). LRAT
regenerated from the committed cores with the original settings: same lemma/hint counts and the
same LRAT SHA256 as the 29 Oct packed pilot. v3 module (`gen_lean_lrat_v3.py`, seg 60k, OFF 4000,
13-bit words), same module name and theorem. Records in `data/pilot.jsonl`.

| window | old bytes | v3 .olean | old kernel CPU (Check + main) | v3 CPU (whole lean) | peak RSS |
|---|---:|---:|---:|---:|---:|
| Q012304A26432 | 112,075 | 32,448 | 0.59 s | 0.33 s | 0.40 GB |
| Q01234A4244 | 16,441,583 | 2,634,048 | 201.0 s | 126.8 s | 1.43 GB |
| R012301A34324 | 9,735,460 | 2,526,440 | 249.4 s | 122.7 s | 1.44 GB |

- `#check` (pp.all) of `unsat`: the same string from the old and the v3 module
  (`Snake9.LocalWindow.Unsat Snake9.LocalWindow.<W>.cnf`); `#print axioms`: propext,
  Classical.choice, Quot.sound.
- `lean/MigratePilotAggV3.lean` (the aggregate forms, `Tags.refuted_of_sat <W>.sat <W>.unsat`)
  compiled against the old and the v3 replays: both pass with the three standard axioms and give
  byte-identical .olean files.
- The three windows were then swapped in production.

## Production notes

- `LratV3.olean` and `ProofPack.olean` did not exist in the production lib; they were compiled once
  with `lean -o` into it (new files; no existing module was rebuilt).
- Pre-existing: `LocalWindowDirUnsatR4b` was already stale under `--trust-mtime` before the
  migration (the mains of Q01203A3443, Q01203A4433, Q01234A3434, Q01234A4334 have 23 Oct mtimes,
  after its 20 Oct .olean). The swap gives a new .olean `min(old mtime, oldest importing
  aggregate - 1 s)`, so it adds no staleness.
- No source is left for a migrated window (the v3 source is about 5 B/hint); it is regenerated
  deterministically from the core (`src_sha256` in the manifest).
- Order: `data/order.tsv` (`scripts/order.py`), greedy by bytes freed per CPU second within the disk.

## Log

- 05:58 UTC: full run started, `--stop-at` 13:00 UTC (no build started that would end after it).
- 06:20 UTC: driver restarted twice (gen now skips ahead to windows that fit the free disk; a
  window is verified at most 120 s after it is built; CPU model of `order.py` recalibrated to
  max(0.19 ms/hint, 0.62 x old check wall): the large Q windows take 0.19-0.24 ms/hint).
- 07:56 UTC: 179 windows swapped (101 Q, 78 R), 967 MB of old files replaced by 91 MB; disk free
  1.2 GB; Q01203A4344 (12.2 M hints) and Q01234A4334 (16.3 M) building.
