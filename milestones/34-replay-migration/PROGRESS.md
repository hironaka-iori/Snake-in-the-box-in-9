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
- 08:50 UTC: main's floor port copied from tmpfs to disk: `/home/user/floors233` (461 MB, `cp -a`,
  `diff -rq` clean). `/dev/shm/floors233` left in place. The on-disk overlay is made at the end.
- 09:47 UTC: 187 windows swapped (107 Q, 80 R), 3.22 GB of old files replaced by 0.24 GB; disk
  free 2.7 GB. Building Q01234A3335 and Q0120A334 (24.0 M hints). R01203A4434 (39 M hints) and
  R01203A3453 (34 M) are past the time budget of this run (estimated 7.5 h and 4.1 h of CPU).
- 13:00 UTC: run finished at `--stop-at` (`{"done": true, "err": null}`). **334 windows migrated**
  (196 Q, 138 R, 0 K; 189.8 M hints): **6,755,894,868 B of old files replaced by 525,299,384 B**,
  6.23 GB freed. Build CPU 12.8 h in all, peak RSS 5.3 GB; 0 failed builds, 0 failed verifications.
  Per window: `data/manifest.tsv` (old bytes, new bytes, CPU, RSS, status). Not migrated: 414
  windows (191 Q, 223 R; 485.8 M hints, 12.1 GiB of old files), among them R01203A4443 (42 M hints),
  R01203A4434 (39 M), R01203A3453 (34 M); all K windows (packed already, 2.2 GB).

## Aggregates and audits (13:05-13:50 UTC)

- `stale.py` before the builds: `LocalWindowDirUnsatR4b` stale (pre-existing, see above),
  `LocalWindowDirUnsatR4` and `LocalWindowDirUnsatK6` up to date. `LocalWindowDirUnsatR4.lean` was
  then touched (mtime only) so that it is rebuilt against the v3 replays; after that the check gave
  exactly {R4b} and {R4}, and nothing else in the 7,996 / 28,790-module closures. K6 imports no
  migrated window, so it was not rebuilt.
- `guarded_lake_build.py --direct --trust-mtime --jobs 1 --rss-cap-gb 13`, one target at a time:
  `LocalWindowDirUnsatR4b` 123 s, 3.5 GB; `LocalWindowDirUnsatR4` 389 s, 10.5 GB; no other module
  compiled (`data/aggregate_build.jsonl`); `allRefuted237`/`allRefuted236`: standard axioms.
- `chain_audit.py --reuse` (`outputs/upper-bound-23{6,5,7}-audit-linux-v3.log`): UpperBound236
  (193 s, 11.8 GB), UpperBound235 (228 s, 11.7 GB), UpperBound237 (the 34 R4b shards had been
  swept and were rebuilt; 1,523 s wall): all **AXIOM AUDIT PASSED**, `propext`,
  `Classical.choice`, `Quot.sound` only.
- The 234 and 233 conditional chains (`AggregateDirection7B234`, `AggregateDirection6SB233`,
  `Floors233Main`) do not import the three aggregates or any `LocalWindowUnsat.[QRK]` module (only
  `UpperBound235/236/237` and the unbuilt `LocalWindowDirUnsatReuse7*` do), so they were not re-run.

## To continue

Rerun the driver with a later `--stop-at` (same command as above); it takes the remaining windows of
`data/order.tsv`. The three giant R windows need about 4-8 h of CPU each and 2-2.4 GB of staging.
For K windows `migrate_v3.py` has a K path (cores of `lean_core_direction_k6`, CNF regenerated by
`gen_k6_core.regen_cnf`) that has not been run; `order.tsv` has no K rows.

## Second run (from 13:50 UTC)

- `data/order2.tsv`: the 414 windows not migrated, in the order of `order.tsv`, with R01203A3453,
  R01203A4434 and R01203A4443 last (27 CPU-hours estimated before them).
- Shared with the 233 certificate agent (`milestones/33-233-lean/CERT-PROGRESS.md`, which needs
  1.2 GB free disk): `--min-disk-mb 1500`, `--rss-cap-gb 6.0` per `lean`, a build starts only with
  6.5 GB available, at most 2 `lean` processes, `--stop-at` 22:00 UTC.

  ```sh
  setsid nohup python3 migrate_v3.py run --jobs 2 --min-disk-mb 1500 --rss-cap-gb 6.0 --min-avail-gb 6.5 \
      --stop-at 1794348000 @../data/order2.tsv >> /home/user/v3stage/run2.log 2>&1 &
  ```
