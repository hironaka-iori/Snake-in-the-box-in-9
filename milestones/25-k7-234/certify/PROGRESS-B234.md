# Progress of the B234 shard build (this machine)

Production build of `WindowAutomaton7B234Data` and the 792 shards `WindowAutomaton7B234Shard<i>_<t0>`
of the final key set `../data/keys_best234.json.gz` (tag `B234`, λ = 6423/1544, 13 bits, range
8,152, bound 234). Started 31 October 2026. Machine: 4 cores, 15 GB RAM, about 0.4 GB of free disk.

## How it runs

- **Where.** Sources are generated into `work/final_lean` and compiled there by
  `work/guarded_lake_build.py --direct --trust-mtime` into `work/final_lean/.lake/build/lib/lean`,
  with `LEAN_PATH = work/spectral/.verification/chain`. That directory now also holds
  `WindowAutomaton7Defs`, `DirectionWindowBridge7` and `AggregateDirection7Conditional` (new
  `.olean` files, compiled by the `chain_audit.py` invocation; no existing `.olean` was touched).
  Inside `work/final_lean` the closure of the shards is the data module and the shards only.
- **Driver.** `../lean/scripts/build_shards7.sh` (detached, `nohup`), in batches:
  `shard_build7.py prepare --limit BATCH` places the next sources, `shard_build7.py stale` checks
  that only `WindowAutomaton7B234*` modules would be built (simulation with `closure()`/`uptodate()`
  of `guarded_lake_build.py`), then the guarded build runs at `nice -n 10` with `--heavy-jobs`
  from `work/final_lean/.lake/b234/heavy_jobs` (3), `--rss-cap-gb 2.5`, `--min-free-gb 4` and
  `--min-disk-mb 254` (no new batch is prepared below 258 MB; the driver then waits). The batch size is read from `work/final_lean/.lake/b234/batch` before each
  batch.
- **Sweeper.** `shard_build7.py sweep` (detached) deletes the source of every module the guarded log
  reports built, after checking it against the manifest `../lean/data/shards7_B234.sha256`
  (sha256 of the data module and of the 792 shards). `prepare` regenerates them byte for byte and
  gives them the fixed mtime 2026-10-29 00:00 UTC, so a regenerated source never makes a built
  `.olean` stale. The sweeper also pauses the build (SIGSTOP by PID to the driver and its
  descendants) below 250 MB of free disk, resumes it at 260 MB, and writes
  `work/final_lean/.lake/b234/status.json`.
- **Files** (all under `work/final_lean/.lake/b234/`, not committed): `build.pid` (driver),
  `sweep.pid`, `build.log`, `sweep.log`, `guarded.jsonl` (one line per module), `guarded_logs/`,
  `status.json`.
- **Resume.** Start the driver and the sweeper again with the commands below; modules with an
  `.olean` are skipped (`prepare` places only missing ones, `--trust-mtime`).
- **Stop.** `kill $(cat work/final_lean/.lake/b234/build.pid)`, then the `lean` processes listed by
  `ps --ppid <guarded_lake_build PID>` by PID; then `kill $(cat work/final_lean/.lake/b234/sweep.pid)`.

```sh
cd /home/user/Snake-in-the-box-in-9
W=work/final_lean/.lake/b234
nohup milestones/25-k7-234/lean/scripts/build_shards7.sh > $W/build.log 2>&1 & echo $! > $W/build.pid
nohup python3 milestones/25-k7-234/lean/scripts/shard_build7.py sweep --tag B234 \
    --manifest milestones/25-k7-234/lean/data/shards7_B234.sha256 --log $W/guarded.jsonl \
    --pid-file $W/build.pid --status $W/status.json --floor-mb 250 > $W/sweep.log 2>&1 & echo $! > $W/sweep.pid
python3 milestones/25-k7-234/lean/scripts/shard_build7.py status --tag B234 --log $W/guarded.jsonl
```

## Log

| time (UTC) | event | shards built | free disk |
|---|---|---|---|
| 31 Oct 06:40–06:43 | `WindowAutomaton7Defs`, `DirectionWindowBridge7`, `AggregateDirection7Conditional` compiled into `work/spectral/.verification/chain` | — | 385 MB |
| 31 Oct 06:45 | manifest written (793 sources); staleness simulation: 11 modules in the closure, all `WindowAutomaton7B234*`, nothing outside the tag | — | 360 MB |
| 31 Oct 06:46 | `WindowAutomaton7B234Data` built (74.8 s, 0.63 GB, 20.9 MB `.olean`); its source deleted (sha256 checked) | 0 | 360 MB |
| 31 Oct 06:47 | first batch (10 shards), 2 heavy jobs next to the scratch composition test | 0 | 359 MB |
| 31 Oct 06:57 | shards (0, 1), (0, 2): 611–615 s, 1.19–1.20 GB, 217,176 B `.olean` + 92,895 B `.ilean` (146 `decide`s each, model: 218 kB) | 2 | 383 MB |
| 31 Oct 07:00 | restarted with `--no-ilean` (the 3 `.ilean` files written so far deleted), then with the driver waiting for disk instead of exiting | 2 | 379 MB |
| 31 Oct 07:12 | shards (0, 3)…(0, 6): 622–656 s, 1.17–1.25 GB | 6 | 377 MB |
| 31 Oct 07:20 | scratch of the composition test deleted (45 MB) | 6 | 430 MB |
| 31 Oct 07:29 | restarted with 3 heavy jobs and disk thresholds 254 MB (start) / 258 MB (prepare); batches of 48 | 6 | 428 MB |

**Projection** (31 Oct 07:30): mean 629 s per shard so far (the 4-shard fit of `../lean/README.md`
gives 159 CPU-hours for all 792, mean 12 min). With 3 jobs, about 53 hours of wall time, so the end
is around 2 November 13:00 UTC if the disk lasts. Disk: about 167 MB of shard `.olean` in all
(211 kB on average), against about 175 MB above the 254 MB start threshold. It should just fit;
otherwise the driver waits at the last batches (`status.json` says `paused`/how many are built).

| time (UTC) | event | shards built | free disk |
|---|---|---|---|
| 31 Oct 08:02 | 33 minutes stable at 3 jobs, no failure: (100, 1…6) 274–289 s, (101, 1…6) 705–723 s, at most 1.25 GB; 18 shard `.olean` files, 3.64 MB (202 kB each); sources of built shards deleted by the sweeper | 18 | 426 MB |

Remaining disk check at 08:02: 774 shards × about 211 kB ≈ 163 MB, against 426 − 254 = 172 MB. The
build should end at about 263 MB free, with about 9 MB to spare above the start threshold.
