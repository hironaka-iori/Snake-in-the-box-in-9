# Certificates of the unconditional 233: progress log

Resumable log of the certificate run for the two premises `AllRefuted6SB233` and
`AllRefutedShare6SB233` of `Snake9.Floors233Port.upper_233_of_certs6SB233`. Driver:
`milestones/33-233-lean/certify/cert233.py` (see its docstring). Scratch: `/home/user/cert233work`
(not in the repository; set `CERT233_SCR` to change it).

## How to resume (after a container restart)

1. `pgrep -af cert233.py`. If nothing runs, restart the step that was running (each step skips
   finished keys):

   ```sh
   cd milestones/33-233-lean/certify
   export CERT233_SCR=/home/user/cert233work
   # cores (phase 2), two shards at nice 10:
   for i in 0 1; do setsid nohup nice -n 10 python3 cert233.py cores --shard $i/2 --min-disk-mb 1200 \
       >> $CERT233_SCR/logs/cores$i.log 2>&1 & done
   python3 cert233.py status
   ```

   A shard writes one gzipped core JSON per key into
   `milestones/10-window-aggregate/data/lean_core_direction_6s/` and a line per key into
   `_progress<i>.jsonl` there; a key interrupted mid-run has no JSON and is redone.
2. Kill only by PID (`$CERT233_SCR/*.pid`).

## Log

- 11:27 UTC: start. Disk 3.8 GB free; the migration agent runs 2 `lean` processes.
- 11:33: libraries built in the core lib (`guarded_lake_build.py --direct --trust-mtime --no-ilean`;
  the staleness simulation listed only the 5 new libraries): `LocalWindowCnfPack`,
  `LocalWindowTagsW`, `LocalWindowTagsSW`, `LocalWindowFamilies`, `LocalWindowDirGlue7`.
  `LocalWindowTagsShare.olean` and `LocalWindowTagsSharePacked.olean` were copied (`cp -p`) from the
  floors port (`/home/user/floors233`), so the share modules and `Floors233Main` see the same files.
- 11:45: phase 1 done (validation sample `certify/data/sample233.json`: 18 plain keys giving 6 seeds
  and 12 L1 keys, 2 H8 keys giving 1 seed and 1 L1 key, 2 share thresholds, 5 reused keys). Every
  module compiled in scratch with `lean -o`; `allRefutedMini6SB233` and `allRefutedShareMini6SB233`
  depend on `propext`, `Classical.choice`, `Quot.sound`. Details in `certify/README.md`.
- 11:46: phase 2 (cores) started: 2 shards, PIDs 14294 and 14295.
- 11:58: `prod233.py --kinds share --once` tested on the first 9 share thresholds (core shard 1 paused
  by SIGSTOP meanwhile): staleness simulation 29 modules, only the 18 new ones stale; built 18/18 in
  92 s with one job (share Cnf 4-17 s, 0.65-1.33 GB; replays 0.8-2.8 s, under 0.62 GB); 18 sources swept.
- 14:35: plain/H8 cores done (5,673). `plan`: 2,637 seeds (2,098 widened), 2,613 keys by L1 and
  423 by L2 (80 s); `data/seeds6SB233.json.gz`. `final` written (30 modules, merge orders checked).
- 14:42: built `LocalWindowDirKeysN6SB233` (43 s), `LocalWindowDirKeysR6SB233`, and
  `LocalWindowDirUnsatR6SB233` (the 1,383 reused keys; 53 s, 3.28 GB); staleness simulation of the
  43,484-module closure: only these 3 stale.
- 14:45: production started: `prod233.py --jobs 1 --batch-hints 3e7` (PID in `$CERT233_SCR/prod.pid`);
  jobs 2 once the last share cores finish. Resume: rerun the same command (it skips built modules).
- 15:00-17:12: production ran (jobs 2) until a container restart (usage-limit pause); state at
  restart: 632 seed and 16 share certificates built (Cnf + replay), no `.olean` without an `ok`
  record in `.lake/guarded_build_233cert.jsonl`.
- 17:16: production restarted, `prod233.py --jobs 2 --batch-hints 3e7`.
- 18:05: batch 3 (334 certificates) built 332; two share Cnf modules with caps 99 and 107 hit the
  6.5 GB cap. Probe: the last clause part (the cap-totalizer clauses, 4,000 literals) took 5.9 GB.
  Fix: share modules with cap ≥ 24 use parts of 1,000 literals (500 from cap 60); cap 99 then
  compiles in 82 s at 3.43 GB. Production restarted (PID in `prod.pid`).
- 19:00: batch 4 (159 certificates, 22.9 M replay hints): generation 925 s (the 8 x 5 proofs of the
  53 cores above 200 k hints took 644 s of it, for about 12 % fewer hints), build 2,104 s wall
  (replays 2,761 s = 0.12 ms/hint; Cnf 1,410 s). The 8 x 5 portfolio now only from 5 M hints
  (`replay --big 5e6`). Remaining: 1,988 certificates, 6.15 G full-proof hints (estimate; replay
  hints are 0.7-0.8 of it so far).
- 19:40: state: 1,252 of 3,118 certificates built (1,150 seeds of 2,637, 102 share keys of 490):
  82.4 M replay hints (0.76 of their full-proof estimate), replay `.olean` 219 MB (2.66 B/hint),
  Cnf `.olean` 108 MB (87 kB each). Batch 5 (113 certificates): generation 289 s, build 1,707 s.
  Production keeps running (`prod233.py`, PID in `$CERT233_SCR/prod.pid`).
- 22:07: production relaunched after a container restart (`prod233.py --jobs 2 --batch-hints 3e7`).
- 22:20: fix of the one failed module, `LocalWindowUnsat.T012345A36236K87` (batch of 91, "Stack
  overflow detected"). Compiling each `ok<c>` alone: only `ok2` overflows (the main theorem and
  the Cnf/Sat module are fine; `--max-lemmas 2000` does not help). Cause: the kernel caches
  `drop64R raw (b + 1)` only within one declaration, and the first lookup of block `b` forces
  every block from the highest one already evaluated up to `b` recursively; segment 2 jumps by
  138 blocks (8,800 input clauses) at once (the passing segments: at most 79). Fix:
  `gen_lean_lrat_v3.py --warm N` (default 0, so the migration is unchanged): for a segment that
  jumps by more than N blocks into `raw` or an earlier segment's lemma list, `warm<c> : andB W
  (check ...) = true` by `decide +kernel`, where `W` evaluates every N-th block in increasing order
  (`seqN (headR OFF (nthR raw 64k)) true`), and `ok<c>` is the same statement as before, by
  `(andB_eq_true warm<c>).2`. `cert233.py replay` passes `--warm 32`. The module (same LRAT,
  238,843 hints) compiles in 49 s. `prod233.py` now deletes and regenerates the source of a module
  whose last guarded build failed after the source was written, keeps running after a batch with
  at most 20 unbuilt modules, and leaves a module that failed twice out of the rest of the run.
  No other failure in `prod6SB233.jsonl` or `.lake/guarded_build_233cert.jsonl` (the two share Cnf
  modules killed at the RSS cap on 18:05 are built). State: 1,345 of 3,118 certificates (1,227
  seeds, 118 share keys).

## Projection (measured rates)

- Remaining: 1,866 certificates, 6.1 G full-proof hints, so about 4.6 G replay hints at 0.76.
- Kernel: 0.12 ms/hint for the replays plus the Cnf modules: about 160-190 CPU-hours, i.e. about
  80-95 h of wall time on 2 cores (milestone 31 projected 3.0 G hints; the `--unsat` cores used here
  give longer proofs than its best-of-two cores).
- Disk: about 12 GB more of `.olean` (2.66 B/hint) against about 8 GB free now; `prod233.py` waits
  for space (reserve 1.4 GB).
- Then: `cert233.py final` (already written once; rerun to refresh), build
  `LocalWindowDirUnsat6SB233` and `LocalWindowShareUnsat6SB233` with the guarded build, rebuild the
  floors overlay (`scripts/floors_overlay.py /home/user/floors233/.lake/build/lib/lean NEWDIR`, since
  the overlay must list the new `LocalWindowCnf`/`LocalWindowUnsat` files), and run
  `chain_audit.py --target UpperBound233 --reuse --extra-lean-path NEWDIR --log outputs/upper-bound-233-audit-linux.log --axioms Snake9.upper_bound_233 Snake9.verified_interval_191_233`.
- 2026-11-11 07:51 UTC check-in: 1,909 / 3,118 certificate modules built, production and migration both running, 9.2 GB free.
- 2026-11-11 08:53 UTC check-in: 1,996 / 3,118 certificate modules built, production and migration both running, 9.4 GB free.
- 2026-11-11 09:56 UTC check-in: 2073 / 3,118 certificate modules built, production and migration both running, 7.5 GB free.
- 2026-11-11 10:58 UTC check-in: 2139 / 3,118 certificate modules built, 8.4 GB free.
- 2026-11-11 12:00 UTC check-in: 2199 / 3,118 certificate modules built, 10.0 GB free.
- 2026-11-11 13:02 UTC check-in: 2251 / 3,118 certificate modules built, 9.9 GB free.
- 2026-11-11 14:05 UTC check-in: 2299 / 3,118 certificate modules built, 9.8 GB free.
- 2026-11-11 15:08 UTC check-in: 2347 / 3,118 certificate modules built, 9.7 GB free.
- 2026-11-11 16:12 UTC check-in: 2385 / 3,118 certificate modules built, 9.6 GB free.
- 2026-11-11 17:14 UTC check-in: 2423 / 3,118 certificate modules built, 9.5 GB free (migration finished at 16:12).
- 2026-11-11 18:15 UTC check-in: 2456 / 3,118 certificate modules built, 9.4 GB free.
- 2026-11-11 19:16 UTC check-in: 2489 / 3,118 certificate modules built, 9.3 GB free.
- 2026-11-11 20:17 UTC check-in: 2517 / 3,118 certificate modules built, 9.2 GB free.
- 2026-11-11 21:18 UTC check-in: 2545 / 3,118 certificate modules built, 9.1 GB free.
- 2026-11-11 22:20 UTC check-in: 2571 / 3,118 certificate modules built, 9.0 GB free.
- 2026-11-11 23:22 UTC check-in: 2597 / 3,118 certificate modules built, 8.9 GB free.
- 2026-11-12 00:23 UTC check-in: 2620 / 3,118 certificate modules built, 8.8 GB free.
- 2026-11-12 01:25 UTC check-in: 2639 / 3,118 certificate modules built, 8.7 GB free.
- 2026-11-12 02:29 UTC check-in: 2659 / 3,118 certificate modules built, 8.6 GB free.
- 2026-11-12 03:30 UTC check-in: 2677 / 3,118 certificate modules built, 8.5 GB free.
- 2026-11-12 04:32 UTC check-in: 2698 / 3,118 certificate modules built, 8.6 GB free.
- 2026-11-12 05:38 UTC check-in: 2716 / 3,118 certificate modules built, 8.3 GB free.
- 2026-11-12 06:40 UTC check-in: 2732 / 3,118 certificate modules built, 8.1 GB free. Production restarted with `--jobs 4 --batch-hints 6e7` (the replay migration no longer uses the cores; driver of c06694bc: regenerate sources of failed modules, tolerate up to 20 failed modules per batch). The final chunks `LocalWindowDirUnsatN6SB233_10`..`_13` (all their certificates present) were built early: 7-15 s and 0.5 GB each.
- 2026-11-12 07:23 UTC check-in: 2747 / 3,118 certificate modules built, 8.0 GB free. First 4-job batch: 15 modules (58 M hints) in 267 s generation + 1,647 s build, no failure; 4 lean jobs at 1.4-1.7 GB each, 8 GB memory available.
- 2026-11-12 08:24 UTC check-in: 2775 / 3,118 certificate modules built, 7.9 GB free (about 28 modules an hour on 4 jobs; batches of 14-15 modules, 270-470 s generation + 1,700 s build, no failure).
- 2026-11-12 09:26 UTC check-in: 2797 / 3,118 certificate modules built, 7.7 GB free (22 in the last hour: the remaining modules are larger, about 4 M hints each; no failure; 7 GB memory available during builds).
- 2026-11-12 10:28 UTC check-in: 2814 / 3,118 certificate modules built, 7.6 GB free (17 in the last hour; batches of 12-13 modules, about 4.5 M hints each; no failure).
- 2026-11-12 11:30 UTC check-in: 2825 / 3,118 certificate modules built, 7.5 GB free (11 in the last hour: a 12-module batch of 58 M hints took 501 s generation + 2,001 s build; no failure).
- 2026-11-12 12:45 UTC check-in: 2836 / 3,118 certificate modules built, 7.5 GB free. The generation phase is now the bottleneck: the last batch spent 3,645 s generating (cadical 8 seeds x 5 rounds per core of at least 5 M hints, serial) against 1,545 s building. `pregen233.py` (two workers, own scratch directories, claims by O_EXCL files) now generates sources ahead of prod, outside the batch prod is generating or building, and moves each into `work/final_lean/LocalWindowUnsat` unless prod got there first.
- 2026-11-12 13:05 UTC: third pre-generator (`--worker 2`) started; the first two moved 8 sources in 27 min, none failed or dropped. Remaining: 282 certificates, about 1.7 GB of `.olean` against 7.2 GB free.
- 2026-11-12 13:26 UTC check-in: 2836 / 3,118 certificate modules built, 7.0 GB free. Prod's current batch generated its own sources (started before the pre-generators, about 68 min) and is now building; 16 sources are pre-generated for the next batches (none failed). Load 6.6 on 4 cores (4 lean + 3 generators), 8 GB memory available.
- 2026-11-12 14:29 UTC check-in: 2850 / 3,118 certificate modules built, 6.9 GB free. The pre-generators work: prod's current batch spent about 13 s generating (all 11 sources pre-generated) against 4,088 s for the previous one. Builds are slower under the shared CPU (2,660 s for the previous batch); 30 sources pre-generated so far, none failed; 4 GB memory available.
- 2026-11-12 15:18 UTC: 2861 / 3,118 certificate modules built, 6.7 GB free. The last batch spent 11 s generating and 2,958 s building (11 modules: about 13 an hour). Pre-generation ran ahead of the builds (41 sources moved, about 19 waiting) and the shared CPU slowed the builds while only 3 GB memory was left, so worker 2 was stopped (by PID; its unfinished claim removed). Two workers remain.
- 2026-11-12 15:30 UTC check-in: 2865 / 3,118 certificate modules built, 6.7 GB free, 6 GB memory available with two pre-generators.
- 2026-11-12 16:31 UTC check-in: 2878 / 3,118 certificate modules built, 6.7 GB free. Batches of 10 modules in 11 s generation + 2,320-2,400 s build (about 15 an hour); no failure; 3 GB memory available.
- 2026-11-12 17:32 UTC check-in: 2895 / 3,118 certificate modules built, 6.7 GB free. Batches of 10 in 11 s generation + 2,320-2,480 s build; no failure; 6 GB memory available.
- 2026-11-12 18:36 UTC check-in: 2908 / 3,118 certificate modules built, 6.6 GB free; gen_s 10 s, no failure, 4 GB memory available. (17:34: an unscoped `git pull` fetched all branches, 3.9 GB pack, removed after fsck; remote.origin.fetch now limited to this branch.)
- 2026-11-12 19:38 UTC check-in: 2924 / 3,118 certificate modules built, 6.6 GB free; batches of 8-9 modules in 2,095-2,379 s, gen_s 9-10 s, no failure.
- 2026-11-12 20:33 UTC: container restart (2935 built at the time); relaunched `prod233.py --jobs 4 --batch-hints 6e7` (PID 396) and pregen workers 0/1 after clearing the 97 pre-generator claims.
- 2026-11-12 20:40 UTC check-in: 2935 / 3,118 built, 6.4 GB free; prod generating its first batch itself after the restart; pregen worker 2 restarted while no build runs (12 GB available).
- 2026-11-12 21:46 UTC check-in: 2943 / 3,118 built, 6.2 GB free; first post-restart batch: 8 modules, gen_s 521, build_s 3,017 (slowed by three pre-generators); pregen worker 2 stopped again (2 GB available).
- 2026-11-12 22:48 UTC check-in: 2955 / 3,118 built, 6.1 GB free; last batch 8 modules, gen_s 9, build_s 2,618; no failure; 4 GB available.
- 2026-11-12 23:50 UTC check-in: 2965 / 3,118 built, 6.0 GB free; batches of 7-8 modules in 2,300-2,860 s, gen_s 8-9 s; no failure.
- 2026-11-13 00:35 UTC: correction: the certificate total is 3,127 (`cert233.py status`: 2,637 seeds + 490 share), not 3,118 as written in earlier lines; production always worked from the full list. Now 2,971 / 3,127 built (2,537 seed + 434 share).
- 00:50: post-production prepared as `certify/post233.sh` (not run yet). It fixes two errors in the plan above: `chain_audit.py` needs `--mathlib-dir /home/user/lean-deps/mathlib4`, and the overlay must drop its links to LocalWindowTagsShare(Packed).olean (byte-identical separate copies in the core lib, else chain_audit stops with 'would shadow').
- 01:00: remaining-work estimate (read-only analysis of work_items and the build logs): the 157 remaining
  certificates hold 2.85 G estimated hints (all 2,978 built so far: 3.44 G), up to 77.6 M per module
  (largest built: 8.7 M). Expected about 140-165 h more at the old settings; generation (cadical,
  ~est^1.43, up to ~6 h per module) becomes the bottleneck, batches shrink to 1 module above 3e7.
  Actions: production restarted at a batch boundary with `--batch-hints 1.2e8` (PID 8129); stale
  `$CERT233_SCR/pregen2` scratch (177 MB) removed. Planned: before free disk nears 3000 MB, restart the
  pregens with `--min-disk-mb 2300` (they exit, not wait, below their floor); before the six largest
  modules (from S012301A34354, 47 M est. hints; predicted RSS up to ~9 GB), restart prod with
  `--rss-cap-gb 11` (they would otherwise be killed at 6.5 GB, deterministically, twice).
- 00:55: the 1.2e8 batch (13 modules) held 7 without a pregenerated source, so prod generated them
  serially with the build cores idle (and pregen had dropped two of them, S0123104A435535 and
  T012034A46335K59, as "prod got there first", leaving their claims). Stopped prod (8129) and its
  replay; started pregen workers 2 and 3; `$CERT233_SCR/waitbatch.sh` relaunches prod once the 13 sources
  exist and then stops workers 2/3. Lesson: change --batch-hints only when the pregenerated buffer
  covers the new batch.
- 01:16: `supervisor233.py` started (log `$CERT233_SCR/logs/supervisor.log`): adds pregen workers when lean builds + replays use fewer than 4 cores (MemAvailable >= 4 GB), retires them above 5, kills one below 1.2 GB; swaps the old workers for the new pregen233.py (helps prod's current replay from the end of its list, never drops a source, stop file) at their next item boundary.
- 01:25: parallel seeds: `gen_lean_core.best_cadical_proof(..., jobs=)` runs a round's portfolio configurations in parallel and picks the same proof (first, in portfolio order, with the fewest hints; checked identical byte for byte on PHP(8,7), 8 seeds x 3 rounds, jobs 1 vs 4); default unchanged (serial). `cert233.py replay --seed-jobs auto` uses idle cores (limited by disk, 15 B/est. hint per run, and memory, 70 B/est. hint per run); pregen233.py passes it through; supervisor233.py (restarted) starts workers with it and counts each cadical process as a core.
- 01:30: Lean multithreading (`Elab.async`, `-j`) considered and rejected: the generator sets `Elab.async false` on purpose (kernel caches live per declaration; parallel declarations multiply peak memory, the binding limit for the largest modules), it may defeat the warm-up declarations, and idle cores are now used for generation anyway.
- 01:27: waitbatch fired at 01:26: prod relaunched (PID 13258; the waiter's PID file was empty because setsid inside a script does not fork, fixed by hand), building the 13-module batch. supervisor233.py fixed (pool children of a --seed-jobs replay were counted as separate replays, which retired worker 0 by mistake; stop request withdrawn) and restarted.
- 2026-11-13 01:40 UTC check-in: 2972 / 3,127 built, 5.3 GB free; prod building the 13-module batch (4 lean), 2 pregen workers (new code), 3 GB available; no stale claim.
- 02:42 UTC: 2,985 / 3,127 built, 5.1 GB free, MemAvailable 10.9 GB. Batch 13 (13 modules, 1.14e8 est. hints) done at 02:24: gen_s 5, build 3,509 s, 0 failed. Batch 14 (13 modules): 9 sources were pregenerated; prod's replay generates S0123014A444435 itself, workers 0/1/2 are on the other three. Supervisor: 3 workers, busy 5, no thrash. No stale claims.
- 03:44 UTC: 2,991 / 3,127 built, 5.2 GB free, MemAvailable 5.4 GB. Batch 14 build started about 02:50 (gen about 26 min while the missing sources were made), 4 lean jobs running. Supervisor: worker 2 was started and retired twice (03:00 and 03:12), because `--seed-jobs auto` replays briefly run up to 10 cadicals; mild, left as is. 2 workers, pregen logs clean, no stale claims.
- 04:46 UTC: 2,998 / 3,127 built (129 left, 2.60 G est. hints), 4.9 GB free, MemAvailable 10.3 GB. Batch 14: gen 1,555 s, build 5,829 s, 0 failed. Batch 15 started its guarded build at 04:46 (sources ready). Worker 2 start/retire repeats about every 20 min (03:00, 03:12, 04:17, 04:39); harmless churn, left as is. No stale claims, pregen logs clean. S012301A34354 (first of the six large-RSS modules) is about 120 modules away.
- 05:49 UTC: 3,005 / 3,127 built, 5.0 GB free. Batch 15 still building (4 lean jobs at 2.1-2.5 GB RSS each, started 04:46). MemAvailable is low at 2.1 GB (4 lean + 2 worker replays). There are no OOM kills in dmesg, and earlier batches with the same mix peaked below 3 GB per lean, so this is left as is but watched. No stale claims, pregen logs clean, no supervisor churn since 04:39.
- 06:52 UTC: 3,009 / 3,127 built, 4.8 GB free. Batch 15 (12 modules): 11 ok, 1 lost to the cgroup OOM killer (T012034A36435K55, lean at 3.1 GB anon RSS, dmesg 34241 s), so prod queued it for regeneration (one of its two attempts is used). Cause: 4 lean jobs plus 2 worker replays, and the supervisor's memory kill rule could not fire because it requires more than --min-workers (2) workers. Fix: restarted supervisor233.py with `--min-workers 1 --kill-mem-gb 1.5` (PID 8797). Workers 0/1 count as legacy for it and are swapped at their next item boundary. Batch 16 is building (4 lean jobs), MemAvailable 7.7 GB.
- 07:56 UTC: 3,017 / 3,127 built, 4.8 GB free, MemAvailable 4.7 GB. T012034A36435K55 (the OOM loss) rebuilt fine on its second attempt. No new OOM kill. The new supervisor stopped legacy workers 1 (07:27) and 0 (07:40) at item boundaries. It started worker 0 again only at 07:52, because its start rule needs MemAvailable >= 4 GB, so pregeneration ran with 0 workers for about 12 min. Now: 3 lean jobs, 1 worker, no stale claims, pregen logs clean.
- 08:59 UTC: 3,024 / 3,127 built, 4.5 GB free, MemAvailable 6.8 GB. Batch 16 (11 modules): gen 1,242 s, build 5,092 s, 0 failed. Batch 17 has been building since about 08:13 (4 lean jobs). No new OOM. The supervisor keeps 1-2 workers during builds (it retires down to 1 when busy > 5). Cores stay full, so --start-mem-gb is left at 4. No stale claims, pregen logs clean.
- 10:06 UTC: 3,029 / 3,127 built, 4.1 GB free. Batch 17: 9 ok, 1 more OOM loss (T012301A24643K15, lean at 2.7 GB anon RSS, dmesg 46615 s). Prod requeued it in batch 18, which is generating now. Root cause: the memory cgroup of these processes has a 13.35 GiB limit (memory.limit_in_bytes 14337294336, failcnt in the millions), below the 16 GB that MemAvailable reflects, so the supervisor overestimated headroom by about 2.7 GB. Fix: `mem_avail_gb()` in supervisor233.py and cert233.py (for `--seed-jobs auto`) now returns min(MemAvailable, cgroup limit − usage + inactive_file). Supervisor restarted as PID 1594 with `--min-workers 1 --kill-mem-gb 2.0`. The six large-RSS modules must be planned against 13.35 GiB, not 16 GB: --jobs 2 at most, and no workers while one of them builds.
- 10:39 UTC: the container restarted (uptime 0). 3,029 / 3,127 built, 5.2 GB free after cleanup. Cleared 101 claims, the stop file and leftover scratch in $CERT233_SCR/{pregen*,}/replay. Relaunched prod (PID 286, same args); its guarded build started at once (batch 18 sources were ready), with T012301A24643K15 retried and the in-memory failure count reset. Then the supervisor (PID 323, `--min-workers 1 --kill-mem-gb 2.0`), which started worker 0. The memory cgroup path changed with the restart (the limit is still 14337294336 B); mem_avail_gb() reads it from /proc/self/cgroup.
- 2026-11-13 11:43 UTC: 3,037 / 3,127 built, 4.6 GB free. Batch 18 guarded build running since 10:39 (T012301A24643K15 still compiling, no OOM kill so far; cgroup at its limit with page reclaim). Supervisor PID 323 with worker 0.
- 2026-11-13 12:48 UTC: 3,042 / 3,127 built, 4.7 GB free. Batch 18 done 25/25 in 4,943 s, 0 failed (T012301A24643K15 built, peak RSS 3.47 GB). Batch 19 building; no OOM kills. 85 left (2.11 G est. hints), 79 of them before idx 151.
- 2026-11-13 14:31 UTC: 3,049 / 3,127 built, 4.4 GB free. Batch 19 done 27/27 in 4,067 s, 0 failed; next batch building; no OOM kills. (The 13:50 check-in did not fire; re-armed.)
- 2026-11-13 16:00 UTC: speed-up: replay-source generation for 58 of the remaining modules moved to three cloud sessions (xfer233.py gen; worker lists are round-robin in prod order; local claims written so pregen233 skips them). They push each gzipped source to a throwaway branch xfer/233/<name>; a local daemon (xfer233.py pull, log logs/xfer_pull.log) materialises them just in time (at most 14 unbuilt sources ahead, disk floor 2.3 GB) and deletes the branch. The kernel checks every source again when it is built here, so nothing generated remotely is trusted. The local 4 cores now go almost entirely to Lean builds (~97 core-h left).
- 2026-11-13 17:00 UTC: 3,060 / 3,127 built, 4.3 GB free. Remote generation works and is fast (16 sources pushed in the first hour, 6-17 min each on 4 cores). The pull daemon died at 16:03 because this session's git proxy refuses branch deletion (HTTP 403); fixed (deletion best effort, consumed names in $CERT233_SCR/xfer_consumed) and restarted 16:59; it materialised the first sources at once. Leftover xfer/233/* branches to be removed at the end from a session that may delete them.
- 18:02 UTC: 3,067 / 3,127 built, 3.9 GB free, no OOM. Remote workers: 31 of 58 sources pushed, no failures; xfer pull materialised 14 so far (prod keeps ~14 ready, local build is now the bottleneck). prod, supervisor, pull daemon alive.
- 19:08 UTC: 3,072 / 3,127 built, 3.8 GB free, no OOM; last batch 25/25 ok (gen_s 8). Remote: 41 of 58 sources pushed, 17 materialised. All daemons alive.
- 20:15 UTC: 3,079 / 3,127 built, 3.5 GB free, no OOM; remote 49 of 58 pushed, 24 materialised. Built peaks follow pred_rss_pow (2.7-3.8 GB), well below pred_rss_lemlin. Guard script ($CERT233_SCR/bigsix_guard.sh) restarts prod with --jobs 2 --rss-cap-gb 11 and stops supervisor/pregen as soon as a batch includes one of the six largest modules.
- 21:00 UTC: container restart at about 20:45 stopped everything (3,080 built). Recovery: claims reset (47 remote names), replay scratch cleared; prod's reset_failed deleted the sources of the 3 interrupted modules, so they were un-consumed and re-fetched from their xfer branches instead of regenerated locally. Relaunched prod (PID 967, --jobs 4), xfer pull, big-six guard; supervisor/pregen not restarted (all remaining sources come from remote workers).
- 21:13 UTC: 3,080 / 3,127 built (batch of 5 running since 21:00), 3.7 GB free, no OOM; remote 53 of 58 pushed. prod 967, guard 979, pull 1026 alive.
- 22:00 UTC: second container restart at about 21:40 (3,083 built). Recovery is now scripted: $CERT233_SCR/recover233.sh (claims reset, scratch cleared, unbuilt sources touched so reset_failed keeps them, consumed-but-missing sources re-fetched from xfer branches, then prod --jobs 4 or --jobs 2 --rss-cap-gb 11 once the big six started, pull and guard). prod 911, pull 333, guard 923.
- 22:17 UTC: 3,083 / 3,127 built (4 modules building since 22:00, 2.5-3.4 GB each), 3.6 GB free, no OOM, no regeneration; remote 55 of 58 pushed. prod 911, guard 923, pull 333 alive.
