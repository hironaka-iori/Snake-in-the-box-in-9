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
