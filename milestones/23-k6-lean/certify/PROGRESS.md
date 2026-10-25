# Progress of the 235 build (resume notes)

Plan: `README.md` in this directory. Scratch dir S = /tmp/claude-0/-home-user-Snake-in-the-box-in-9/9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad
(may be lost on container restart; every step resumes from the oleans with --trust-mtime).

PATH: export PATH=/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin:$PATH

## Log

- 2026-10-23: start. 3,545 MB free. Staleness simulation of LocalWindowDirSatK6 + LocalWindowDirGlue6K235:
  1,281 modules in closure, 1,275 stale, all new (635 Cnf K, 635 Sat K, Keys/Sat/Glue modules). No base module stale.
- Step 1 phase A: Cnf + Sat modules with source <= 95 kB (582 of 635), heavy-jobs 2, cap 6.5 GB,
  log work/final_lean/.lake/guarded_build_k6sat.jsonl. Phase B: the rest alone (heavy-jobs 1, cap 10).
- gen_k6_core.py final: LocalWindowDirUnsatK6 now uses one `refine` per window (was one giant ⟨…⟩); regenerated.
- Step 2 runs from a driver (scratch `driver.py`): replay_k6.py gen in 20 M-hint batches (at most 40 M pending),
  guarded builds (heavy-jobs 3, cap 6.5, min-free 6, log .lake/guarded_build_k6.jsonl) of the cases recorded in
  S/k6replay/replay_gen.jsonl, then `replay_k6.py sweep`; pauses everything below 400 MB free.
  Resume after a restart: rerun `replay_k6.py gen/build/sweep` as in README (all steps resume; gen skips cases whose
  main module exists; NOTE the record file replay_gen.jsonl lives in S and may be lost, the main modules are the truth).
- Step 4 (automaton without --provisional, chain, glue) started early, while step 1 runs.
- 2026-10-25 (resume): 635/635 Cnf, 592/635 Sat oleans; 495 replay cases generated (40.4 M hints), none built;
  2,806 MB free. Staleness simulation of LocalWindowDirSatK6 + Glue6K235: 44 stale (43 Sat K, LocalWindowDirSatK6), no base module.
  Step 1 phase B started (heavy-jobs 1, cap 10, log guarded_build_k6sat.jsonl). In parallel: chain_audit.py --reuse
  --target AggregateDirection6K235 (shards into work/spectral/.verification/chain; scratch log).
- Step 1 done: 1281/1281, 0 failed (43 Sat K at most 5.02 GB; LocalWindowDirSatK6 1,837 s, 2.10 GB).
- Step 2: scratch driver.py restarted (PID file in S/b235); first build of the 495 generated cases (40.4 M hints)
  started 04:38. Staleness simulation of those 495 roots: 4,147 in closure, 3,640 stale, all LocalWindowUnsat.K*.
- 2026-10-25 15:15 (resume after a container restart, down since about 06:18): 598 replay cases generated (121.7 M hints),
  565 built (81.4 M), 1,200 check modules ok so far (4.98 kernel-hours, at most 1.89 GB); 1,828 MB free.
  Staleness simulation of the 598 replay roots: 8,052 in closure, 1,931 stale, all LocalWindowUnsat.K* (33 unbuilt cases).
  Lesson: a concurrent sweeper deleted a Data source of a case whose build had restarted (Data olean already built),
  and guarded_lake_build.uptodate() then raised FileNotFoundError. Now the driver sweeps right BEFORE each build
  (swept modules are PREBUILT in the closure) and after it; no concurrent sweeper. Driver restarted with GEN_MIN_DISK=700.
  Chain prebuild (chain_audit.py --reuse --target AggregateDirection6K235) resumed at shard 17_3 (108 shards were done).
