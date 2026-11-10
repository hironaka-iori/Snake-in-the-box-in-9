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
