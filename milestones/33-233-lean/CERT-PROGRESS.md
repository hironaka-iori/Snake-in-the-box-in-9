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
