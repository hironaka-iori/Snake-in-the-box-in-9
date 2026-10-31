#!/bin/bash
# Detached production build of WindowAutomaton7<T>Data and the 792 shards in work/final_lean, in
# batches, on a small disk (see shard_build7.py).  Each batch: `prepare --limit BATCH` places the
# sources of the next modules without .olean, `stale` checks that only modules of the tag would be
# built, then guarded_lake_build.py --direct --trust-mtime builds them (nice 10, no .ilean, 3 heavy jobs,
# 2.5 GB RSS cap, 4 GB free memory to start one, no start below MIN_DISK_MB of free disk).
# `shard_build7.py sweep` (started next to it, see PROGRESS-B234.md) deletes the built sources and
# pauses the build below 250 MB of free disk.  Stops when every shard is built or when a build
# fails; while there is no disk for the next batch it waits (checking every 10 minutes).
#
#   echo 48 > work/final_lean/.lake/b234/batch       # shards per batch (read before each batch)
#   echo 3 > work/final_lean/.lake/b234/heavy_jobs   # parallel shards (read before each batch)
#   nohup milestones/25-k7-234/lean/scripts/build_shards7.sh > LOG 2>&1 & echo $! > PIDFILE
set -u
T=${T:-B234}
LAM=${LAM:-6423/1544}
KEYS=${KEYS:-milestones/25-k7-234/data/keys_best234.json.gz}
MIN_DISK_MB=${MIN_DISK_MB:-254}
PREP_DISK_MB=${PREP_DISK_MB:-258}
R=$(cd "$(dirname "$0")/../../../.." && pwd)
S=$R/milestones/25-k7-234/lean/scripts
W=$R/work/final_lean/.lake/b234
MAN=$R/milestones/25-k7-234/lean/data/shards7_$T.sha256
mkdir -p "$W"
export PATH=/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin:$PATH
export LEAN_PATH=$R/work/spectral/.verification/chain
cd "$R"
while :; do
  # the batch size can be changed while the build runs: echo N > $W/batch (and $W/heavy_jobs)
  BATCH=$(cat "$W/batch" 2>/dev/null || echo 48)
  HEAVY=$(cat "$W/heavy_jobs" 2>/dev/null || echo 3)
  echo "== $(date -u +%FT%TZ) batch: prepare (free $(df -m "$R" | awk 'NR==2{print $4}') MB)"
  nice -n 10 python3 "$S/shard_build7.py" prepare --keys "$KEYS" --tag "$T" --lam "$LAM" \
      --manifest "$MAN" --limit "$BATCH" --min-disk-mb "$PREP_DISK_MB"
  rc=$?
  [ $rc -eq 2 ] && { echo "== all modules of $T built"; exit 0; }
  if [ $rc -eq 3 ]; then
    # paused: no disk for the next batch; resumes by itself once space is freed
    echo "== $(date -u +%FT%TZ) paused: no disk for the next batch (retry every 10 minutes)"
    while [ "$(df -m "$R" | awk 'NR==2{print $4}')" -lt "$PREP_DISK_MB" ]; do sleep 600; done
    continue
  fi
  [ $rc -ne 0 ] && { echo "== prepare failed ($rc)"; exit 1; }
  python3 "$S/shard_build7.py" stale --tag "$T" || { echo "== staleness check failed"; exit 1; }
  targets=$(cd work/final_lean && ls WindowAutomaton7${T}Data.lean WindowAutomaton7${T}Shard*.lean 2>/dev/null | sed 's/\.lean$//')
  [ -z "$targets" ] && { echo "== nothing placed"; exit 1; }
  nice -n 10 python3 work/guarded_lake_build.py --direct --no-ilean --trust-mtime --lean "$(command -v lean)" \
      --jobs 1 --heavy-jobs "$HEAVY" --heavy "^WindowAutomaton7${T}Shard" --rss-cap-gb 2.5 --min-free-gb 4 \
      --min-disk-mb "$MIN_DISK_MB" --log "$W/guarded.jsonl" $targets \
      || { echo "== build failed"; exit 1; }
done
