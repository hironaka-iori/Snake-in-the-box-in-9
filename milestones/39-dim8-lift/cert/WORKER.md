# Level-116 farm worker (milestone 39)

A farm session is given a share list `INDEX` (for example `12-15`) of `WORKERS=200` shares by the
coordinating session. It runs exactly this, from the repository root:

    git fetch origin research/unconditional-241 && git checkout -B research/unconditional-241 FETCH_HEAD
    INDEX=<list> WORKERS=200 bash milestones/39-dim8-lift/cert/d8_machine.sh

The script installs what is missing, builds the stacks (about 10 minutes), and starts
`prod_d8.py run --publish`, which pushes finished public `.olean` files and `manifest.jsonl` to
`refs/heads/xfer/d8/w<first index>` only. Logs: `~/d8.log`, `~/d8_setup.log`.

Keep-alive (cheap): a tracked background Bash wait (run_in_background, timeout 7000000) of

    timeout 6600 bash -c 'while pgrep -f "[p]rod_d8.py run" >/dev/null; do sleep 120; done'; date; tail -3 ~/d8.log; uptime -s

When it ends: if `prod_d8.py run` is no longer running and `~/d8.log` does not end with
`worker finished`, the container was restarted; rerun the two lines above (the run resumes). Then
re-arm the same wait. Keep turns short; no progress reports.

Report to the coordinating session (send_message) only: a `SAT?` record, the publish failing
(`publish failed` in the log), a build failing twice, or `worker finished` with the final counts
(`python3 milestones/39-dim8-lift/cert/prod_d8.py status --work ~/d8work`). Do not edit code, do not
push anywhere else, stop only when the coordinating session says so (`touch ~/d8work/STOP`, kill by PID).

## Code update (when the coordinating session says "update to <commit>")

Kill the worker and its children by PID (`pgrep -f "[p]rod_d8.py run"`, `pgrep -f "[m]ake_cert.py"`,
`pgrep -f "[b]uild_cert.sh"`, `pgrep -f "[l]ean.*--root"`, `pgrep -f "[p]ilot.py"`, `pgrep -x cadical`;
`kill` those PIDs, then check that `pgrep -x cadical` and `pgrep -f "[l]ean.*--root"` print nothing),
then rerun the two lines at the top. Orphans left by an earlier update (parent PID 1, e.g.
`ps -o pid,ppid,etime,cmd -C cadical`) compete for the cores and write into the new run's job
directories: kill them too. Finished certificates are kept; failed and interrupted items are retried. The
built stacks in `~/d8stack` and the plain stack are reused (only rebuilt if missing).

## Tail mode (TOO_BIG cubes), after your cube share has finished

When the coordinating session gives you a tail share `T` (of `TW` tail shares), make sure no
`prod_d8.py run` is running, then from the repository root:

    git fetch origin research/unconditional-241 && git checkout -B research/unconditional-241 FETCH_HEAD
    MODE=tail INDEX=<T> WORKERS=<TW> bash milestones/39-dim8-lift/cert/d8_machine.sh

It certifies the TOO_BIG cubes of the published manifests by recursive vertex splitting (each piece small
enough for this machine) and pushes OK records and public .olean files to `refs/heads/xfer/d8/t<T>` only.
Log `~/d8tail.log`; it resumes after a restart (rerun the same two lines). Keep-alive as above, with
`[t]ail_d8.py run` in place of `[p]rod_d8.py run` and `~/d8tail.log`. Report to the coordinating session:
a `SAT?` record, the first OK or BUILD_FAILED/CHECK_FAILED record of a cube (with its log tail), and
`tail worker finished`.

The tail item list is read once, at start, from the manifests published then. So on `tail worker finished`
rerun the same two lines at once: the new run picks up TOO_BIG cubes published since. Keep rerunning until a
run starts with `0 cubes to do` twice in a row, then report and stay idle (keep-alive off).

A pre-assigned tail share (given while your cube share is still running) means: when `prod_d8.py` reports
`worker finished`, switch to tail mode with that `T` right away, without waiting for the coordinating session.

## Disk (tail mode)

* Flags: `--chain 2000000 --chain-solve 0 --chain-over 3000000` while free disk is >= 8 GB when a cube
  starts; below 8 GB, relaunch without `--chain` at the next cube boundary (never mid-cube).
* Below 2.5 GB free: `touch ~/d8tail/STOP` (the worker ends cleanly and resumes on rerun), then report.
* Standing permission: once your cube share (`prod_d8.py`, `~/d8work`) has finished and every OK record of
  `~/d8work/manifest.jsonl` is on your `refs/heads/xfer/d8/w<N>` (its .olean and manifest line, sha256
  matching), you may delete `~/d8work/jobs`. Never delete `~/d8tail`, a parked hard cube's state
  (`b229/PARKED.md`) or anything a running worker uses.
* A share is relaunched past a parked cube with `--skip A,A,...`.

## Cover mode (one cover certificate, then back to your previous job)

When the coordinating session gives you a cover item `X` (`c5` or a Q5 representative number) and a name `kN`:

1. Reach a boundary without losing work. Tail worker: wait until `~/d8tail.log` shows a new `cube ...` line,
   then kill tail_d8.py and its children by PID (as in "Code update"). Cube worker: `touch ~/d8work/STOP`
   and wait until prod_d8.py exits (running jobs finish; then `rm ~/d8work/STOP`).
2. From the repository root:

       git fetch origin research/unconditional-241 && git checkout -B research/unconditional-241 FETCH_HEAD
       bash milestones/39-dim8-lift/scripts/make_tables.sh
       nohup python3 milestones/39-dim8-lift/cert/cover_d8.py run --stack ~/d8stack --work ~/d8cover \
         --only X --mem-gb 12 --procs 2 --publish --name kN >> ~/d8cover.log 2>&1 &

   (make_tables.sh takes ~10 min; cover_d8.py ports Walk, WalkSplit and TabAll into ~/d8stack itself.)
   One cover is 4 leaves of ~1.7 h each, built one at a time: ~6-7 h. It resumes after a restart (same lines).
   Keep-alive as above with `[c]over_d8.py run` and `~/d8cover.log`.
3. Report to the coordinating session: the OK record (or SAT?, BUILD_FAILED, CHECK_FAILED, FAILED with log tail).
4. On `cover worker finished`: rerun your previous worker with its usual line (tail: MODE=tail ...; cube:
   INDEX=... d8_machine.sh). Both resume from their own state.
