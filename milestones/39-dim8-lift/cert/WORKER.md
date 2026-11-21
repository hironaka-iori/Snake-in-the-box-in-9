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
