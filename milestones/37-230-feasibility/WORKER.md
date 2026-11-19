# Worker instructions for the 230 farm (milestone 37)

You are a production worker machine for the Lean 4.35 proof of the unconditional bound 230 (repository hironaka-iori/Snake-in-the-box-in-9, branch research/unconditional-241). Your role, LAUNCH line, LOGFILE and PGREP pattern are given in the message that sent you here.

Authorisation (from the repository owner, relayed by the orchestrator session): "有任何需要许可的，你全部同意就好了。不需要经过我的批准。" and "不用得到我的允许，想到什么能提升效率的就直接做。" You are allowed to push ONLY to branches under refs/heads/xfer/c230*, which the tools below do automatically. Never push to main or to research/*; never open a PR; never delete branches; never run an unscoped `git fetch` or a plain `git pull` (the remote has hundreds of large branches) - fetch only research/unconditional-241 by name; kill processes only by PID; do not edit or commit repository files.

Setup and launch (run in the repository checkout, as one Bash call; setup takes a few minutes):
  cd ~/Snake-in-the-box-in-9 2>/dev/null || cd /home/user/Snake-in-the-box-in-9
  git fetch origin research/unconditional-241 && git checkout -B research/unconditional-241 FETCH_HEAD
  python3 lean435/tools/prod435.py setup
  export PROD435_ADAPTER=$PWD/lean435/tools/c230.py
  export PROD435_CERT="$PWD/lean435/tools/c230.py cert"
  export PROD435_PFX=refs/heads/xfer/c230/
  export C230_PLAN=$PWD/milestones/37-230-feasibility/data/c230plan.json.gz
  LAUNCH

Then keep this session alive and watch the job:
- Keep a background Bash keep-alive task running at all times (e.g. `while true; do sleep 240; date; tail -2 LOGFILE; done` with run_in_background and a long timeout), and re-arm it whenever it ends. Never end your turn while the job is running; if you must wait, wait inside Bash commands (e.g. `timeout 540 tail -f LOGFILE | grep -m1 -E "published|FAIL|rror|done|finished"` or sleep loops of at most 9 minutes) and check again.
- Every ~30 minutes: check the process is alive (`pgrep -f PGREP`), `tail -20 LOGFILE`, `free -g`.
- If the container restarted (process gone, log stopped growing, ~/l435 missing) or the job died without finishing: re-run the whole setup-and-launch block above (it resumes; published work is skipped). Do not delete anything under refs/heads/xfer/c230*.
- If the log says the job finished (no work left / time limit / all items done or published elsewhere), report and stop.
- Do not change the commands or flags. If something fails repeatedly in the same way (3 times), stop retrying and report the exact error lines.
Report at the end in one short message: role, items published (count from the log), anything that failed.

## Self check-ins (added 18 Nov 04:30 UTC; required)
Sessions that end their turn get their container reclaimed after a while, which kills the nohup job. So, in addition to the above:
- Right after launching (and after every check), arm ONE self check-in with the claude-code-remote `send_later` tool (delay_minutes 30, initiation own_followup), message: "Self check-in (230 farm): check the job per milestones/37-230-feasibility/WORKER.md (pgrep, tail the log); if it is not running and not finished, re-run the setup-and-launch block (it resumes); then arm the next 30-minute self check-in with send_later."
- Keep exactly one such check-in pending; when one fires, do the check, then arm the next. Stop arming only when the job has finished (no work left).
- Split machines must run commit >= 63f10efb of research/unconditional-241 (parts 2 at a time with a memory cap). If an older c230split.py is running, kill it by PID and relaunch after the fetch/checkout.

## Hold the turn open (added 18 Nov 06:00 UTC; overrides anything above that suggests ending the turn)
Observed: containers are restarted between turns (machine "up 0 min", job gone), so an idle session loses its job within ~30 min.
- NEVER end your turn while the job runs. Chain foreground Bash waits back to back, each at most ~9 minutes, e.g.
  `timeout 540 bash -c 'while pgrep -f "PGREP" >/dev/null; do sleep 60; done'; date; tail -3 LOGFILE; uptime`
  and immediately issue the next one. Every ~30 minutes also check free memory and that the log grows.
- If a wait shows the job gone (or uptime says the machine just booted), re-run the setup-and-launch block at once.
- Keep the 30-minute send_later self check-in as a safety net only (it brings you back if the turn does end).

## Relaunch for the scheduler fix 87fbd8e5 (18 Nov 11:30 UTC; owners and helpers only, NOT split machines)
Machines used ~1 of 4 cores (memory-budget fairness rule + over-predicted build memory). Fixed in 87fbd8e5. Do this once, in one Bash call where possible:
1. `ps -eo pid,etime,args | grep "[b]in/lean -R /root/l435/prod/jobs"` - OWNERS only: if a lean build has run > 90 min, first wait for that PID to exit (`while kill -0 PID; do sleep 60; done`, <= 9 min per Bash call, chained).
2. `P=$(pgrep -f "prod435.py (run|one)|/l435/prod/jobs/|c230.py cert|genv3stream" | tr '\n' ' '); [ -n "$P" ] && kill -9 $P; sleep 3`
3. `git fetch origin research/unconditional-241 && git checkout -B research/unconditional-241 FETCH_HEAD && git log --oneline -1`  (must be 87fbd8e5 or later)
4. `[ -f ~/l435/prod/core/LocalWindowShareCtx.olean ] || python3 lean435/tools/prod435.py setup`
5. the four exports (plus your C230_PLAN override if you are a share helper), then your LAUNCH line unchanged (>> keeps the log).
Generation already done is reused, only in-progress Lean builds are lost. After ~15 min: `uptime` should show load ~3-4 and `cat ~/l435/prod/budget.json` usually more than one entry under "run". Then continue holding the turn open (wait chain, 15-min send_later safety net).

## Relaunch for the "over builds" fix 6ecaa06f (18 Nov 17:55 UTC; owners and helpers only, NOT split machines)
Small builds may now run beside big ones when RAM is free (preemptible). Same steps as the 87fbd8e5 section, with these rules:
- `ps -eo pid,etime,args | grep "[b]in/lean -R /root/l435/prod/jobs"`: if NO lean build has run longer than ~45 min, relaunch now. Otherwise wait for that big build to end (`while kill -0 PID; do sleep 60; done`, <= 9 min per Bash call), then relaunch.
- Machines still on 478869ee/46b11be3 (never did the 87fbd8e5 relaunch): relaunch NOW regardless.
- After checkout, `git log --oneline -1` must show 6ecaa06f or later. After ~15 min `cat ~/l435/prod/budget.json` should show entries under "over" while big builds run; load ~3.5-4.
Then keep holding the turn open.

## Split work stealing (18 Nov 20:00 UTC, commit 3fa46a11): converting a machine to a split stealer
The 109 split items are the critical path. Machines told to become SPLIT STEALER K do this once:
1. Stop the old job by PID: split machines kill their c230split.py / splitfarm435.py / lean PIDs; helpers kill their `prod435.py run` tree (and its lean / c230.py cert / genv3stream children). Pushed sources and parts are reused.
2. `git fetch origin research/unconditional-241 && git checkout -B research/unconditional-241 FETCH_HEAD && git log --oneline -1` (>= 3fa46a11); `[ -f ~/l435/prod/core/LocalWindowShareCtx.olean ] || python3 lean435/tools/prod435.py setup`; the four exports.
3. LAUNCH: `nohup python3 lean435/tools/c230split.py --steal --index K >> ~/c230_steal$K.log 2>&1 &`   (LOGFILE ~/c230_steal$K.log, PGREP "c230split.py --steal")
4. Keep holding the turn open (chained <= 9-min waits, 15-min send_later). To stop: `touch ~/l435/prod/STOP_SPLIT` (finishes running units).
Indices: static split machines S0..S5 -> K = 1..6; helpers -> K = 7 and up (the orchestrator assigns K).

## Stealer relaunch for bd7e3cac (18 Nov 20:20 UTC; split stealers only, no work lost)
`kill $(pgrep -f "c230split.py --steal")` (ONLY the stealer; do NOT kill splitfarm435/lean children), then fetch/checkout research/unconditional-241 (>= bd7e3cac), the four exports, and the same LAUNCH line (`--steal --index K`). The log shows "adopted N running unit(s)". Keep holding the turn open.

## Cheap keep-alive (replaces "Hold the turn open", 19 Nov 03:20 UTC)

The account hit its 5-hour usage limit because ~50 sessions made a model
call every 9 minutes. A harness-tracked background task keeps the container
alive while the turn is ended (tested by the efficiency session). So:

1. Start ONE Bash call with `run_in_background: true`, `timeout: 2400000`:
   `timeout 1800 bash -c 'while pgrep -f "PGREP" >/dev/null; do sleep 120; done'; date; tail -3 LOGFILE; uptime -s`
2. Arm a `send_later` safety check-in 40 minutes ahead.
3. END THE TURN (no text needed). Never end a turn without such a tracked
   background task running: an idle session without one loses its container.
4. On every wake (task finished, or the check-in): if the job died, redo the
   setup block and the same LAUNCH line; then repeat steps 1-3. No other
   commands, no text.

## Stealer to main-plan helper conversion (19 Nov 14:20 UTC)

The split backlog is nearly drained (97 of 109 items published, the rest
claimed), so the repository owner's plan is to move split stealers to the
main plan. The coordinating session tells each stealer its helper index J
(J = 20 + K). When told to convert:

1. `touch ~/l435/prod/STOP_SPLIT` (the stealer finishes its running units
   and exits).
2. Wait until `pgrep -f "c230split.py --steal"` is empty, with tracked
   background waits as in "Cheap keep-alive", ending the turn between waits.
3. `rm -f ~/l435/prod/STOP_SPLIT`, then with the four exports of the setup
   block (`C230_PLAN` = `c230plan.json.gz`):
   `nohup python3 lean435/tools/prod435.py run --steal --plan $C230_PLAN --index J --hours 48 --max-plan-hints 2e7 > ~/c230_hJ.log 2>&1 &`
4. Continue the cheap keep-alive with PGREP `prod435.py run --steal` and
   LOGFILE `~/c230_hJ.log`.

Stealers K1-K4 stay on split work until all 109 items are published.
