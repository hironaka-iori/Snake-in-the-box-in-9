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
