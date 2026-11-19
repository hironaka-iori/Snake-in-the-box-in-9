# Pilot certificate: Lean kernel time per LRAT hint for the level-116 cubes

Purpose: measure what one level-116 cube certificate costs in Lean before any farm Lean time is spent.

- What is measured: the kernel seconds per LRAT hint of the repository's v3 replay (`LratV3`, generated
  by `lean435/tools/genv3stream.py`) at literal offset 65,536, and the peak RSS.
- Why it is needed: the compacted cores of the cube CNFs have about 54,000 variables, against at most
  4,000 for the window certificates, so the calibration of milestone 36 (0.23 ms per hint) may not hold.

Machine: a free 15-16 GB machine with Lean 4.35 at `/opt/lean-4.35.0-linux` and CaDiCaL 2.1.3 on PATH
(the `snake-in-the-box-9-lean435` environment). Do not run it next to other heavy jobs.

## Commands (one Bash call; about 30-90 min)

```bash
cd ~/Snake-in-the-box-in-9 2>/dev/null || cd /home/user/Snake-in-the-box-in-9
git fetch origin research/unconditional-241 && git checkout -B research/unconditional-241 FETCH_HEAD
nohup bash milestones/39-dim8-lift/cert/run_pilot.sh > ~/pilot39.out 2>&1 &
```

Then keep the session alive with tracked waits on `~/pilot39.out` and `~/pilot39/pilot.log` until the
log line `done:` appears or the script stops.

## What `run_pilot.sh` does

1. Builds the milestone-39 Lean modules (`milestones/39-dim8-lift/lean/build.sh`, core Lean, about 5 min).
2. Exports one cube CNF, `cubeCnfC4 13 116 0x036cbc13bc5243ac 29` (858 k clauses), with
   `lean --run Export.lean`. It solves the CNF with `cadical --lrat` (about 25 s, a 68 MB LRAT file).
3. Runs `cert/pilot.py`:
   - extracts the core (75,503 clauses) and compacts its 54,398 variables;
   - renames the LRAT;
   - writes the core module, NatPack-packed: about 0.7 GB RSS to elaborate, against more than 9 GB
     unpacked.
4. Runs `genv3stream.py --off 65536`: 40 segments, 17-bit words, about 15.6 MB of Lean.
5. Builds the prerequisites: `LocalWindowModel`, `LratV3` (with the one 4.35 fix of `lean435/tools/port.py`),
   `NatPack`, `ProofPack`, `SplitZ` and the core module.
6. Builds the replay module `LocalWindowUnsat/CubeP0.lean`. All kernel checks happen in this step, and
   the step is timed and its peak RSS recorded.
7. Writes `milestones/39-dim8-lift/cert/results/pilot_<host>.json` and commits and pushes it to
   `research/unconditional-241`. It fetches by name, merges and never forces.

The result file contains:

| field | meaning |
|---|---|
| `replay_seconds` | wall time of step 6 |
| `replay_peak_rss_mb` | peak RSS of step 6 |
| `hints` | 1,880,307 |
| `ms_per_hint` | replay milliseconds per hint |
| `exit_code` | of step 6 |
| `axioms` | output of `#print axioms` for `Snake9.LocalWindow.CubeP0.unsat` |
| `replay_errors` | tail of the build output |

If step 6 fails or exceeds memory, the JSON still records the exit code and the error tail. Push it anyway.

Rules for the machine: push only this result file to `research/unconditional-241`. Do not touch
`refs/heads/xfer/*` or the 230 farm.
