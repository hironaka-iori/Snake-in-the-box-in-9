# Current execution instructions

Use the v2 scripts with native memory monitoring. The original prepared
scripts are preserved for provenance. No pilot module has yet been checked.
Wait for the current milestone154 compiler batch and its paper compilation
to finish; inspect live processes before starting another compiler.

From the repository root, using the configured Python runtime:

```powershell
python -B -X utf8 milestones/155-share17-replay/scripts/run_replay_v2.py
python -B -X utf8 milestones/155-share17-replay/scripts/finish_pilot_v2.py
python -B -X utf8 milestones/155-share17-replay/scripts/emit_full_v2.py --full --max-source-mib 256
```

The emitter is guarded by acceptance of all 34 pilot modules. It generates
full sources only. A separate full checker and runner must reuse the pilot
receipts and complete the single contradiction. Compose that checked result
with the broader actual-snake implication from milestone154 afterwards.
Pilot progress: data/replay-progress-v2.json. Pilot acceptance:
data/pilot-completion-v2.json. Do not treat either source preparation or a
pilot checkpoint as the complete contradiction or a new global bound.
