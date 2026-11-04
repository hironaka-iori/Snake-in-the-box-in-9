# Resume the existing share-18 proof

Work from `E:/Snake-in-a-box`. Inspect the current161 batch record and actual
processes before starting another run. An observation timeout does not mean
that the compiler stopped. Use one compiler at a time and preserve all
accepted sources, objects, logs and receipts.

The bounded continuation command is:

```powershell
& 'C:/Users/hironakaiori/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe' -B -X utf8 'milestones/161-share18-full-replay/scripts/run_replay.py' --limit 100
```

The limit counts newly accepted modules. Existing accepted modules are
verified and reused. A resource stop or compiler failure is recorded and
does not establish a contradiction. Inspect its specific record before
retrying; never restart merely because a tool stopped displaying output.

After a terminal bounded batch, use `audit_progress.py` in the same scripts
folder with a fresh `--label`. It verifies the consecutive completed groups,
their segment checks and the preserved terminal batch record. A bounded
prefix composition can then be checked using the procedure saved in162
and reused here. Read `data/completion.json` when present for this round's
accepted extent; source preparation alone is insufficient.

The last complete group needs a separate final-contradiction audit. Require
every continuation segment and the final empty-clause theorem before using
the three remaining actual-snake checks described in
`../162-share18-composition-plan/review/remaining-composition.md`.

The numerical snake bound remains unchanged until its separate local and
global obligations are met. Last full paper revision:156; next:166.
