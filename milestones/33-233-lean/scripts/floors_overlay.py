"""Build the LEAN_PATH overlay for `chain_audit.py --extra-lean-path` after the floor port.

    python3 -I floors_overlay.py PORT_OLEAN_DIR OVERLAY_DIR

Lean resolves a module in the first LEAN_PATH entry that has its top-level directory.  The
port's `.olean` files live under `LocalWindowCnf/` and `LocalWindowUnsat/`, which the core build
also has, so the overlay holds symlinks to every port `.olean` plus symlinks to the core's
`.olean` files under the top-level directories the two share.  A name collision aborts.
"""
import os, sys
from pathlib import Path
CORE = Path(__file__).resolve().parents[3] / 'work/final_lean/.lake/build/lib/lean'
port, out = Path(sys.argv[1]).resolve(), Path(sys.argv[2])
out.mkdir(parents=True)
n = {'port': 0, 'core': 0}
for f in port.rglob('*.olean'):
    d = out / f.relative_to(port); d.parent.mkdir(parents=True, exist_ok=True); os.symlink(f, d); n['port'] += 1
for top in sorted({p.name for p in port.iterdir() if p.is_dir()}):
    if not (CORE / top).is_dir():
        continue
    for f in (CORE / top).rglob('*.olean'):
        d = out / f.relative_to(CORE)
        if d.exists() or d.is_symlink():
            raise SystemExit(f'collision: {d}')
        d.parent.mkdir(parents=True, exist_ok=True); os.symlink(f, d); n['core'] += 1
print(n)
