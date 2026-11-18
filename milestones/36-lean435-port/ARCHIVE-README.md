# Certificate interfaces of the Lean 4.35 bounds 232 and 231 (archive)

This orphan branch holds the **public `.olean` interfaces** of every certificate used by the two
interface-only audits of milestone 36 on branch `research/unconditional-241`:
- `Snake9.upper_232_435` (plan `certplan231_m232_541_1b`, tag `M232B541`, 12,507 certificates);
- `Snake9.upper_231_435` (plan `certplan231_563_1_cap`, tag `563B1`, 24,797 certificates).

The two sets share 9,902 certificates, so the union is **27,402 modules**. The archive was made on
17 November 2026 (23:30 UTC). It is a copy of the interface directory that `prod435.py merge` built from the
113 worker branches. Those branches were:
- `xfer/c435/w*` (32);
- `xfer/c435help/w*` (69, including `w150` with the five split certificates);
- `xfer/c435free/w*` (12).

That merge was the one used for the 231 audit, at 21:41 UTC: 113 branches, 0 conflicts.

| path | contents |
|---|---|
| `LocalWindowCert/*.olean`, `LocalWindowCtxCert/*.olean` | the 27,402 public `.olean` files (401.8 MB). No `.olean.server`, `.olean.private` or `.ir` |
| `manifest.jsonl.gz` | the merged manifest, one line per module, from the farm. It records the sha256 and size of every part, the source sha256, the generator commit, the Lean version, the statement, the hints and the CPU time. Uncompressed it is 55.6 MB, sha256 `ac2ea1cba097db0096edc74f4a328b9b5f3fa0b33ab42fca9b3b22b36d252b2f`; the gzip sha256 is `d8d58b3e9460ab4aa25d465c7e7f9ec070a8c093a81c44bb9e404520e7dcbbbf` |
| `OLEAN-SHA256.txt` | `sha256sum` of every `.olean` here, sorted by path (sha256 `06a6955c1e8b95e0bfdf97fc25507a6370a687297284fabb41c98ee7d2aaab52`) |

## Verification before the push

Every one of the 27,402 files was hashed and compared with the `parts[".olean"]` sha256 of its line in
the committed manifests:
- `milestones/36-lean435-port/audit232/manifest232.jsonl.gz`;
- `milestones/36-lean435-port/audit231/manifest231.jsonl.gz`.

All matched. The set of modules was exactly the union of the two manifests: no file missing, no extra file.

## Use instead of the worker branches

Fetch this one branch only, at depth 1. Then unpack the manifest and hand the directory to
`assemble435.py`, which takes `--iface` and `--manifest` directly. `audit.py final` re-checks every sha256
against the manifest on each compile.

```
git fetch --depth 1 origin research/c435-interfaces-231
git worktree add ~/l435/arch FETCH_HEAD           # or: git archive FETCH_HEAD | tar -x -C ~/l435/arch
gunzip -k ~/l435/arch/manifest.jsonl.gz
python3 lean435/tools/assemble435.py --tag 563B1 --chain-src ~/l435/chain231/src --chain-build ~/l435/chain231/build \
  --glue ~/l435/chain231/glue --iface ~/l435/arch --manifest ~/l435/arch/manifest.jsonl \
  --floors-src ~/l435/floors/src --floors-build ~/l435/floors/build --bound 231 --jobs 2 --work ~/l435/asm231-arch
```

For 232, use `--tag M232B541`, `~/l435/chain232` and `--bound 232`. The spec layer is rebuilt from the
repository, as described in `milestones/36-lean435-port/README.md`, sections "Final audit of the bound 232"
and "Final audit of the bound 231":
- the core (`prod435.py setup`);
- mathlib (`/opt/mathlib4-v4.35.0`);
- the floors (`lean435/floors/tools`);
- the chain (`chain435.sh <plan> <tag> <bound> <dir>`).

## What this archive does not contain

- **The certificates' proofs.** The `.olean.private` and `.olean.server` parts are not here; they were never
  published. Their kernel checks ran once, on the farm machine that built each module. Re-checking them means
  rebuilding from source. The manifest gives the source sha256 and the generator commit; the split
  certificates' sources are on `xfer/c435split/src-*`.
- **Any statement about `main`.** This is an orphan branch with one commit and no parent.
