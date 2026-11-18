# Remote branches of the certificate farm: what the 232/231 audits need (milestone 36)

Inventory of 17 November 2026, 23:40 UTC, from one `git ls-remote --heads origin`. Nothing was fetched for it.
That call listed **433 heads**.

**Do not fetch these families with a plain `git fetch`/`git pull`.** They are many GB in all; see Incidents in
the [README](README.md). The tools fetch single refs, at depth 1.

## Counts

| family | heads | role |
|---|---:|---|
| `xfer/c435/w*` | 32 | **required**: owner workers of the paid 4.35 family (public `.olean` + manifest lines) |
| `xfer/c435help/w*` | 69 | **required**: helper workers of the paid family (`run --steal`), including `w150` (the five split certificates) |
| `xfer/c435help/claims` | 1 | scratch: an old claims ref |
| `xfer/c435free/w*` | 12 | **required**: the free family (free plain seeds and free share keys) |
| `xfer/c435freehelp/*` | 0 | (none exist; the merge reads the prefix but nothing is there) |
| `xfer/c435claim/*` | 112 (80 `h*`, 32 `o*`) | scratch: claims of owners and helpers |
| `xfer/c435freeclaim/*` | 2 (`h90`, `o11`) | scratch: claims of the free family |
| `xfer/c435test/*` | 2 (`ctl`, `w0`) | scratch: the toy test of `prod435.py` (README, "Test branches") |
| `xfer/c435split/src-*` | 6 | sources of split certificates (see below) |
| `xfer/c435split/<N>-k<K>` | 66 | built kernel part modules of split certificates (see below) |
| `xfer/233/*` | 59 | Lean 4.19, milestone 33: generated sources of 58 certificates moved to cloud workers, and `xfer/233/cadical` |
| `xfer/233o/*` | 19 | Lean 4.19, milestone 33: the built `.olean` files of the 19 certificates compiled on cloud workers |
| `xfer/231/*` | 15 (`ctl`, `w0`–`w13`) | milestone 28 `farm231.py`: solver farm records (plain/share/ctx/rounds) |
| `xfer/231s/w*` | 10 | milestone 28 `certsample231.py`: certificate cost samples |
| `xfer/231x/w*` | 10 | milestone 28 `split231.py`: split/re-solve job results |
| other | 18 | `main`, `research/*` (14), `claude/*` (2), `RamseyCheck` (not part of the farm) |

## Required to reproduce the 232 and 231 audits

The 113 branches `xfer/c435/w*`, `xfer/c435help/w*` and `xfer/c435free/w*` are required. Each holds the
**public** `.olean` of the certificates its worker finished, plus one manifest line per certificate:
- the sha256 and size of every part;
- the source sha256 and the generator commit;
- the Lean version;
- the statement, the hints and the CPU time.

`prod435.py merge` with those three prefixes (and `c435freehelp`, now empty) rebuilds the interface directory.

The merge at 21:41 UTC gave:
- **27,402 certificate interfaces** from 113 branches, with 0 conflicts;
- a merged manifest of 27,402 lines, 55.6 MB, sha256 `ac2ea1cb…52b2f`.

The union of what the two audits need is exactly these 27,402 modules:
- 24,797 for 231 and 12,507 for 232, of which 9,902 are shared;
- 401.8 MB of public `.olean` in total (231 alone: 359.3 MB).

The manifest subsets committed in [`audit232/`](audit232) and [`audit231/`](audit231) pin every one of them
by sha256. So a re-merged directory can be checked line by line against the repository, even if the branches
were rewritten.

Which branch holds which module is not recorded; the merge keeps one copy per module. So all 113 branches
must be kept, unless the consolidated archive below replaces them.

The spec layer is not on any branch: core, chain, floors and mathlib are rebuilt from the repository and
`/opt/mathlib4-v4.35.0`, as described in the README.

## Split certificates (`xfer/c435split/*`)

Five certificates of the 231 plan were built by the split route ([SPLIT.md](SPLIT.md)):
`T012301A36264K45`, `T012301A46246K33`, `T012301A33436K47`, `T012301A35353K20` and `T012301A26346K35`.

- **For the audits**, only their final public `.olean` on `xfer/c435help/w150` is needed. It is part of the
  required set above.
- **To re-check a split certificate from sources**, `xfer/c435split/src-<N>` is enough. It holds the gzipped
  split sources (`SPLIT-MANIFEST.N.json` with the sha256 of every source). `splitfarm435.py part` and
  `final` rebuild the Cnf, D and Ps base modules, every kernel part K and the final module from it, then
  compare the final `.olean` with the manifest. Rebuilding the parts is the expensive step: 5.4 to 12.5
  CPU-hours per certificate (SPLIT.md, Results).
  - The sources can also be regenerated from the generator: the manifest records the generator commit and the
    source sha256, and `split435.py` is deterministic.
  - So `src-<N>` saves that regeneration and pins the exact input.
- **The part refs `<N>-k<K>`** hold the built part modules and their manifests. They are needed only to rerun
  `splitfarm435.py final` without rebuilding the parts, for example to check that the published final
  `.olean` came from these parts. They are not needed for a from-source re-check.
- **`T012304A44356K33`** (`src-` plus 2 part refs) is an abandoned split. The stock route published that
  certificate first, and nothing of the split was published. All 3 refs are scratch.

## Scratch: safe to delete for the owner

The scratch refs are:
- `xfer/c435claim/*` (112);
- `xfer/c435freeclaim/*` (2);
- `xfer/c435help/claims` (1);
- `xfer/c435test/*` (2);
- the 3 `xfer/c435split/*T012304A44356K33*` refs.

That is 120 heads. They hold coordination state only (who builds what), or a test, or an unpublished split.
No audit reads them.

The 64 part refs and the 5 `src-*` refs of the five published split certificates are **not** scratch. SPLIT.md
("What an independent re-check needs") asks to keep them as the record of what was checked where.

The agents do not delete branches (an agent session's git proxy refused branch deletion with HTTP 403 in
milestone 33, CERT-PROGRESS, 13 November). Deletion is for the owner.

## Older families (what is known from the repository)

- **`xfer/233o/<name>` (19).** The `.olean` files of the 19 large 233 certificates that were built on cloud
  workers with Lean 4.19. `xfer233.py opull` installed each after a sha256 check, against
  `milestones/33-233-lean/certify/data/remotebuild6SB233.jsonl`.
  - They are **needed to rerun the Lean 4.19 233 audit without rebuilding those 19 certificates**.
  - Keep them unless the owner accepts a from-source rebuild of those 19.
- **`xfer/233/<name>` (58 + `cadical`).** Sources of 233 certificates, generated remotely by `xfer233.py gen`,
  were pushed here for the cloud builds.
  - The sources are reproducible with `cert233.py` (the repository holds the generator). So they are
    convenience copies, not the only copy.
  - What `xfer/233/cadical` holds is not documented in the repository I read (presumably the CaDiCaL binary
    given to the workers). Check it before deleting.
- **`xfer/231/*`, `xfer/231s/*`, `xfer/231x/*` (35).** Solver-side farm results of milestone 28 (`farm231.py`,
  `certsample231.py`, `split231.py`). Their results were merged into `milestones/28-combined-identities/data/`,
  and the 231 plan `certplan231_563_1_cap.json.gz` used here is committed.
  - They are not needed for the 232/231 Lean audits. They are the raw records behind the committed merged data.
  - Delete them only if the owner is satisfied that the merged data suffices.

## A consolidated archive branch

All 27,402 needed interfaces plus the merged manifest would fit one orphan branch, for example
`research/c435-interfaces-231`:
- `tar | gzip -1` of the merged directory is **119 MB** (401.8 MB of `.olean` uncompressed, plus the 55.6 MB
  manifest); a git pack of the same files should be of the same order;
- 27,403 files, each far below GitHub's 100 MB file limit.

This is practical, and it would let the owner delete the 113 worker branches after checking the archive
against the committed manifests. The orchestrator agreed, and the archive was built and verified (18 November, 00:00 UTC):
- orphan commit `e82d6b68cbc10ad9f80f918eb595d04154d49c39`, tree `89fa780c`;
- 27,402 `.olean` files, every one equal to `parts[".olean"]` of the committed audit manifests;
- `manifest.jsonl.gz`, `OLEAN-SHA256.txt` and a README with the exact `assemble435.py --iface … --manifest …`
  command.

It is **not pushed**. The owner's rules for this work allow commits to `research/unconditional-241` only,
so pushing a new branch needs the owner's explicit approval. Until it is pushed, the 113 worker branches
remain **required**. Once it is pushed and checked, they are redundant for the 232/231 audits. Nothing is
to be deleted except by the owner.
