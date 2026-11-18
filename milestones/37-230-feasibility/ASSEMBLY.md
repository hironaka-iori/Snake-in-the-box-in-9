# Lean glue and assembly of the bound 230 (K7 route)

Status: **in progress** (18 November 2026). Nothing here claims the bound: the claim needs a passing
final audit of `Snake9.upper_230_435`.

## The theorem and its premises

```
Snake9.upper_230_of_refutedK7 (hT : C230.AllTab C230.tab230) (hS : C230.AllShareL C230.shares230) :
    ∀ {m : Nat}, Snake m → m ≤ 230                                          (lean435/c230/C230Final.lean)
```

1. **Walk.** The ported chain `total_boundK7R34C7W16` (relaxed-keller milestone 10, 4.19 → 4.35) with
   `d = pathDir p`, `a = coreAlpha p`: `89 m ≤ 19 Σ_{k=1}^{m-1} α_k + 678`. Its premises `hw2 .. hw7`
   (no window is excluded by `wforbK7R34C7W16`) come from `C230K7.no_forb`.
2. **Cover** (`C230K7.lean`, `C230Mask.lean`, generated `C230Rows*`, `C230Shapes`).
   `wforbK7R34C7W16 s syms` is bit `16 pos(code syms) + 15` of the forward row `sfwd c (wsh s)` or of the
   reverse row `srev c (wsh s.reverse)`. For every canonical induced shape of 3 .. 8 directions
   (1, 2, 4, 12, 34, 132 shapes; `ShapesCover`, kernel RGS enumeration) both rows are checked by one kernel
   evaluation each (`rowCheck`): every set bit is the position of a symbol list inside a key box of the
   table `tab230` (forward: keys of shape `s`; reverse: keys of shape `canon s.reverse`, read backwards).
   The mask of the key boxes is built by halving the position range, so a 4 MB row costs about
   size × 12. Two-centre rows hold copies of their entries and are checked under the mask `v2` of the bits
   `wforb` reads. A hit gives a key `(shape, intervals)`; `window_refute` applies its certificate through
   `C230Cover.refuted_dir_iv` (reverse hits: on `revSnake p`).
3. **Shares.** Every 8-direction window has its canonical shape in `shares230` (= `shapes8`); the
   certificate `RefutedShare (winOf s) [(1,21)] × 7 12 29` gives corner share ≥ 30 on its 7 centres
   (`refuted_share_bridge`). With `core_charge_sum_le 12` and `α_0, α_m ≥ 4`: `127242 m ≤ 29391726`.

## The table `tab230` and its certificates (`AllTab tab230`)

`lean435/data/c230derive.json.gz` (`c230derive.py`) gives each of the 58,817 exclusions of the chain one
source of `Refuted (winOf dirs) alpha` (literal intervals):

| source | count | Lean term |
|---|---:|---|
| own certificate of the 230 plan | 33,628 | `V….refuted` (farm, `xfer/c230*`) |
| a 231 plain key on a sub-window (either orientation) | 25,189 | `Families.refuted_sub (mkPerm v) s (<231 term> : Refuted …) (by decide +kernel)` |

The 231 terms are those of the 231 glue (`glue435.plain_term`): 10,086 certificate modules of the 231 audit,
all in the archive `research/c435-interfaces-231`. `subOK` is evaluated in Python before generation.

## Corner-share certificates (`AllShareL shares230`)

`c230.py shareplan` → `data/c230share.json.gz` (132 items, kind 5, code 19 = `(1, 21)`, level 30). The share
route of prod435 with the c230 adapter builds `LocalWindowCert.W<dirs>AFFFFFFFK29`:
`RefutedShare (winOf dirs) ([(1, 21), …]) 12 29` (the adapter writes the literal intervals into the Cnf
module; `boundsOf` would mean `(6, 21)`). They are produced by helper 900:

```bash
export PROD435_ADAPTER=$PWD/lean435/tools/c230.py PROD435_CERT="$PWD/lean435/tools/c230.py cert"
export PROD435_PFX=refs/heads/xfer/c230/ C230_PLAN=$PWD/milestones/37-230-feasibility/data/c230share.json.gz
python3 lean435/tools/prod435.py run --steal --plan $C230_PLAN --index 900 --hours 12 --procs 1
```

publishing to `xfer/c230help/w900` (more helpers may use other indices ≥ 901).

## Assembly (when the farm has finished)

```bash
bash lean435/tools/c230chain.sh ~/l435/c230chain              # spec layer: port, generate, build
python3 lean435/tools/prod435.py merge --out ~/l435/iface230  # with the c230 exports; all xfer/c230* families
# 231 interfaces: git fetch --depth 1 origin research/c435-interfaces-231; extract to ~/l435/arch231
python3 lean435/tools/assemble230.py --spec-src ~/l435/prod/core-src --spec-build ~/l435/prod/core \
  --spec-src ~/l435/c230chain/src --spec-build ~/l435/c230chain/build --glue ~/l435/c230chain/gen/glue \
  --iface <merged dir with both interface sets> --manifest <230 manifest> --manifest ~/l435/arch231/manifest.jsonl \
  --work ~/l435/asm230
```

`assemble230.py` compiles the 305 glue chunks, `G230S` and `G230` from interfaces only (hash checks, clean
directory, strace), then `UpperBound230_435.lean` with `audit.py final`; the axioms of
`Snake9.upper_230_435` must be within `[propext, Classical.choice, Quot.sound]`.

## Tests so far

- **Conditional 230 (18 Nov, 03:40 UTC):** the whole spec layer (417 modules: core, ported K7 chain,
  main-line bridges, `C230*` incl. all 85 row-check modules and the shape covers) built on this machine;
  `assemble230.py --conditional` (audit.py final, clean directory, strace) on
  `Snake9.upper_230_of_refutedK7 : AllTab tab230 → AllShareL shares230 → ∀ m, Snake m → m ≤ 230`:
  `[propext, Classical.choice, Quot.sound]`, AUDIT PASSED (`audit230/conditional-audit.txt`). What remains
  is the glue, i.e. the certificates themselves.
- Row checks: 41 modules, largest `C230Rows7_0` 168 CPU-s, peak 4.1 GB (`C230Rows7_1`); ~15 min in all on 3 cores.

- Glue chunks `G230_0_0` (4 certificates of 231) and `G230_50_0` built from the archived 231 interfaces:
  AUDIT PASSED, no interface `.olean.private`/`.server` opened.
- Kernel cost of the largest row check (2,462 key points, 4 MB row, mask included): 23 s, 2.4 GB.
