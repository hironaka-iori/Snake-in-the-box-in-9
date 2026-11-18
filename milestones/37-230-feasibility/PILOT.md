# Pilot of the certificate production for the 230 route

Run of 17-18 November 2026 on one 4-core, 15 GB machine. Lean 4.35.0 was installed at
`/opt/lean-4.35.0-linux` and CaDiCaL 2.1.3 was used. The goal is to check, before 40-50 workers start,
that every certificate of the K7 cap-7 route (see `README.md`) can be produced, published and consumed
by the glue, and that none will need rebuilding later.

## 1. The certificate statement (fixed)

Every certificate is one module `LocalWindowCert.<NAME>` whose only public theorem is

    Snake9.LocalWindow.<NAME>.refuted : Refuted (winOf [d0, d1, ...]) ([(lo0, hi0), (lo1, hi1), ...])

The parts of this statement:

- **`Refuted`:** the predicate of `LocalWindowModel` (core stack), the same predicate as every 233/231
  plain key. It does not depend on the radius; the radius (3, or 4 for 113 keys) only selects the
  ball of the CNF.
- **The directions:** the canonical direction list of the key, as a literal.
- **The bounds:** the key's count intervals, as a literal. They are written through the existing
  widened-seed path of `gen_lean_cnfsat_packed.py` (`lean_bounds`).
- **`NAME`:** `'V' + dirs + 'A'` and one character per count:
  - `1`-`5`: that count exactly;
  - `G`: the interval [6,21];
  - `6`, `7`: exactly 6 or 7;
  - `H`: the interval [8,21].
  The `V` prefix cannot clash with the S/T/C modules of the 233/231 families.
- **Imports:** a certificate imports only core-stack spec modules, publicly `LocalWindowShareCtx`
  and privately `LocalWindowDirModel`, `LocalWindowCnfPack`, `LocalWindowTagsW`, `LratV3` and
  `ProofPack`. It never imports the K7 automaton chain. So the pending 4.19 -> 4.35 port of the
  173-module SWAR chain cannot invalidate any certificate.

**Bridge.** The certificates go through `LocalWindow.refuted_bridge` (`LocalWindowBridge`, core stack,
already ported), which takes arbitrary bounds. `lean435/c230/C230Cover.lean` (4.35, no sorry) contains:

- `refuted_dir_iv`: `refuted_dir` with explicit interval bounds, from snake window to `False`;
- `AllRefutedIV L`, with `get` and `append`, and `no_window_of_list`: the form the K7 cover lemma will
  consume;
- `refutedIV_of_main`: reuse of the 25,189 windows that our existing certificates imply. A lumped key
  `Refuted (winOf cs) (boundsOf syms)` gives every narrower interval key through
  `Families.refuted_narrow`. Sub-windows go through `refuted_sub` / `refuted_key_sub` of
  `LocalWindowFamilies` in the same way.

`lean435/c230/C230Toy.lean` consumes the published pilot certificate `V012034A2H644` (`toy_window`,
`toy_narrow`). `audit.py final` passed on it from the interfaces alone:

- only `V012034A2H644.olean` of the certificate was opened (strace);
- nothing outside the clean directory and the toolchain was opened;
- the axioms are `[propext, Classical.choice, Quot.sound]`.

## 2. The production adapter

- **`lean435/tools/c230.py`**
  - `plan`: writes `data/c230plan.json.gz` from `data/k7_uncovered.json.gz`, in the certplan231 format.
    It has 33,628 plain items, all paid. `est_hints` is the DRUP lines times 8.8 (47.7 G in total).
    Each item also carries `radius`, `bounds`, `case`, `drup_lines` and `split` (set when the estimate
    is above 20 M).
  - `cert STEP ...`: cert435.py with the adapter applied.
  - `names PLAN [--min-est H]`: lists the items.
- **What the adapter changes in the 4.19 generators** (in this process only, nothing on disk):
  - it decodes the interval codes in `dir_bounds` and `bound_of`;
  - it names keys `V…`;
  - it sets the radius per key;
  - it writes `lean_bounds` and the true radius into every core JSON;
  - it sets the SPLIT.md replay defaults: one round of the 3-configuration portfolio, `--seed=1`, and
    `genv3stream.py`.
- **`prod435.py` hooks.** Two opt-in hooks: `$PROD435_ADAPTER`, whose `apply()` is called before
  `cert231` is used, and `$PROD435_CERT`, the command run instead of `cert435.py`. When they are
  unset, nothing changes for the 231/232 families.
- **Split route.** `bigreplay435.py` and `splitfarm435.py prepare` now accept plain seeds. The split
  family is `<PROD435_PFX>split/`, i.e. `xfer/c230split/`.
- **Branch families (new):**
  - `xfer/c230/w<I>`: owners;
  - `xfer/c230help/w<J>`: helpers and split finals;
  - `xfer/c230claim/{o<I>,h<J>}`: claims;
  - `xfer/c230split/{src-N,N-k<K>}`: split sources and parts;
  - `xfer/c230/ctl`: STOP.

## 3. Pilot certificates

| item | route | plan est. | real hints | kernel CPU | peak RSS (anon) | public .olean | published |
|---|---|---|---|---|---|---|---|
| `V012034A2H644` (r 3) | prod435 | 0.30 M | 0.18 M | 16.8 s | 0.70 GB | 9 KB | `xfer/c230help/w0` |
| `V012031A33555` (r 3) | prod435 | 5.09 M | 7.40 M | 1,113 s (republished run: 1,134 s) | 2.33 GB | 28 KB | `xfer/c230help/w0` (same .olean sha256 as the first, independent build) |
| `V0120342A664435` (r 3) | split, 8 parts | 20.1 M | 30.77 M | 7,681 s over 8 parts (441-1,260 s each) | 3.74 GB (part K7) | 8 KB | `xfer/c230help/w500` (parts `xfer/c230split/V0120342A664435-k0..k7`, sources `src-…`) |

Kernel cost on these two is **0.09-0.15 ms per hint**, below the 0.3-0.5 of the 231 share
certificates.

The plan underestimates large items by about 1.45x: 5.1 -> 7.4 M, and 20.1 -> 30.8 M. Small items are
overestimated: 0.30 -> 0.18 M. Per SPLIT.md, prod435 already schedules on the cores step's estimate,
not the plan's.

## 4. Calibration of the plan (cores step on a random stratified sample)

The plan's `est_hints` is DRUP lines x 8.8. The 8.8 assumed replay = 0.6 x the trimmed full proof, the
ratio of the share certificates. For these plain keys the replay is 0.82-0.96 of the cores step's
full-proof estimate (pilots 1-2).

24 items were drawn, one per equal-count stratum of the 33,519 non-split items, and only the cores
step was run (`c230.py cert cores`, 2.2 s per M hints). Their full-proof estimates are 0.02-2.8x the
plan; small items are overestimated and large ones underestimated (median 1.3, pooled 2.0).

Stratified totals, non-split items:

| quantity | G hints |
|---|---|
| plan | 44.6 |
| cores estimate | 86.9 |
| replay | about 75 |

With the 109 split items, about 5 G at the pilot's 1.5x, **the real total is about 80 G hints
(range 65-100 G)** against the plan's 47.7 G. The sample is only 24 items, and the largest stratum
dominates.

Kernel cost measured here:

| item | route | ms per hint |
|---|---|---|
| pilot 1 (0.2 M) | prod435 | 0.09 |
| pilot 2 (7.4 M) | prod435 | 0.15 |
| pilot 3 (30.8 M) | split | 0.24 (summed over its parts) |

So the certificates need 80 G x 0.15-0.24 ms = **3,300-5,300 kernel-hours**.

prod435 schedules and sizes memory by the cores estimate (not the plan), so the underestimate affects
only the total time.

## 5. Worker instructions

Every machine needs:

- the environment `snake-in-the-box-9-lean435` (Lean 4.35.0 at `/opt/lean-4.35.0-linux`,
  `cadical` 2.1.3 on PATH, 15 GB, 4 cores);
- this branch, fetched by name, at commit >= the one that adds this section.

```bash
cd ~/Snake-in-the-box-in-9
git fetch origin research/unconditional-241 && git checkout -B research/unconditional-241 FETCH_HEAD
python3 lean435/tools/prod435.py setup                      # core stack, ~2 min (once per machine)
export PROD435_ADAPTER=$PWD/lean435/tools/c230.py
export PROD435_CERT="$PWD/lean435/tools/c230.py cert"
export PROD435_PFX=refs/heads/xfer/c230/
export C230_PLAN=$PWD/milestones/37-230-feasibility/data/c230plan.json.gz
```

**Owner I of W.** Hash-partitioned, largest first, publishes to `xfer/c230/w<I>`:

```bash
nohup python3 lean435/tools/prod435.py run --plan $C230_PLAN --index $I --workers $W --hours 48 \
      --max-plan-hints 2e7 > ~/c230_o$I.log 2>&1 &
```

**Helper J (J >= 1; 0 was the pilot).** Whole plan, smallest first, publishes to `xfer/c230help/w<J>`:

```bash
nohup python3 lean435/tools/prod435.py run --steal --plan $C230_PLAN --index $J --hours 48 \
      --max-plan-hints 2e7 > ~/c230_h$J.log 2>&1 &
```

**Split machine S of N.** For the 109 items of `data/c230_split_items.txt` (plan estimate > 20 M, 3.1 G
in the plan, about 5 G real): prepare, 8 parts (16 above 35 M), final. It publishes to
`xfer/c230help/w<500+S>` and skips anything already published:

```bash
nohup python3 lean435/tools/c230split.py --index $S --of $N > ~/c230_s$S.log 2>&1 &
```

**Status and STOP:**

```bash
python3 lean435/tools/prod435.py status --plan $C230_PLAN     # with the exports above
python3 lean435/tools/prod435.py ctl --stop                   # xfer/c230/ctl
```

**Recommended fleet: 40-50 machines.**

| role | machines | what they do |
|---|---|---|
| owners | 34 (W = 34, I = 0..33) | from the largest item down |
| helpers | 10 (J = 1..10) | from the smallest item up |
| split | 6 (N = 6, S = 0..5) | about 18 items each, 1-1.5 h per item |

At 4 builds per machine (12 GB budget; a 7 M certificate peaks at 2.3 GB) the 44 prod435 machines give
about 176 kernel-hours per hour. That is **about 20-30 h of wall time** for about 3,300-5,300
kernel-hours, plus the tail.

With 40 machines, take 30 owners, 6 helpers and 4 split machines, and expect about 25-35 h.

Order:

1. start the split machines first, because their items are the long ones;
2. then the owners;
3. then the helpers.

## 6. Status of the pilot: all checks passed

All three certificates, including the split one:

- built with the kernel check;
- carry the fixed statement;
- were published on the new families;
- are counted by `prod435.py status`, which reports 3 certificates, 38.4 M hints and 2.45 CPU-h;
- were merged by `prod435.py merge` without conflicts.

`audit.py final` of `lean435/c230/C230Toy.lean` ran from the merged public `.olean` only:

- it opened exactly the three certificate interfaces;
- it opened nothing outside the clean directory and the toolchain;
- `toy_window` (which uses all three via `AllRefutedIV`) and `toy_narrow` have the axioms
  `[propext, Classical.choice, Quot.sound]`: AUDIT PASSED.

Rebuilds are byte-deterministic: pilot 2 built twice, with the same `.olean` sha256.

The container restarted once during part K6/K7. `splitfarm435.py part --k 6 --k 7` was re-run and
the already-built base modules were reused.

**Still open for the 230 theorem** (not certificate work):

1. port or regenerate the K7 chain (`WindowAutomatonK7R34C7W16*`) on 4.35;
2. the generated cover lemma from the chain's `wforb` tables to `AllRefutedIV` keys, with reuse of
   the 25,189 implied windows via `refuted_narrow` / `refuted_sub`;
3. the corner-share wrapper with its 132 `RefutedShare … 12 29` certificates (all UNSAT,
   `data/corner7_levels.jsonl`). These need the share route of prod435, not this plain plan.
