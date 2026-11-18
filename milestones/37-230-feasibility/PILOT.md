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
| `V012031A33555` (r 3) | prod435 | 5.09 M | 7.40 M | 1,113 s | 2.33 GB | 28 KB | see below |
| `V0120342A664435` (r 3) | split, 8 parts | 20.1 M | 30.8 M (core proof) | see below | see below | | see below |

Kernel cost on these two is **0.09-0.15 ms per hint**, below the 0.3-0.5 of the 231 share
certificates.

The plan underestimates large items by about 1.45x: 5.1 -> 7.4 M, and 20.1 -> 30.8 M. Small items are
overestimated: 0.30 -> 0.18 M. Per SPLIT.md, prod435 already schedules on the cores step's estimate,
not the plan's.

## 4. Status of the pilot (updated at the end)

(see section 5)
