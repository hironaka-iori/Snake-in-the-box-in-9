# Certificate families for the 234 keys: prove families, not windows

Run of 9 November 2026, about 14:50 to 18:00, on one core at `nice -n 15`, peak RSS under 0.2 GB.
New disk use was under 5 MB. No proof was kept: every LRAT proof went through a FIFO into
`lrattrim`. One small Lean module was compiled into scratch. No lake build was run and no
existing `.olean` was touched.

**Question.** The 234 bound needs certificates for the **9,784 new keys** of
`../25-k7-234/data/keys_best234.json.gz`: 5,687 k6, 192 F8 and 3,905 H9. They carry **1.733 G
replay hints**, which the certify budget turns into about **138 CPU-hours and 5.8 GB of `.olean`**
(`families.budget`, the unit costs of `../25-k7-234/certify/README.md`). How much of this can
structure replace?

## Answer

| | certificates | hints | CPU-h | `.olean` |
|---|---|---|---|---|
| now (every key replayed) | 9,784 | 1.733 G | 137.7 | 5.82 GB |
| (a)–(d) on the key set as it is, existing lemmas only | 9,784 | 1.733 G | 137.7 | 5.82 GB |
| **L1** count-range widening of cores (`refuted_narrow`, **compiled**) | **4,918** | **1.529 G** | **111.7** | **4.82 GB** |
| **L1 + L2** widening + sub-window/reversal (L2 proposed) | **2,804** | **1.493 G** | **104.2** | **4.53 GB** |
| + pool keys as seeds (L1 + L2, §4) | 2,804 | 1.488 G | about 103 | about 4.5 GB |

- **Keys drop by 71 %, hints only by 14 %.** Structure removes thousands of cheap keys (mostly
  H9 and low-count k6 keys), but not the expensive ones. The 447 seeds above 1 M hints carry
  1.10 G, and their cores are *tight*: every window vertex and both counters of every centre are
  used. Nothing shares them.
- **The saving needs one small lemma and no new proof.** A key's UNSAT core often leaves out the
  counters of some centre, or one side of them. The same core and the same LRAT proof then prove
  the key with that centre widened, and the widened statement implies every sibling key inside it.
  The clause checker (`LocalWindowTags.ctrOK`) only reads the bounds of the counters that occur
  in the core, so the certificate is unchanged except for its `bounds` argument.
- **Merging siblings into one range CNF does not pay.** For 60 sibling runs among the expensive
  seeds, the box CNF cost **1.20×** the sum of its members (median 1.04, §3).
- **What is left** is about **1.49 G hints, 104 CPU-hours and 4.5 GB** in 2,804 certificates. The
  hints are now the floor for this key set: the 1.1 G in tight cores needs either a smaller pool
  of hard windows (an automaton question, not a certificate question) or cheaper proofs of the
  same windows.

## 1. Implication classes on the key set as it is (`classify.py` → `data/classify.json`)

| class | keys implied | hints | why |
|---|---|---|---|
| (a) sub-window of another key of the set | 355 (354 H9, 1 F8) | 0.44 M | 330 of the impliers are already certified (free) keys. The automaton keeps them because a step checks only the windows that end at the new vertex |
| (a′) sub-window of a known-UNSAT pool key (28,949 k6 + 86,775 F8/H9) | 1,375 have one, 347 cheaper | greedy cover saves 20 M (1.1 %) | |
| (b) reversal | 0 | 0 | k6 and F8 keys are already the minimum of both orientations; an H9 key and its reversal are different key kinds |
| (c) count ranges | 0 | 0 | the symbols are disjoint intervals (1..5 exact, 6 = 6..21), so no key narrows another; 6,466 sibling groups (6,970 keys) differ at one centre only, which is what §2 and §3 use |
| (d) cube symmetry beyond relabelling | 0 | 0 | an automorphism that fixes a window path fixes its directions up to the relabelling the canonical form already quotients; it can only permute unused coordinates, and the count `absentCorners` is symmetric in those |

So, **with the lemmas Lean already has, the seed set is the whole key set**: 9,784 keys, apart
from the 355 sub-window cases worth 0.44 M hints, which need L2. The monotonicity Lean has today
is the automaton's (a transition is dead if any sub-window is in the table, `rowOK6_mono`,
`refuted_extend` for a trailing uncounted centre). It acts on table coverage, not on
`Refuted` statements, so it cannot drop a certificate.

## 2. Shared obstructions from the UNSAT cores (`cores.py`, `families.py`)

**Cores.** All 9,784 keys were re-solved: radius-4 CNF of `k7.encoding`, lazy cycle cuts,
CaDiCaL `--seed=1 --unsat --lrat` through a FIFO into `lrattrim`. This took 1.3 CPU-hours. The
original clauses of the empty clause's cone were mapped to the clause families of
`wincert.Encoding` (`data/cores.jsonl.gz`: used window units, used `alpha>=` / `alpha<=`
counters per centre, cycle cuts, vertex support). All 9,784 are UNSAT. The full-CNF proofs total
3.20 G hints, 1.85× the replay estimates, as expected before the core-only portfolio.

**Widened key E(K).** At each centre, E keeps both bounds if the core uses both counters,
(lo, 21) if it uses only `alpha>=lo`, (0, hi) if only `alpha<=hi`, and (0, 21) (uncounted) if
neither. The window is trimmed to the used window units and the two path neighbours of every
centre still counted, since they fix its directions. Every core clause is sound for
`Axioms (winOf E) (centresOf E)`, so K's proof proves E at no extra cost.

- 9,366 of the 9,784 cores are widened somewhere. They leave 33,096 centre slots uncounted and
  19,325 one-sided, and 1,451 windows are trimmed.
- Centres E still counts: 1 (2,652 keys), 2 (901), 3 (1,957), 4 (1,953), 5 (1,753), 6 (513),
  7 (55).

**Implication.** E implies a key K2 when E's directions are, up to relabelling and in one
orientation of K2, a slice of K2's, and every range E still counts contains K2's symbol there.
The seed set is a weighted greedy set cover of the paid keys by the E(K), with cost = K's hints.

| lemma set | seeds | keys removed | hints removed |
|---|---|---|---|
| L1 only (same window and orientation) | 4,918 | 4,866 | 204 M (11.7 %) |
| L1 + L2 (any sub-window, either orientation) | **2,804** | **6,980** (3,594 k6, 82 F8, 3,343 H9) | **240 M (13.9 %)** |

**Top obstruction families** (L1 + L2; keys = covered keys including the seed). The top 10 families remove 72 M hints, the top 50 134 M,
the top 100 168 M, and the top 500 237 M of the 240 M.

| seed | E (directions; ranges, `*` = uncounted) | keys | hints removed |
|---|---|---|---|
| k6 012314 / 33546 | 012314; 3,3,5,4,`*` | 3 | 15.5 M |
| k6 012031 / 36444 | 012031; 3,`*`,4,≤4,4 | 21 | 10.7 M |
| k6 012314 / 36534 | 012314; 3,`*`,5,3,4 | 3 | 10.3 M |
| k6 012314 / 34536 | 012314; 3,4,5,3,`*` | 2 | 7.7 M |
| k6 012032 / 34446 | 012032; 3,4,4,4,`*` | 4 | 7.4 M |
| k6 0120324 / 444536 | 0120324; 4,4,4,5,3,`*` | 14 | 5.8 M |
| largest by keys: k6 012345 / 15633 | 012345; ≤1,`*`,`*`,`*`,`*` | 532 | 0.88 M |
| H 012314251 / 3661556 | 314251 (a slice); ≤1,`*`,`*`,`*`,`*` | 478 | 0.74 M |
| k6 0123042 / 155553 | 012304; ≤1,`*`,`*`,`*`,≤5 | 467 | 0.73 M |
| k6 0123415 / 454464 | 0123415; ≤4,`*`,`*`,`*`,`*`,≤4 | 392 | 0.83 M |

Two kinds of family show up:

- **Expensive keys.** These families are "a symbol-6 (6..21) centre does not matter". The core
  ignores that centre's counter, so one 1–12 M proof covers 2–20 siblings that differ only there.
  They carry most of the hints removed: families with 4 counted centres remove 128 M, with 5
  remove 70 M.
- **Cheap keys.** These are end-centre upper bounds on long windows ("the first interior vertex
  has at most one singleton square on window 012345"). Each covers hundreds of H9 and low-count k6
  keys, but they are cheap. Families with 1–2 counted centres remove 4,050 keys but only 9.5 M
  hints.

**Checks (`verify_e.py` → `data/verify_e.json`).** All 6,980 implications were re-checked by brute
force on explicit direction bijections, independently of `families.contains`: 0 failures. All 17
trimmed E's that cover other keys are UNSAT in their own radius-4 ball, so the standard
generator can certify them directly. The untrimmed ones are proved by K's own core.

## 3. Range ("box") keys (`box.py` → `data/box.jsonl`)

A run of siblings with consecutive symbols s..t at one centre is one key with the range
(lo(s), hi(t)). It is UNSAT iff every member is, and L1 gives the members. This was tried on the
60 runs with the largest hints among the remaining seeds, using the same full-CNF method on both
sides:

- box / sum of members: **median 1.04, geometric mean 1.09, aggregate 1.20**;
- 10 of 60 runs are below 0.8, and 2 are at 0.5;
- box / largest member: median 0.99.

The range CNF costs about what its members cost together, so the expensive siblings do **not**
share an obstruction. They are separate contradictions that happen to sit next to each other.
Not recommended, except per pair with a portfolio (no gain was measured on average).

## 4. Pool keys as seeds (`poolcand.py` → `data/poolcand.json`)

Could a cheaper known-UNSAT key *outside* the set, through its own widened core, imply one of the
expensive seeds? Candidates were taken for the 300 most expensive seeds (they carry 0.94 G):

- pool keys cheaper than the seed, whose window equals a slice of the seed's (either
  orientation), disagreeing at no more than 2 centres;
- that gave 2,518 candidates, of which 2,012 cores were extracted in the 40-minute budget, the
  best benefit/cost first (`data/pool_cores.jsonl.gz`).

**Result: 8 seeds replaced, net 4.9 M hints.** Typical case: the pool key with symbol 6 at a centre
ignores that centre, and so implies the seed with symbol 5 there. Even these 8 savings rest on
modelled costs (class means of 1.1–2.5 M). The expensive seeds are not implied by anything
cheaper that is known.

## 5. Proposed Lean lemmas

**L1 `refuted_narrow` (implemented: `lean/LocalWindowFamilies.lean`, compiled in scratch; axioms
`propext`, `Classical.choice`, `Quot.sound`).**

```lean
def widerB : List (Nat × Nat) → List (Nat × Nat) → Bool   -- pointwise ⊇ on wide's length
theorem refuted_narrow {W : List Nat} {wide narrow : List (Nat × Nat)}
    (h : Refuted W wide) (hw : widerB wide narrow = true) : Refuted W narrow
theorem refuted_key_of_wide {ds syms : List Nat} {wide : List (Nat × Nat)}
    (h : Refuted (winOf ds) wide) (hw : widerB wide (boundsOf syms) = true) :
    Refuted (winOf ds) (boundsOf syms)
```

Use:

- The 4,918 seed certificates prove `Refuted (winOf ds) E.bounds`, with the widened bounds of
  `data/seeds.json.gz`. Same core, same LRAT. `gen_lean_cnfsat` needs only explicit bounds, since
  `ctrOK` checks a counter against its centre's bound and the core has no counter of a widened
  side.
- Each of the 4,866 derived keys is one term `refuted_key_of_wide h (by decide)` in the
  `AllRefutedK7` chunks.
- `AllRefutedList`, the bridges and the automaton are unchanged.
- **Removes 4,866 certificates and 204 M hints (−26 CPU-h, −1.0 GB).**
- **Proviso.** The Lean core must be one that omits those counters. The certify pipeline
  (`cost234.replay_cost`) takes the core of the cheaper of the `--unsat` and default full runs,
  then a portfolio on that core. It must take the `--unsat` core used here, or recompute E from
  the core it keeps.

**L2 `refuted_sub` (proposed, not implemented).**

```lean
-- o = orientation, i = offset: the slice of (ds, syms) at i, reversed if o = 1, relabels onto cs,
-- and bounds is wider than its boundsOf on every counted centre (uncounted H9 centres -> (0,21)).
def subOK (cs : List Nat) (bounds : List (Nat × Nat)) (ds syms : List Nat) (o i : Nat) : Bool
theorem refuted_sub {cs ds syms : List Nat} {bounds : List (Nat × Nat)} {o i : Nat}
    (h : Refuted (winOf cs) bounds) (hok : subOK cs bounds ds syms o i = true) :
    Refuted (winOf ds) (boundsOf syms)
```

- **Route A** keeps `AllRefutedList` unchanged. It needs `Axioms` to be invariant under a cube
  automorphism `amap P t` for an arbitrary S, E, plus the slice. This is the generic analogue of
  the snake-specific `frame_axioms` (`LocalWindowBridge.lean`, about 400 lines with its Frame
  section). Estimated 300–400 lines.
- **Route B** works at snake level, for about 150 lines but with a bridge change. A key only needs
  "no snake window matches it". From `refuted_bridge` (already general in bounds), a lemma
  `canon (slice (canon l)) = canon (slice l)`, and `revSnake` for orientation, a derived key
  follows. `window_refute7` / `window_refuteH` then take an `AllFreeList` in place of
  `AllRefutedList`.
- **Removes another 2,114 certificates and 37 M hints (−7.5 CPU-h, −0.3 GB)**, plus the 355
  class-(a) keys.
- The 17 trimmed E's can be certified by the standard generator (UNSAT in their own ball);
  the rest by K's core renamed by the automorphism.

**Not proposed.**

- **Range keys** (§3): no hint saving.
- **Reversal and cube symmetry** (§1): nothing left to quotient.
- **A "union" lemma** (`Refuted W (b[i:=(a,m)]) ∧ Refuted W (b[i:=(m+1,c)]) → Refuted W (b[i:=(a,c)])`):
  it would only re-assemble what L1 takes apart, with no saving.

## 6. Remaining certificate cost

| plan | certificates | hints | replay + Cnf/Sat CPU | `.olean` |
|---|---|---|---|---|
| B234 as built | 9,784 | 1.733 G | 137.7 h | 5.82 GB |
| L1 (ready) | 4,918 | 1.529 G | 111.7 h | 4.82 GB |
| L1 + L2 | 2,804 | 1.493 G | 104.2 h | 4.53 GB |
| L1 + L2 + 8 pool seeds | 2,804 | 1.488 G | about 103 h | about 4.5 GB |

The derivations themselves cost one `decide` on short lists per key, a few ms each.

## Caveats

- Hints are the key-set estimates (measured for 0.40 G, modelled for the rest). The cores come
  from one CaDiCaL configuration, and another proof of the same key can use different counters.
- The greedy set cover is not optimal. Removing a key does not change the automaton or its
  table: every key stays in `AllRefutedK7`, it is only *proved* differently.
- L2 is specified, not built.

## Files

| file | contents |
|---|---|
| `classify.py` → `data/classify.json`, `data/siblings.json.gz` | classes (a)–(d), the pool cover, the sibling groups |
| `cores.py` → `data/cores.jsonl.gz` | cores of the 9,784 keys, mapped to clause families |
| `families.py` → `data/families.json`, `data/seeds.json.gz` | widened keys, implications, set covers (L1 only and L1 + L2), budget, top families; the seeds with their E and the keys each covers |
| `verify_e.py` → `data/verify_e.json` | brute-force re-check of the implications; own-ball solves of the trimmed E's |
| `box.py` → `data/box.jsonl` | the 60 range-key experiments |
| `poolcand.py` → `data/poolcand.json`, `data/pool_cores.jsonl.gz` | pool keys whose widened core implies an expensive seed |
| `lean/LocalWindowFamilies.lean` | L1 (`widerB`, `refuted_narrow`, `refuted_key_of_wide`, an example) |

Reproduce: `nice -n 15 python classify.py; python cores.py; python families.py; python box.py
--top 60; python verify_e.py 40; python poolcand.py --ham 2 --top 300 --budget 2400`. Compile
L1: copy the file into a scratch root and run
`LEAN_PATH=<scratch>/olean:work/final_lean/.lake/build/lib/lean lean -o <scratch>/olean/LocalWindowFamilies.olean LocalWindowFamilies.lean`.
