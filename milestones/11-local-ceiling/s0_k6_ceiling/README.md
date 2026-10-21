# Breaking the s0 share ceiling with six-centre windows

Run of 21 October 2026 (about 2 h of one core at nice 19, next to a Lean build). Everything is solver-side; nothing here is a Lean theorem. Units, the automaton and the thresholds are those of `../s0_share_loop/README.md`: M = 12, W(e) = 120·sym + T5, μ = λ/120, m ≤ 9171/(μ+35), so 230 needs μ > 4.701, 229 needs μ > 4.874, 228 needs μ > 5.048 and 227 needs μ > 5.224.

## Answer

| question | answer | status |
|---|---|---|
| Does the period-3 all-α=4 ceiling cycle survive k = 6? | **No.** Both of its 6-windows are plain-UNSAT at radius 4. No share charge is needed. | CaDiCaL 2.1.3 DRAT proofs, **checked by drat-trim** |
| Does it survive k = 7? | No. Every 7-window contains one of those 6-windows. | follows from the k = 6 result |
| Does it survive radius 5 with k = 5? | **Yes.** Both 5-windows are SAT at radius 5, with share witnesses 94 and 71, the same as at radius 4. | SAT witnesses |
| Do exact M = 2520 shares remove it? | No. The radius-5 witnesses have exact shares 21216/2520 and 15696/2520, which gives μ ≤ 4.769 and m ≤ 230.6. | SAT witnesses |
| What is the new ceiling after k = 6 exclusions? | **None below 222 is known.** Every fully witnessed cycle of the old data dies at k = 6. The lowest fully witnessed cycle found has μ = 6.207 (m ≤ 222.6). | rigorous, but loose |
| Heuristic value of the route | With untested 5-windows assumed to force F = 108, the minimum is **≥ 4.94 and still rising** (m ≤ 229.6). | not rigorous |
| Rigorous lower side | Unchanged at 4.1034 (m ≤ 234). The binding lo cycle still consists of untested windows. | solver-side |

**Summary.** Radius 5 and M = 2520 cannot move the 230 ceiling, but six-centre windows remove it outright, together with every other low periodic pattern we could witness. Of the 375 six-windows tested on low cycles, 234 are plain-UNSAT (62 %). The local share route at k = 6 therefore has no known obstruction above 222 edges. Its plausible value, under the share loop's usual "untested windows force about 108" assumption, is **229 or better**. Whether 228 or 227 is reachable is open. It depends on the lower side, which needs the full share-aware refinement, now on a larger automaton.

## 1. The ceiling cycle and its lifts (`recon.py`, `k6lib.py`)

The optimistic minimum cycle of the share loop (round 113, μ_hi = 1699/3 / 120 = 4.7194) passes through three states. Each state has 7 canonical directions and 4 counts:

| from | to | sym | 5-window key | T5 |
|---|---|---|---|---|
| (0,1,2,3,4,1,2) | (0,1,2,3,0,1,4) | 4 | (0,1,2,3,0,4), α 4×5 | exactly 94 |
| (0,1,2,3,0,1,4) | (0,1,2,3,0,4,2) | 4 | (0,1,2,3,0,4), α 4×5 | exactly 94 |
| (0,1,2,3,0,4,2) | (0,1,2,3,4,1,2) | 4 | (0,1,2,3,0,1), α 4×5 | witness 71 |

Any real direction sequence that follows the cycle has the form ... (N[j+1], N[j], N[j-1]), (N[j+2], N[j+1], N[j]), ... In each block of three steps, one direction is new and the other two repeat the direction four steps back, with N[j] ∉ {N[j-1..j-4]}.

- **6-windows.** A 6-window uses 7 consecutive directions. These are exactly the target state's 7 remembered directions, so the 6-windows are unique for every lift. There are two keys: (0,1,2,3,0,1,4) and (0,1,2,3,0,4,2), both with α = 4 at all six centres.
- **7-windows.** These depend on the lift. The fresh-direction lift gives (0,1,2,3,0,1,4,3) and (0,1,2,3,4,1,2,5). The lift with N[j+1] = N[j-4] gives (0,1,2,3,4,1,2,0).
- **Long lifts.** The lift N[j] = j mod 9 is an induced path for 52 steps, so the direction pattern alone is not contradictory.

## 2. Tests (`runk6.py`, `certk6.py`; `results.jsonl`, `certs.jsonl`)

| window | k | r | test | result | time |
|---|---|---|---|---|---|
| (0,1,2,3,0,1,4), α 4×6 | 6 | 4 | plain | **UNSAT** (DRAT 38.7 MB, drat-trim VERIFIED) | 8 s |
| (0,1,2,3,0,4,2), α 4×6 | 6 | 4 | plain | **UNSAT** (DRAT 17.1 MB, drat-trim VERIFIED) | 4 s |
| (0,1,2,3,0,1), α 4×5 | 5 | 4 | plain | SAT, share 97 (control) | 4 s |
| (0,1,2,3,0,4), α 4×5 | 5 | 4 | plain | SAT, share 111 (control) | 4 s |
| (0,1,2,3,0,1), α 4×5 | 5 | 5 | plain / share ≤ 71 | SAT / **SAT, witness 71** (exact M = 2520: 15696) | 1 s / 57 s |
| (0,1,2,3,0,4), α 4×5 | 5 | 5 | plain / share ≤ 94 | SAT / **SAT, witness 94** (exact M = 2520: 21216) | 9 s / 31 s |

The two CNFs are the static `wincert.Encoding` clause sets after lazy cycle cuts; neither needed a cut. Their SHA-256 hashes are in `certs.jsonl`. Proof files were deleted after checking.

Monotonicity: a radius-5 model, or a 7-window model, restricts to a model of the radius-4 6-sub-window.
- Interior vertices stay interior, and their degrees are unchanged.
- The square, cube, degree, cycle-cut and α clauses are all inherited.

So the radius-4 UNSAT also covers k = 7 and the radius-5 6-windows. At radius 5 the window (0,1,2,3,0,4) has minimum share exactly 94, because the minimum can only grow with the radius.

Three further 6-window exclusions were also DRAT-checked. They kill the next binding cycles of the loop's witness data:
- (0,1,2,3,0,4,2) with α 3,6+,3,3,6+,3 (46 cycle cuts);
- (0,1,2,3,0,1,4) with α 3,3,5,4,4,5;
- (0,1,2,3,0,4,2) with α 3,5,4,4,5,3.

## 3. The k = 6 automaton and its ceiling (`ceil6.py`, `ceilF.py`, `evalR.py`, `evalLo.py`)

**Construction.** The L7 k6 automaton is the k5 automaton with one more remembered count: states are (k5 state, a0). A k5 edge v → w becomes (v, a0) → (w, v.α[0]). Its 6-window key is key(w.dirs, (a0,)+v.α+(new,)), which is well defined (§1). After the share loop's exclusions it has 54,840 states, 846,880 edges and about 110k 6-window keys. Edge weights stay 120·sym + T5, so 6-windows are used only as plain exclusions. 6-window share charges (144·sym + T6) are evaluated as well, in `evalR.py`.

**Witnessed sub-automaton (`ceil6.py A`, `rounds_A.jsonl`).** This uses only 5-windows that already carry a witness. Removing the k = 6 UNSAT windows moves the ceiling 4.7194 → 4.7722 → 4.8306 → 4.8333 → 4.8869 → 4.9220 → 5.5341 → 5.6941. After that no witnessed cycle is left. The second and third binding cycles were also period-3: α (3,6+,3) and (3,5,4,4,5,3). Both died at k = 6.

**Full automaton, guess search (`ceilF.py 108 … 0`, `rounds_F108_p0.jsonl`).** A 5-window without a witness is weighted max(108, proved lb). Each round tests the windows of the minimum cycle:
- 5-windows: a plain solve, then a threshold test at min(ub, 108), exactly as the loop does;
- 6-windows: a plain solve.

Over 20 rounds the minimum rose 4.760 → 4.793 → 4.824 → 4.863 → 4.900 → 4.922 → 4.937 (m ≤ 229.64) and had not converged. This is the share loop's what-if at F = 108, now with k = 6. Without k = 6 the same what-if stopped at the 4.7194 ceiling.

**Completion search (`ceilF.py 108 … 120`, `rounds_F108_p120.jsonl`).** Windows without a witness get a +120 search penalty, which steers the search toward cycles that can be completed. Over 53 rounds its candidate cycles had means between 5.26 and 5.68, but tests at k = 6 kept breaking them.

`evalR.py` then takes the minimum over cycles whose every 5-window has a witness and whose every 6-window is SAT (`rigorous_ceiling.json`). The result is a 14-edge cycle with α (6+,5,3,4,3,3,6+,5,6+,3,3,4,3,5):
- 5-window share witnesses: μ = 5214/7/120 = **6.207**, m ≤ 222.6;
- 6-window share witnesses: μ = 6.745.

These witnesses are unminimised plain models, so the bound is loose. It shows only that **no known pattern stops the k = 6 route above 222**.

**Rigorous lower side (`evalLo.py`).** The minimum of 120·sym + proved T5 is 14280/29 = 4.1034 (m ≤ 234.5), with or without the 234 k6 exclusions. Its 29-cycle consists entirely of untested windows, as in every round of the share loop.

**Totals.**
- 6-window calls: 663, of which 234 distinct keys are UNSAT and 141 SAT. The 663 includes repeats of keys cut short by restarts.
- New radius-4 5-window calls (`oracle5_extra.jsonl`): 588.
  - plain: 178 UNSAT, 201 SAT, 6 timeouts;
  - threshold: 62 UNSAT, 53 SAT, 88 timeouts at 30–60 s.
- 6-window plain solves take 0.0–9 s and have about 4k variables and 68k clauses. They are much cheaper than the 5-window share tests.

## 4. Consequences for the share route

1. The 230 ceiling is an artefact of k = 5. Radius 5 and exact shares do not remove it, but six-centre plain exclusions do, cheaply. The proofs are 7–39 MB DRAT, 1–12 s each. For Lean, the 236/237 replay chain already handles plain exclusions at this size.
2. The next cheap step is to rerun the share loop on the L7 k6 automaton: 6-window plain exclusions, plus 5-window share charges. Charge 6-window shares only where the lo cycle demands it. On the hi side, 62 % of the tested 6-windows are infeasible. This suggests the k = 6 automaton is much tighter than k = 5 on the lo side too. That has not been measured: the lo cycle is still all untested.
3. **Implied best bound for the local share route, k = 6, radius 4, M = 12.**
   - Proved solver-side: m ≤ 234, unchanged.
   - No obstruction known above 222.
   - Heuristic: 229, under the F = 108 assumption, with the guess search still rising.
   - 228 needs μ > 5.048, and 227 needs μ > 5.224. Both remain open: they are not excluded, and there is no evidence for them yet.

## Files

- `k6lib.py`: lifts of the cycle and their k-windows.
- `recon.py`: rebuilds the ceiling cycle from the loop's data.
- `runk6.py`: single plain or threshold tests, for any k and radius, with all α = 4. It appends to `results.jsonl`.
- `certk6.py`: lazy cuts, then a cold CaDiCaL binary run with DRAT, then drat-trim. The proof files are deleted after the check, and the result goes to `certs.jsonl`.
- `ceil6.py`: the k6 automaton on witnessed edges only (mode A), plus the 6-window oracle `oracle6.jsonl`.
- `ceilF.py`: the full k6 automaton, the guess search and the completion search. New 5-window calls go to `oracle5_extra.jsonl`, which is in the same record format as `../s0_share_loop/share_oracle.jsonl`.
- `evalR.py`: the rigorous witnessed ceiling, written to `rigorous_ceiling.json`.
- `evalLo.py`: the rigorous lower side.
- `ceilA.log.gz`, `ceilF.log.gz`: run logs.

The automaton cache comes from `../s0_share_loop/refine_share.load_compact`, which rebuilds it from the radius-4 oracle cache when it is missing.
