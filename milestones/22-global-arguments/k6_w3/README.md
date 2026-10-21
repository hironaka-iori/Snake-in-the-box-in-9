# k6 + w_3: do the local ceilings near 230 survive six-centre windows?

Run of 21 October 2026, about 3.2 h on one core at nice 19, next to a Lean build. Solves ran one at a time. **Everything here is solver-side. Nothing is a Lean theorem, and no bound in the chain changes.**

Units are those of `../w3_survey`. The charge is c(x) = Σ_Q ⌊12/|Q∩S|⌋, and 12 c = 1 w_3. T5 and T6 are the minimum window charges of five-centre and six-centre windows. μ is the per-vertex mean of c, and the bound is m ≤ 7 + 63148/μ. The k = 6 boundary terms move this by less than 0.1 edge, and they have not been re-derived. The automaton is the radius-4 L7 k6 K5 automaton of `../../11-local-ceiling/k6_loop`: 61,999 nodes and 1.0 M edges, with all plain α exclusions of milestones 10 and 11 plus 79 new ones (`data/plain_k6w3.jsonl`).

## Answer

| question | answer | status |
|---|---|---|
| (a) Does the w_3 ceiling cycle (period 6, 8497/6, m ≤ 229.95) survive k = 6? | **No.** Its k6 lift is unique, and its three distinct 6-windows (`0123014/3,4,5,4,3,5`, `0123042/3,5,3,4,5,4`, `0123014/4,3,5,3,4,5`) are **plain-UNSAT**. No w_3 charge is needed. | CaDiCaL 2.1.3 DRAT, **drat-trim VERIFIED** (3.7–14.5 MB, under 3 s each) |
| Does it survive k = 7? | No. Every 7-window contains one of those 6-windows. | follows |
| Witnessed sub-automaton (the 20 keys with SAT witnesses in w3_survey) | It has **no k6 cycle**. | rigorous |
| Next binding cycle (completion search, `ceil.py 1420 300`) | It is again period 6, the same shapes with one α = 5 replaced by 6+. The α pattern is 4,3,5,3,4,6+ on shapes 012301/012304/012034/012310. Its 6-windows are plain-SAT. The 5-window witnesses are 1403, 1424, 1462 and 1471, which gives λ = 1441 and **m ≤ 226.1**. | rigorous ceiling for "k ≤ 6 exclusions + T5 charges" (SAT witnesses) |
| Does that cycle survive k = 7? | **No.** At 5 of its 6 positions, every 7-window extension is plain-UNSAT. That is 4 keys, for example `01203420/4,6+,4,3,5,3,4`. | DRAT, **drat-trim VERIFIED** (2.4–51 MB, under 12 s) |
| T6 (6-window w_3) on that cycle | Its three 6-keys have minima 1744 (lb 1739), 1769 and 1769, all exact. That gives μ = 293.4, against 288.2 from T5, so **m ≤ 222.2** on this cycle. | solver-side (symmetry breaking on) |
| What-if: untested 5-windows force max(lb, F), on the k6 automaton | F = 1420: 229.84 → 229.44 over 10 rounds (the cap is 229.35). F = 1440: 227.78 → **227.39** over 10 rounds, still rising. The same what-if at k5 stopped at the 229.95 ceiling. | heuristic |
| (b) The plain k6 route's final cycle (μ_α = 65/16, 16 edges) | Its 9 distinct 5-windows have T5 = 1443–1491, exact for 7 of the 9. One key has only a witness (1567). μ ≤ 294.3, so w_3 gives **m ≤ 221.5** on this cycle. Its 6-windows are all plain-SAT. | witnesses, mostly exact minima |
| Rigorous lower side, T5 lbs on k6 | λ = 21685/16, μ = 271.06, m ≈ 240.0. The k5 value is 240.3. 14 of the 16 binding windows are untested (DP floor). | solver-side |

## What this says

1. **Both "about 230" ceilings come from five-centre windows.**
   - The w_3 ceiling cycle dies at k = 6 by plain α exclusions alone, as the share route's period-3 cycle did (`../../11-local-ceiling/s0_k6_ceiling`).
   - The next witnessed cycle survives k = 6 at 226.1, then dies at k = 7.
   - The α route's own binding cycle (65/16) is harmless for w_3: there, m ≤ 221.5.
2. **The two charges bind on different cycles.**
   - The w_3-binding cycles (the period-6 family with α of about 4.2) are mediocre for α: about 234.
   - The α-binding cycle is easy for w_3.
   - A linear mix `A·(α+35)/9171 + c/63148` on the 1441 cycle only interpolates between 226 and 234, so mixing in α weights does not help.
   - The useful combination is **α exclusions (k6 automaton) with w_3 weights**, which is what was measured here.
3. **The ceiling for k6 + T5 lies between 226.1 (rigorous) and about 227.4–229.4 (what-if, F = 1440 / 1420).**
   - 59 new 5-window witnesses came from 60 s budgets and are unminimised. None is below 1420, and 8 are below 1440.
   - The low witnesses (1393–1424) all belong to the period-6 family.
   - So the realistic solver-side target for k6 + T5 is **about 228**, with full key coverage at T ≈ 1420–1440.
4. **Six-centre w_3 charges are clearly stronger.** On the surviving cycle, T6/6 exceeds T5/5 by 5.2 c per vertex, which is about 4 edges. The 6-window threshold CNFs are about 41 k variables and 1.77 M clauses, with RSS ≤ 750 MB. Their single tests take 1–15 s, like the 5-window ones.

## Recommendation

**k6 + w_3 is not yet clearly below 230 rigorously.** It is the best-placed local route, though: there is no known obstruction above 226 at k = 6, and the period-6 obstruction dies at k = 7.

Do not formalise it yet. Its certificate count (about 10^4 threshold keys) is the w3_survey cost, about 600 kernel-hours at the mean.

Next solver step, about 3–4 CPU-hours: run a **k6 loop with T6 weights**, with plain k ≤ 7 exclusions only where a binding cycle needs them. Then decide on Lean once the lower side passes μ ≈ 282, which corresponds to 230. Keep k6 plain (A, 235) as the formalisation in progress.

## Files

- `k6w3lib.py`: loaders (k6 graph, merged plain statuses, merged w_3 oracle).
- `cert.py`: lazy cuts, cold CaDiCaL DRAT, drat-trim. Results are in `data/certs.jsonl`, with CNF SHA-256 hashes; the proofs were deleted.
- `ceil.py`: what-if and completion search on the k6 automaton with T5 weights, including the witness descent (`data/rounds_*.jsonl`).
- `k7.py`: 7-window extensions of the minimum witnessed cycle (`data/k7_F1420p300.json`).
- `t6.py`: six-centre w_3 minima.
- `plainA.py`: part (b) (`data/plainA_cycle.json`).
- `evallo.py`: the rigorous lower side (`data/evallo.json`).
- `data/w3_k6_oracle.jsonl`: every new w_3 call (5- and 6-window), in w3survey record format.
- `data/plain_k6w3.jsonl`: new plain calls.
- `data/*.log.gz`: run logs.
