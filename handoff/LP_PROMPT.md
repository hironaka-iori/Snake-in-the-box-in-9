# Prompt: break the local ceiling by combining global identities (LP over local frequencies)

Paste everything below the line into a Claude Code session (cloud or local) on a clone of
https://github.com/hironaka-iori/Snake-in-the-box-in-9, branch `research/unconditional-241`.

---

You are a research mathematician and engineer working on the Lean 4 project
https://github.com/hironaka-iori/Snake-in-the-box-in-9, branch `research/unconditional-241` (never push to
`main`, never open a pull request; `main` belongs to another contributor and may be read with
`git show origin/main:<path>`). The project bounds a(9), the longest snake (induced path) in the 9-cube Q9.
Lean-checked today: **191 <= a(9) <= 233**. A 234 build is prepared but expensive (`handoff/README.md`).
Code, comments, commits and READMEs in English; reply to the user in Chinese.

## Why this task

Every upper bound so far has the same shape: one global counting identity of the form
`sum over snake vertices x of g(x) <= A - B * v` (v = number of vertices), plus SAT-certified local window
exclusions, plus a direction automaton whose minimum cycle mean lower-bounds the average of g along the
snake. Each step down costs about ten times more certificates (237: 34 kernel-hours; 236: 100; 234: about
300 plus over 100 GB of disk), and each identity used alone stalls near 230:
- alpha (singleton-square counts) with T + 35v <= 9214: five-centre ceiling about 230, six-centre plain
  ceiling 235.35 (`milestones/11-local-ceiling/`, `milestones/23-k6-lean/share_bonus/README.md`);
- the corner share s0 with sum(24 alpha + share) + 840(m+1) <= 221136 (`work/spectral/ShareCharge.lean`,
  `work/spectral/stronger/ShareBridge.lean`, `milestones/11-local-ceiling/s0_*`);
- the 3-cube census w3 with sum c(x) <= 64512, m <= 7 + 63148/mu (`milestones/22-global-arguments/`,
  `w3_survey/`, `k6_w3/`, `k6_w3_loop/`);
- the three-square share bonus and the share-16/17 floors proved on `main`
  (`milestones/35-equality-share-bonus`, `milestones/152-*`, `milestones/155-share17-replay` on `origin/main`).
They have never been used **together**. Their binding cycles differ: on the k6 plain route's final cycle
(alpha mean 65/16) the w3 minima give m <= 221.5, while alpha is mediocre on w3's binding cycle
(`milestones/22-global-arguments/k6_w3/README.md`). That complementarity is the opportunity.

## The idea, precisely

Fix a target m. A snake of length m induces an empirical distribution mu over its local windows (the
automaton's states and transitions), which is shift-consistent up to O(1/m) boundary terms, supported on
windows not excluded by any certificate. Each identity i gives a linear constraint `E_mu[g_i] <= c_i(m)`.
If the LP {mu >= 0, sum mu = 1, flow conservation, support restrictions, E_mu[g_i] <= c_i(m) for all i} is
infeasible, no snake of length m exists. Its Farkas dual is a nonnegative combination y of the identities.
The combined weight w = sum_i y_i g_i is then an ordinary edge weight on the SAME automaton, so the Lean
certificate is the existing framework with combined weights: a potential plus a min-mean-cycle check
(`work/spectral/stronger/WindowAutomaton{5,6,7}Defs.lean`, `AggregateDirection*Conditional.lean`), plus a
short lemma adding the identities with coefficients y. The alpha-only case must reproduce today's bounds;
use that as a sanity check.

## Stages

### A. Inventory (no computation)
Read `README.md`, `handoff/README.md`, `milestones/11-local-ceiling/README.md` (adversaries 208/224 and the
local ceiling), `milestones/22-global-arguments/README.md`, `milestones/23-k6-lean/{README.md,
full_product/README.md}`, `milestones/25-k7-234/README.md`, `milestones/24-cycle-realizability/README.md`,
and on `origin/main` the README and RESEARCH_LEDGER heads plus milestones 35, 152 and 155. For each identity
write down:
- its exact Lean statement and file;
- its per-vertex or per-window quantity;
- which window data already bound that quantity: oracle and certificate files in `milestones/*/data`, such
  as `k6_loop/oracle_*.jsonl`, `k6_w3*/data/*oracle*`, `s0_share_loop/share_oracle.jsonl` and
  `25-k7-234/data/oracle*`.
Note which bounds are certified (DRAT- or Lean-checked) and which are only solver results.

### B. LP prototype in Python (the main deliverable)
- Automaton and graph: use the six-centre full product of `milestones/23-k6-lean` (264,384 states, its
  `transitions()` in `milestones/23-k6-lean/scripts/gen_lean_automaton6.py`) with the known exclusions
  (about 28.6k plain-UNSAT keys). Also run the k7 product of milestone 25 if memory allows.
- Weights per edge: alpha (exact, from the state); share and w3 lower bounds from the existing oracles (use
  0 where unknown, so the result stays a valid lower bound on what a certified version would give); the
  share-16/17 and three-square floors where their patterns match.
- Solve the min-mean-cycle problem for a combined weight sum_i y_i g_i, optimised over y >= 0. Use the
  Lagrangian or parametric form, so you do not need to materialise the full LP:
  for given y, the bound is min over i-mixtures, via Howard / Karp min mean cycle on the product. Then do
  subgradient, bisection or a small outer LP over y. Derive the exact final arithmetic: how m follows from
  the combined inequality, including the endpoint terms and the potential range as in the existing
  `total_bound6`/`total_bound7`.
- Sanity checks:
  - y = alpha only must give 235 on keys_235 and 234 on the k7 keys_best234;
  - w3-only must agree with the k6_w3_loop numbers.
- Report the best m reached with only already-certified window data, and the best m reachable if the
  solver-only data were certified.

### C. Ceiling of the combined method
Find the binding cycle of the best combination. Check whether its windows have SAT witnesses for every
quantity involved; if they do, that is the ceiling of this automaton. Test the known adversaries
(208/224 in milestone 11) against the combined weight. Estimate how far 5-, 6- and 7-centre windows with
combined weights can go.

### D. Certification plan, only if B or C beats 234
- List exactly which new window certificates the optimum needs (share or w3 threshold certificates and
  plain exclusions).
- Cost them with the measured models: hints ≈ 1.49e6 · t^0.843; packed replay ≈ 2.9 B/hint; Cnf/Sat ≈ 50
  KB per core (`milestones/26-replay-efficiency/README.md`).
- Design the Lean glue that combines identities with coefficients y. Prototype it on a toy instance in
  scratch (one `lean -o` at a time), using only standard axioms.

### E. Optional, if time remains
1. Certificate families: classify the 9,784 new keys of the 234 set (`milestones/25-k7-234/data/keys_best234.json.gz`)
   by obstruction (common sub-window, count monotonicity, symmetry), and estimate how many seed
   certificates plus structural lemmas would replace them.
2. Global Q8 layering: estimate g8(c), the maximum total length of an induced linear forest with at most c
   paths in Q8 (`milestones/22-global-arguments/README.md`, layers section). Start with exact small cases
   (Q5–Q7) and an SAT- or ILP-based upper bound for Q8, since this is the one route known to escape the
   local ceiling.

## Rules
- Standard axioms only in anything committed (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no
  `native_decide`. Solver results are evidence, not proof: say which numbers are certified.
- Never run a plain `lake build` over certificate modules; use `work/guarded_lake_build.py --direct
  --trust-mtime` if you build anything, and never recompile existing base modules. In scratch tests,
  `LEAN_PATH` lists the scratch output before `work/final_lean/.lake/build/lib/lean`.
- Run solvers and Python at modest priority (`nice`), keep memory within the machine (check `free -g`),
  delete proofs after measuring them, and watch the disk (`df -m /`).
- Kill processes only by PID (pgrep or pkill patterns can match your own shell). Use nohup and a PID file
  for long jobs, and checkpoint results to files.
- Sub-agents are allowed. Give each one a disjoint task and its own scratch directory.
- Git: commit scripts, small data and an English README under `milestones/28-combined-identities/`; never
  commit large data (gzip anything above a few MB). `git pull --rebase origin research/unconditional-241`
  before each push; commit only your own paths. Do not edit `README.md`, `COLLABORATION.md` or `paper/`.
  End each commit message with:
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`

## Report (in Chinese, under 400 words)
- The best y and the bound it gives, with certified data only and with solver data.
- The sanity-check results.
- The binding cycle and the ceiling of the combined method.
- If below 234: the certificate list, cost and Lean plan.
- What stages A–E found.
