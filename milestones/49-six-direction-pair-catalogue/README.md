# Complete survey of low two-count restrictions on six-direction segments

## Question and outcome

The working hypothesis was that a complete family of short two-count restrictions would exclude the low-charge sequences missed by individual cycle tests. The survey examines every six-direction induced-path shape, up to coordinate relabelling and reversal, and every pair of its five internal positions. The four tested cap pairs are $(2,2),(2,3),(3,2),(3,3)$.

There are nine shapes and 360 instances. All instances were resolved: 50 are excluded, and 310 have saved acyclic local configurations. The 50 negative rows reduce to 34 maximal cap combinations and 33 distinct shortened basis statements. No timeout is counted as an exclusion.

**Proof status:** all 33 basis replays, all 50 survey deductions, the stronger four-step return inequality, and its complete-snake sharpness witness passed Lean. All 159 dependency audits use only propositional extensionality, classical choice and quotient soundness. The independent verification receipt is `data/verification.json`; it also checks 747 positive local configurations, 131 complete bank paths and 123,771 oriented basis-pattern occurrences. Pattern-occurrence totals include different inequalities applied to the same segment.

## Mathematical statements

Let $\alpha_i$ be the number of coordinate squares whose intersection with a snake is exactly $\{x_i\}$. Positions in the table are offsets from the start of the displayed direction segment. Digits label distinct coordinates, rather than fixed coordinate values. An entry $(i,j):(u,v)$ means that the simultaneous bounds $\alpha_{r+i}\leq u$ and $\alpha_{r+j}\leq v$ are impossible.

The table lists the maximal forbidden cap combinations within the tested four-pair domain. A row also excludes coordinatewise smaller bounds. Other counts and endpoint distances are unrestricted.

| Direction shape | Maximal excluded cap combinations |
|---|---|
| `012031` | $(1,3):(2,2)$, $(1,4):(2,2)$, $(1,5):(2,3)$, $(1,5):(3,2)$ |
| `012032` | $(1,3):(3,2)$, $(1,4):(2,3)$, $(2,4):(3,3)$, $(2,5):(3,2)$, $(3,5):(2,3)$ |
| `012034` | $(1,3):(3,2)$, $(1,4):(2,2)$, $(1,5):(2,3)$, $(2,4):(2,2)$ |
| `012301` | $(1,5):(2,2)$ |
| `012304` | $(1,5):(2,3)$, $(1,5):(3,2)$, $(4,5):(2,2)$ |
| `012310` | $(1,2):(2,2)$, $(1,3):(3,2)$, $(1,4):(2,2)$, $(2,4):(2,3)$, $(2,4):(3,2)$, $(2,5):(2,2)$, $(3,5):(2,3)$, $(4,5):(2,2)$ |
| `012314` | $(2,4):(2,2)$ |
| `012340` | $(1,2):(2,2)$, $(1,5):(2,3)$, $(1,5):(3,2)$, $(4,5):(2,2)$ |
| `012345` | $(1,2):(2,2)$, $(1,5):(2,3)$, $(1,5):(3,2)$, $(4,5):(2,2)$ |

Each excluded survey row has an explicit arbitrary-coordinate theorem. The generated deductions connect its count bounds and segment to a checked basis exclusion, including the two cases whose unnecessary outer directions were removed. The basis uses radius-four degree, endpoint, square and selected-cycle constraints; joint-cardinality soundness is needed only for the additional return inequality.

### Four-step return inequality

For distinct coordinates $a,b,c$, the transition pattern $(a,b,c,a)$ satisfies

$$\alpha_{r+1}+\alpha_{r+3}\geq5.$$

This strengthens the basis exclusion that both counts cannot be at most two. The proof assumes the sum is at most four, represents the two opposite-corner counts with a multiplicity-preserving joint counter, and derives a checked contradiction. It then applies the arbitrary-snake geometric bridge and coordinate normalization. A complete 146-edge snake attains the bound: at segment start $r=95$, its counts are $\alpha_{96}=2$ and $\alpha_{98}=3$. Lean checks all vertex pairs, the transition pattern, the two counts, and the implication that any universal constant for this pattern is at most five. Thus five is the exact best constant for this inequality. This sharpness result does not determine the longest snake in $Q_9$. In the 131-path bank, 8,982 oriented occurrences have minimum observed sum 12; that observation does not justify a stronger universal constant.

## Effect on the finite graph

Applying the complete low-cap catalogue in both orientations and at every represented subsegment removes 528,610 additional transitions from the milestone 48 graph. There remain 3,855,773 transitions on the same 1,586,304 states. The exact normalized minimum remains **42/11**, attained by a new eleven-step cycle. A matching integer potential has range 7,728 and satisfies

$$7056+\pi(v)\leq11w(u,v)+\pi(u)$$

on every retained transition. The graph update uses the 33 basis exclusions. The stronger return-sum inequality is recorded separately; the attaining cycle also satisfies it.

The attaining cycle uses only counts two through five, with zero recorded excess demand and zero recorded share events. Its persistence cannot be explained by the capped symbol six. This does not assert that an actual snake with those counts exists, nor that its true empty-square contribution is zero.

The complete Lean bridge from this graph to arbitrary snakes remains pending. The integrated global interval stays **191 <= a(9) <= 236**. No 192-edge witness or exact optimum has been obtained.

## Why more two-count cap tests on six-direction windows are insufficient here

The attaining cycle has 330 pair-position occurrences across its six-direction subsegments, reducing to 104 distinct queries. Every query has a saved acyclic local configuration with both counts at most the corresponding cycle values. This includes caps four and five, beyond the original survey domain.

Within this precise necessary-condition model, no valid exclusion of the form $\alpha_i\leq A$ and $\alpha_j\leq B$ on a six-direction window can eliminate one of these cycle occurrences: any such upper-bound rectangle containing the cycle values also contains the recorded witness counts. This conclusion is about the stated local model and monotone pair-cap exclusions. It does not cover stronger connected-path conditions, exact-value exclusions, arbitrary weighted inequalities, or longer segments. The positive local witnesses may have several components and are not complete snakes.

The result redirects the next investigation toward restrictions involving three counts or longer windows. It does not establish a limitation on all mathematical methods.

## Comparison for the next round

Two bounded surveys use the replacement cycle's actual count caps:

| Context | Distinct tests | Local witnesses | Solver exclusions | Unknown |
|---|---:|---:|---:|---:|
| Six directions, two counted positions | 104 | 104 | 0 | 0 |
| Six directions, three counted positions | 109 | 92 | 17 | 0 |
| Eight directions, two counted positions | 222 | 214 | 8 | 0 |

The three-count exclusions cover eight of the eleven phases; the longer two-count exclusions cover five. These new scout exclusions have not been replayed in Lean. The next priority is a short three-count theorem with useful coverage, rather than extending the pair-cap table on the same six-direction model.

One promising numerical exclusion has directions $(a,b,c,d,e,a)$ and caps four at offsets 1, 4 and 5. A joint-sum test over these positions excludes sum at most 11; the sum-at-most-12 test returned UNKNOWN after its time limit. Thus the current evidence does not establish a sum bound of 13.

## Verification and reproduction

`scripts/survey.py` recursively enumerates the shapes and solves all 360 instances. `shorten.py` removes unnecessary outer directions from maximal exclusions. `certify.py` generates the ordinary clause cores, including any required cycle cuts; use `--force` to regenerate previously exported certificates. `wrappers.py` and `catalogue.py` state the arbitrary-coordinate basis results and derive all 50 negative survey rows in Lean. `replay.py` checks independent certificate chains with two workers and records each successful source hash.

`return_probe.py`, `return_certify.py` and `return_replay.py` establish the additional joint-sum result. `full_return.py` finds its full-snake sharpness witness; `return_witness.py` checks the witness and optimality of the constant in Lean. Its build receipt is separate and uses the same build directory. `archive.py` preserves exact proof files in lossless compressed form.

`controls.py` independently checks all saved positive local configurations, their counts, degrees, endpoint budget and absence of selected cycles, as well as all 131 complete bank paths and their basis-pattern occurrences. `verify.py` checks every negative proof's clause provenance, Lean dependencies, source/build correspondence, the full survey coverage, an independent direct-product enumeration of all six-direction shapes, every retained graph edge and the attaining cycle. Positive witnesses and shape enumeration are checked in Python; they are not described as Lean proofs.

`next_pairs.py`, `context_comparison.py` and `next_sum.py` record the next-step comparisons. Numerical discovery and checked theorem status remain separate.

This is research round **3 of 5** after manuscript revision 46. The paper and its existing editor mirror are unchanged. GitHub was refreshed before and after the round. Contributor commit `b0ed28b7` reports completion of its 635 semantic SAT modules and the start of replay builds for the proposed 235 bound; the complete result remains unfinished. The updated progress note is pinned under `sources/`. No new global bound is adopted from that progress report.
