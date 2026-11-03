# Independent target and subwindow review

The target is correctly aligned with milestone 120's conditional replacement cycle. Edge 2511 has direction index 0, history 0 and count code 27813. Decoding the code in base six gives the exact six counts $(4,4,3,5,4,4)$, and the direction table gives $012031041$. The resulting vertices are

$$
(0,1,3,7,6,14,12,13,29,31).
$$

The existing `sixSymbols_explicit` theorem places those counts at centres $r+3,\ldots,r+8$. Consequently the probe's eight internal bounds, with the first two intervals $[0,21]$ followed by six singleton intervals, encode the intended graph key. All six symbols are below six, so no bucket interval has been replaced by an exact six.

The saved full-cube probe reports `UNSAT_UNCERTIFIED` in 0.047 seconds, with radius nine, 512 vertices, no sum counter and no added cycle cuts. Its recorded source hashes match the current inputs. This review supplies no contradiction certificate.

## Existing restrictions

The four six-transition subwindows are as follows. The direction offset is zero-based. Counts are listed in the displayed canonical orientation; an asterisk denotes $[0,21]$.

| Offset | Shape | Orientation | Five counts |
|---:|---|---|---|
| 0 | $012031$ | Forward | $(*,*,4,4,3)$ |
| 1 | $012031$ | Reversed | $(5,3,4,4,*)$ |
| 2 | $012314$ | Forward | $(4,4,3,5,4)$ |
| 3 | $012032$ | Forward | $(4,3,5,4,4)$ |

The checked milestone-120 theorem on $012031$ requires at least one of its four outer counts to be at least four. Both displayed $012031$ windows already satisfy that conclusion through their known counts. The theorem therefore gives no contradiction here.

The checked milestone-112 theorem on $012314$ states that middle count at most two forces outer sum at least nineteen. The target middle count is three, so that hypothesis fails. Its outer sum is seventeen. This suggests a stronger count-conditioned test, but the existing theorem cannot be applied with a threshold of three.

The earlier native hypothesis on $012031$, middle at most five implying outer sum at least fifteen, remains uncertified. Applied to offsets zero and one it would respectively require the two unknown counts to sum to at least eight and the remaining unknown count to be at least three. Both are compatible with their stated intervals; neither is a direct contradiction.

The successful `ActualOuter120` and `ActualSum112` receipts were checked against their current source, compiled object, log and source snapshot. Their printed actual-count statements use only `propext`, `Classical.choice` and `Quot.sound`. No new compiler was run.

A bounded syntactic check parsed all 1378 reference keys and examined every contiguous placement in both orientations. It found 1112 shape-matching placements and no single key whose forbidden intervals contain the complete target intervals. This does not establish independence from combinations of references or count propagation. It establishes that the new test is not an immediate interval-containment application of one listed key.

## Six-transition reduction

The six-transition condition

$$
012032,\qquad
\alpha_1\le4,\ \alpha_2\le3,\
\alpha_4\le4,\ \alpha_5\le4
$$

with the middle count unrestricted within $[0,21]$ is an intermediate reduction. It is precisely the final six-transition subwindow, weakened from the target's singleton counts. The parent's saved `012032-second3-outer4.json` reports native UNSAT in 0.063 seconds with no added cycle cuts. This strengthens the earlier `012032-caps43544.json` result by removing its middle cap. The equally short `012314-caps44354.json` also reports native UNSAT and gives an alternative five-count exclusion. Both reduce the nine-transition target to six transitions. No inspection here establishes that fewer than six transitions suffice, or that either condition is optimal.

The positive controls limit further weakening. The saved $012032$ outer-at-most-four probes report local candidates with counts $(4,4,11,4,4)$ and $(4,4,8,4,4)$. Both have second count four and therefore do not satisfy the selected second-count cap of three. They obstruct relaxing that cap to four while keeping the middle unrestricted; they do not obstruct removing the earlier middle cap alone. The second-count-at-most-three control reports $(15,3,13,17,19)$, so that cap alone is insufficient in the saved local model. The broader $012314$ test with middle at most three and all outer counts at most five reports $(5,5,3,5,5)$. These positive models were read rather than independently validated in this bounded review and are not asserted to be full snakes.

The intermediate actual-snake transfer is preserved unchanged in `lean/ActualOuter121.lean`, SHA256 `360242f6f8a93396d28c10b36398f8b5d299843f0a5f82b6d8b18f00d8193082`. It has not been compiled and is now unused because the subsequent pair condition is stronger.

## Selected pair condition and prepared proof

The latest native probes on $012032$ exclude each of

$$
\alpha_2\le1;\qquad
(\alpha_2\le2\ \text{and}\ \alpha_4\le5);\qquad
(\alpha_2\le3\ \text{and}\ \alpha_4\le4),
$$

with every other count unrestricted within $[0,21]$. All three selected records report native UNSAT with no added cycle cuts. Canonical reversal fixes $012032$ and exchanges its second and fourth centres. These exclusions and their reversed forms imply

$$
\alpha_2\ge2,\qquad\alpha_4\ge2,\qquad\alpha_2+\alpha_4\ge8.
$$

For example, if the smaller count is two, the other must be at least six; if it is three, the other must be at least five; if both are at least four the sum conclusion is immediate. An independent bounded arithmetic check over counts $0,\ldots,21$ confirms the implication and equality pairs $(2,6),(3,5),(4,4),(5,3),(6,2)$. This arithmetic check assumes the proposed exclusions and does not prove them.

`lean/ActualPair121.lean` prepares the proof from the three planned semantic/contradiction pairs `PairMin032`, `Pair25032` and `Pair34032`. It uses the existing `dsOf_rev`, `coreAlpha_rev` and `reverse_canon` lemmas to obtain both orientations without additional reversed certificates. The concrete conclusions are `actual_pair_minima` and `actual_pair_sum`, with no local-contradiction hypothesis in their intended final statements. Two reusable pair-exclusion lemmas support the proof; the encoded forward/reverse guards retain explicit cap and local-refutation hypotheses, instantiated by the three concrete refutations. The reverse flag preserves the asymmetric cap order.

The source has 18 axiom-report requests and no new definitions. Its SHA256 is `17732a533cc39f73a1d140a69e5b666260a0fdc3ae5731611ff15b5f45090280`. It has not been compiled; successful concrete certificate checks and the final transfer check remain necessary. The observed local candidates with pairs $(2,6)$, $(3,5)$ and $(4,4)$ suggest local sharpness of eight, but those positive models were not independently validated in this review and are not asserted to be actual snakes.

The useful stopping point is the checked certificate and this actual-snake transfer. The present review makes no claim of a new upper bound or a new mathematical method.

## Evidence

`data/target-review.json`, SHA256 `120b12139f686429764171b6c6fb6c67c135dbbc1dc631fc14af03305887b229`, records the original full key, decoded counts, all four oriented subwindows, reference containment results, successful prior theorem receipts, selected new probe snapshots and exact source pins. The record was extended before final delivery as the parent supplied the stronger pair probes. It retains the previous evidence-file hash and the unchanged intermediate-source hash.

The review ran only bounded JSON/literal inspection, arithmetic, canonicalization and hash checks, followed by the requested transfer-source preparation. No solver, compiler, graph computation or Git action was performed. Only the owned review files and the two new transfer sources were written. One evidence-update command failed on the platform's default text encoding before any write; the explicit UTF-8 retry completed successfully.
