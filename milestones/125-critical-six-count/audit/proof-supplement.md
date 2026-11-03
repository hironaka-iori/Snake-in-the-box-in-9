# Supplementary proof review

Both additional modules passed their saved Lean checks. `EmptyTradeoff125` passed in 18.234 seconds with two axiom reports. The repaired `ActualBounds125` passed in 30.375 seconds with five reports. The independent audit verified 202 distinct file hashes, three additional source pins, all seven reports, and matching successful-run records. Each report contains only `propext`, `Classical.choice`, and `Quot.sound`. Neither source introduces a definition or contains a placeholder proof or `native_decide`.

Current sources, objects, logs, checker bytes, source/checker snapshots, recorded dependencies, and resolved direct imports match their receipts. The original `Structural125` report, JSON, and audit script remain byte-identical to their previously frozen hashes.

`ActualBounds125` initially failed because `dsOf_slice` lacked its namespace qualification and the final arithmetic step retained unsimplified numeral additions in its count indices. The failed source, checker snapshot, log, and attempt record are preserved and hash-checked separately. Their error-generated axiom reports are excluded from the successful proof count. The successful source qualifies `Snake9.GraphInterpretation74.dsOf_slice` and normalizes the indices before the arithmetic step.

The empty-square tradeoffs are conditional actual-snake statements. Let $s_0$ be the number of ordinary empty squares, so the anchored count is $4s_0$. For $m\ge235$, 39 disjoint six-count blocks cover positions 1 through 234. Universal floor24 gives

$$
T\ge39\cdot24+(m-235)+8=m+709.
$$

With $s_0\ge6$, the retained-square charge at $m=235$ is at least

$$
944+35\cdot236+2\cdot6=9216>9214.
$$

Thus `bound234_of_floor24_and_six_empty` concludes $m\le234$. Its Lean empty-square premise is the anchored bound of at least 24, guarded by $m\ge235$.

Universal floor23 instead gives $T\ge m+670$. If $s_0\ge25$, the corresponding charge at $m=235$ is

$$
905+35\cdot236+2\cdot25=9215>9214.
$$

This proves `bound234_of_floor23_and_twenty_five_empty`, with the explicit anchored bound of at least 100. Neither theorem proves its universal floor or empty-square lower-bound hypothesis.

The actual-window result concerns a fitting seven-transition window with canonical directions $0120324$. Its six internal counts are at positions $r+1,\ldots,r+6$. Canonical slicing gives the prefix $012032$ at start $r$ and the suffix $012314$ at start $r+1$; these two normalizations were also checked independently in the audit script.

Write these six actual counts as $a,b,c,d,e,f$. The checked prefix results supply $b,d\ge2$ and exclude $a\le2$ together with $d\le3$. If $d\le2$, then $d=2$ and $a\ge3$. The checked suffix outer-sum theorem applies because its middle count is precisely $d$ and gives

$$
b+c+e+f\ge19.
$$

The total would then be at least 24, contradicting the stated total bound of at most 22. Hence $d\ge3$. Together with the existing internal positivity and upper bound 21, `actual_six_bounds` proves the six intervals

$$
[1,21],\ [2,21],\ [1,21],\ [3,21],\ [1,21],\ [1,21].
$$

These are actual-count intervals, with no clipping or symbol6 interpretation involved. The theorem is conditional on the canonical shape, fitting window, and total at most 22. It supplies the interval reduction needed by a later contradiction argument. It does not establish that the restricted interval is impossible, a local floor23, a native contradiction certificate, or a universal six-count floor.

Evidence SHA256 pins:

- `data/proof-supplement.json`: `8e941a63903c10b582b69edb72939830e651861ef47f9e87e95846c689cab2b0`.
- `scripts/audit_supplement.py`: `639f3a9b294c6baae0d073ae137a0d13208b762edd184e211c18b8989cf674b2`.
- `data/EmptyTradeoff125-audit.json`: `1c29605cb87a8913531752c39ff92c406c8074e860351eabb4a97f6cc737c9fb`.
- `data/ActualBounds125-audit.json`: `df9f9b6c1b883071a026d761d3eda47dd987a525d10ae65dc46fe1c70a1ddedc`.
- Successful `lean/ActualBounds125.lean`: `dbb9f2fbe1ea322903091a73eb3ed36cd677f80a6309cf5aee851a916654ab7a`.

The JSON preserves the complete source/object/log/checker/dependency/import hashes and the unsuccessful attempt's evidence. This supplementary review ran no compiler, solver, proof replay, or graph enumeration. The audit script prints a summary by default and creates an output file exclusively when requested.
