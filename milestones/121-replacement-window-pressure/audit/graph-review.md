# Independent saved-graph review

The independent script checks all 14,646 newly removed keys against the pair
minimum and sum restriction, independently of the producer's interval-mask
implementation. It also checks all 36 clipped count pairs against the six
oriented interval conditions. The old outer-count guard is retained.

For both saved cycles, it checks complete keys, direction/history/count
alignment, retained-diagram membership, original endpoints and weights, all
thirteen inherited sum rules, potential bytes and tightness, exact means and
comparison arithmetic. Both cycles have zero deficits under the inherited sum
rules. There is no common six-transition shape between the two saved cycles.

The completed-share profile retains an eighteen-cycle of mean2915/6 and range
1730/3. The conditional-share profile has a replacement four-cycle of mean 496
and range 602. Integer comparisons stay235 and234. The producer checked every
retained-edge inequality and reproduced the full120 removal set and both old
weight vectors. The independent review does not repeat those full scans.

The first audit attempt used the nonexistent key `newly_removed` for per-pair
effects and stopped before writing any evidence. The producer schema uses
`marginal_removed`; that lookup was corrected and the full audit passed.
The initial script is preserved in `audit/independent-graph-initial.py.txt`.

The result is `data/graph-audit.json`, SHA256
`4744b8e2552621a0a14dfeef0a147b4b9a56f82347f90e8baad8cf19c1d54f65`.
The local theorem has separate Lean receipts. Unproved inherited sum rules and
global assembly remain outstanding; this graph review establishes no new
actual-snake upper bound.
