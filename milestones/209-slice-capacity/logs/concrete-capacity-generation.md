# Concrete capacity source draft

Created `lean/ConcreteCapacity209.lean`, importing `Std` only. The literal 99 vertices were read from the `8.vertices` field of `data/lower-dimensional-input.json`, whose previously audited SHA-256 is `d62c92cc97eae196b21aeefe2111adfb03cc3121b9b62ba7e3e2c6ee6920c20d`.

The Lean definitions recompute the base words on coordinates 0 and 5. Equal consecutive base words start a new chronological interval; changed base words extend the current interval. Each visit set is then enumerated from the four possible base words. No precomputed interval list or visit table is imported.

Four proposed kernel-reduction theorems check the 99-vertex/81-interval extraction, even counts `[12,5,4,10,10]`, odd counts `[6,9,9,8,8]`, and the exact 32 selected even-clique indices with distinctness and index/parity bounds. The expected clique list was read from the saved case 23 extraction; its equality is checked against the source-derived definition rather than assumed.

The draft was not compiled, and no search or tests were run. It does not connect these finite facts to the whole geometric model or certify an exclusion. Parent compilation remains required.
