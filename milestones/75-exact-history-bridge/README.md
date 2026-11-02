# Exact history, share lookup and count-state coding

This milestone adds **39 Lean-checked declarations** needed by the current
snake-to-graph interpretation. The three parts are the history-word invariant,
exact orientation/share lookup, and base-six count/state arithmetic. It does
not construct the complete arbitrary-snake graph walk or establish a new
numerical bound. The retained project interval is191 through235;234 remains
conditional. The longer case7305 refutation is being replayed separately.

## Longest-suffix history

Let \(D\) be a finite dictionary containing the empty word and closed under
deletion of the last symbol. Suppose \(s\) is its longest suffix of the word
\(w\) already read. For any new symbol \(a\) and listed word \(t\),
\[
t\text{ is a suffix of }wa
\quad\Longleftrightarrow\quad
t\text{ is a suffix of }sa.
\]
For a nonempty candidate, removing its last symbol produces a listed suffix
of \(w\), whose length is at most that of \(s\). The two are nested suffixes,
so this shorter word is a suffix of \(s\). Appending the new symbol proves
the forward implication. The reverse follows by suffix transitivity.

Thus updating from the stored history selects the same word as examining the
entire read sequence. The selected longest suffix is unique. The
[history proofs](history/README.md) instantiate this argument with the exact
75-entry dictionary and58 signatures of the current graph. They also prove
that any emitted three-symbol signature is the last three IDs of the read
sequence, and that no emission occurs at steps0 or1. These symbols are IDs
of nine-transition windows, rather than individual cube-coordinate directions.
The generic and exact-instance modules contain22 audited declarations.

## Exact share selection

The Python builder chooses the lexicographically smaller of a canonical
six-direction word and its canonical reversal. The existing catalogue
dispatcher prefers a listed forward representative and reverses otherwise.
The [lookup proof](lookup/lean/GraphShareLookup.lean) checks their equality on
all induced six-direction patterns, then transports it to arbitrary actual
snake windows using canonicalization.

For an edge beginning at \(r\), the suffix of its canonical nine-direction
word selects the catalogue for the six transitions beginning at \(r+3\).
The corresponding share centres are exactly \(r+4,\ldots,r+8\). The checked
share inequality retains all nine displayed local certificate hypotheses.
Three target hypotheses have completed case proofs; six remain pending.
The lookup module contains8 audited declarations.

## Numeric state and guard identities

Write \(C(a_1,\ldots,a_k)\) for the base-six encoding with digits \(a_i-1\),
where \(1\le a_i\le6\). The [count-code proof](numeric/lean/CountStateCode.lean)
checks
\[
\begin{aligned}
C(a_1,\ldots,a_6)&<6^6,\\
\left\lfloor C(a_1,\ldots,a_6)/6\right\rfloor&=C(a_1,\ldots,a_5),\\
C(a_1,\ldots,a_6)\bmod6^5&=C(a_2,\ldots,a_6),\\
C(a_1,\ldots,a_6)\bmod6+1&=a_6.
\end{aligned}
\]
It also checks the exact numeric state layout
\[
\operatorname{state}(s,q,c)=
\begin{cases}
7776s+c,&q=0,\\
1026432+7776(q-1)+c,&q>0,
\end{cases}
\]
including the bound below1601856 for \(s<132\), \(q<75\), \(c<7776\),
and recovery of the count remainder and appropriate block index.

For every cap \(k<6\),
\[
\min(6,\alpha)\le k\quad\Longleftrightarrow\quad\alpha\le k.
\]
An unsaturated symbol equals the actual count; a saturated symbol represents
the interval6 through21 under the known count bound. These identities support
the builder's small-cap guards. They do not by themselves prove every lookup
or short-sum exclusion is covered. This module contains9 audited declarations.

## Proof status and reproduction

All39 printed axiom lists are confined to `propext`, `Classical.choice` and
`Quot.sound`. Existing mathlib and normalization objects were reused; this is
not a fresh rebuild of the entire inherited proof closure. See
`history/data/proof-audit.json`, `lookup/data/proof-audit.json` and
`numeric/data/proof-audit.json` for source/object/log hashes and exact scopes.

From the repository root, use the installed Python runtime with `-X utf8`:

```
python -X utf8 milestones/75-exact-history-bridge/history/scripts/check.py
python -X utf8 milestones/75-exact-history-bridge/history/scripts/audit.py
python -X utf8 milestones/75-exact-history-bridge/lookup/scripts/check.py
python -X utf8 milestones/75-exact-history-bridge/numeric/scripts/check.py
```

Run small checks serially alongside the memory-intensive case7305 replay.
Absolute runtime and support paths remain specific to the saved Windows host.
The current-round checkpoint script validates the recorded evidence without
rebuilding it. Its replay snapshot contains only completed modules and is
distinct from the driver's live record.

## Refutation replay and repository review

The selected case7305 proof is unchanged, with SHA256
`fc220ab5f0d19654b54af0fd4562094839727814ebf4cba87a52d5d0a4619def`.
Its15-bit checker and large proof checkpoints have begun passing Lean.
`data/checkpoint.json` records the last observed process and completed modules;
check the current process before resuming. A snapshot is not evidence that a
process remains live later. No final local share theorem is claimed until the
entire replay, geometric/reversal wrappers and case audit pass.

A read-only planning test found795 unused initial clauses. Even releasing
their slots would leave an estimated17234 slots and the same15-bit width.
The running export was preserved. This test supplies no replay speed claim.

The contributor branch advanced to
`1e0ebb95954cc70f9edf59268b5a36df3f616422`, adding handover documentation.
Its235 result remains contributor-checked; its234 production replay remains
unfinished. The new documentation does not supply a stronger completed bound.
Pinned review evidence is under `upstream/` and `data/repository-check.json`.

## Remaining assembly

The next global proof must still connect these checked pieces:

1. Prove that every actual nine-direction block has the correct ID in the
   505-entry extension table and that its source/target lie in the132-shape
   state table.
2. Define the concrete numeric history index from the checked dictionary
   invariant. Match the builder's maximum-suffix selector and prove the
   compatible direction shape for every nonempty history.
3. Certify every current exclusion lookup, guard and complete set of compatible
   eleven-direction realizations. A signature may have multiple realizations.
4. Apply all relevant geometric, count-conditioned and count-free share bounds
   to the same five centres; use their maximum.
5. Replay the full finite potential and range in Lean, then apply the existing
   overlap, boundary and telescoping results.

The paper remains revision66. The next planned full rewrite is milestone76;
it should explain these mathematical arguments while retaining the unresolved
local and global hypotheses.
