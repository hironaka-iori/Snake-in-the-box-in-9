# Generic symbol-credit bridge: proposed source

Source: `milestones/97-geometric-credit-integration/lean/SymbolCredit97.lean`.
Status: written and inspected; **not compiled**. No compiler, solver or background job was run. The only files written for this task are that source and this note.

## Interface

The module imports `ConcreteRules95`, `ReferenceRetention` and the current `LocalWindowShareBridge`. It introduces no definitions and no concrete refutations. All four declarations are in `Snake9.SymbolCredit97`, with an axiom-print request for each.

1. `canonical_symbol_share` takes a snake, a fitting $n$-transition window with $n\ge1$, its canonical direction match, exact `symsOf` list, and `RefutedShare (winOf cs) (boundsOf syms) M K`. It concludes
   \[
   K+1\le\sum_{i=0}^{n-2}\operatorname{coreShare}(M,p,r+i+1).
   \]
   The empty sum for $n=1$ has the meaning supplied by `List.range (n-1)`.
2. `reversed_symbol_share` has the same conclusion from matches against the reversed direction word and reversed symbol list. Both matches are required.
3. `encoded_forward_suffix_share` assumes $r+9\le m$, a five-symbol list in1..6, a canonical match on the last six directions of the canonical nine-word, and `sixCode p r % 7776 = encodeCounts syms 0`. It concludes
   \[
   K+1\le\sum_{i=0}^{4}\operatorname{coreShare}(M,p,r+(i+4)).
   \]
4. `encoded_reversed_suffix_share` uses the reversed canonical suffix and `encodeCounts syms.reverse 0`, with the identical five-centre conclusion.

Resolution $M$ and cap $K$ are generic. Set $M=12$ for the current credits. No certificate premise is removed by these generic statements. The numeric suffix theorems are stated on `canon (dsOf p r 9)`; applying a lookup indexed by `directionId p r` also needs the already checked `Direction77.direction_decode` rewrite.

## Existing arguments reused

`canonical_symbol_share` follows `Guards79.canonical_symbol_exclusion` closely. `actual_canonical_frame` supplies a coordinate realization, and `LocalWindow.refuted_share_dir` supplies the share conclusion. Its `boundOf_symC` step retains the true count interval: symbols below six determine exact counts, while six means6..21. This module makes no separate saturation inference.

The reverse theorem applies the forward theorem to `revSnake p` at `m-r-n`; it rewrites direction and count lists with `dsOf_rev` and `symsOf_rev`, then transports the sum through `coreShare_window_rev` with $n-1$ centres.

The numeric theorems instantiate `actual_slice_decode` at $s=1,w=5$. Thus the remainder modulo $6^5$ represents counts at $r+4,\ldots,r+8$. The forward direction rewrite is `canonical_nine_share_suffix`; the reversed direction rewrite uses the same equality between two applications of `reverse_canon`. At $r+3$ the six-transition share theorem charges exactly those five vertices.

## Compilation concerns to resolve

The mathematical proof uses existing checked interfaces, but this source has no compilation receipt. The next run should inspect these exact elaboration points if Lean reports an error:

- In `canonical_symbol_share`, inference of the implicit coordinate list `u` and resolution/cap in `refuted_share_dir` from `hu`, `hcs` and `href'`. The source follows the already checked exclusion adapter's argument order.
- In `reversed_symbol_share`, rewriting the shared sum with `coreShare_window_rev` after the natural subtraction identity `m-r-(n-1)-1 = m-r-n`. The hypotheses $n\ge1$ and $r+n\le m$ are present.
- Both numeric applications use `by simpa using hcode` to normalize division by $6^0$ and $6^5=7776`. If simplification is insufficient, replace only that step by explicit arithmetic normalization; the decoding premise is already exact.
- The final five-centre statements use associative/commutative addition simplification to identify `(r+3)+i+1` with `r+(i+4)`. If needed, supply that pointwise equality with `omega` rather than changing the theorem statement.
- The reversed suffix equality is rewritten through `reverse_canon` on the suffix, then the nine-window suffix identity, then `reverse_canon` on the actual six-window. This avoids asserting equality of different canonical orientations.

No historical `ShareFrame`, `ShareInSnake` or concrete SAT/UNSAT module is imported. The intended first check is this module alone on the current95/97 path after the active geometry batch permits it. Its successful receipt should audit exactly the four printed theorem names. After that, closed concrete refutations can instantiate these interfaces without repeating geometric normalization or count decoding.
