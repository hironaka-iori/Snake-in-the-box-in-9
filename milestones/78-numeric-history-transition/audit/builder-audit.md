# Numeric history selector and state encoding audit

This bounded review inspected the milestone70 builder, milestone75 history/count sources, and the completed milestone77 numeric-history and shape interfaces. It ran no Lean job and changed no proof, data, Git state or live case. No discrepancy was found in the intended selector or state formulas. The exact implementation conditions below must remain visible in their connecting theorem.

## Concrete selector

In [milestone70 build.py](../../70-proof-supported-share-model/scripts/build.py), lines 58–61, the dictionary is the ordered list of 75 tuples from milestone67's `full-model.json`. Its index zero is the empty tuple; the remaining entries are distinct, nonempty words of length one or two. Entries are identifiers of oriented nine-direction windows, not coordinate directions or graph-edge indices.

For current dictionary index \(q\) and new direction ID \(d\), the builder forms \(h=D[q]\mathbin{+\!+}[d]\). It considers exactly those indices \(j\) satisfying all three conditions:

\[
D[j]\ne[],\qquad |D[j]|\le |h|,\qquad
D[j]\text{ is the final }|D[j]|\text{ entries of }h.
\]

The indices are enumerated in increasing dictionary order. Python's `max` with length as its key returns the first maximum-length candidate; with no candidates, the result is index zero. A left-to-right scan initialized at zero and replacing the current choice only for a strictly greater candidate length has the same behavior, provided \(D[0]=[]\).

Conditions that the proof must cover:

- **Empty fallback:** index zero denotes a genuine empty dictionary entry. It is not an out-of-range sentinel. Every nonempty candidate has positive length and therefore replaces the initial zero-length incumbent.
- **Empty candidates:** the Python comprehension excludes them. In particular, Python's slice with negative zero returns the whole input, so an unguarded transcription of the slice test for an empty candidate would not have ordinary empty-suffix semantics. A Lean suffix predicate may include the empty word only after proving that this leaves the chosen index unchanged.
- **Length guard:** a true suffix predicate already implies the length inequality. A proof may absorb the explicit guard into that predicate, but should establish that equivalence rather than silently discard it.
- **Ties:** two suffixes of one word with the same length are equal. The checked dictionary distinctness therefore rules out different maximizing indices. For a generic dictionary with duplicate entries, a strict scan still selects the first occurrence, while a scan replacing on equal lengths could disagree with Python and with `idxOf`. Either retain first-occurrence semantics or assume distinctness explicitly.
- **Index bounds:** the concrete outer loop has \(q<75\) and \(d<505\). `getD` with an empty fallback is suitable inside a total Lean definition, but the builder interpretation must not rely on its behavior at an invalid index.
- **The dictionary order is fixed:** it is empty first, then one- and two-ID prefixes sorted by length and lexicographically. Sorting is not needed for maximum correctness, but the numeric result must refer to this exact ordered list.

The prior small audit checked all \(75\cdot505=37875\) update pairs and found unique maxima. That executable check is separate from the new generic proof. Milestone77's actual-history shape filters already justify the builder's nonzero source compatibility test and nonzero target compatibility assertion once the selected next index is identified.

## Shortest connecting argument

The existing `history_decode` theorem identifies the entry at `historyIndex w` with `run prefixes w`. Prove that the strict scan returns an in-range index whose entry is the longest listed suffix of its input. `longest_spec` and `longest_unique` then identify that entry with `longest prefixes input`; dictionary distinctness converts entry equality to index equality.

For the numeric update itself, the defining fold and `List.foldl_append` give

\[
\operatorname{run}(D,w\mathbin{+\!+}[d])
=\operatorname{longest}\bigl(D,\operatorname{run}(D,w)\mathbin{+\!+}[d]\bigr).
\]

This direct update identity does not require a new prefix-closure argument. Prefix closure is needed for the already checked interpretation of the stored word as the longest dictionary suffix of the complete past.

The desired instantiated equality is
`builderNext (actualHistory p r) (directionId p r) = actualHistory p (r+1)`.
The list identity can be proved for arbitrary identifier values if the selector is total. The bound \(r+9\le m\) is required when interpreting the new value as an actual one of the builder's 505 direction IDs. The existing `readDirections_succ` supplies the exact append identity.

## Source and target state formulas

For an actual edge beginning at \(r\), let \(b_i=\min(6,\alpha_i)\), and encode the six symbols \(b_{r+3},\ldots,b_{r+8}\) in base six using digits \(b_i-1\). Write its code as \(c\), and put

\[
B=6^5=7776,\qquad N=132B=1026432.
\]

The builder's \(N\) comes from the eight-direction base metadata `sm['states']`; it is not the final history-expanded state count. With source shape \(s\), target shape \(t\), current history \(q\) and selected history \(q'\), the endpoints are

\[
U=\begin{cases}sB+\lfloor c/6\rfloor&q=0,\\N+(q-1)B+\lfloor c/6\rfloor&q>0,\end{cases}
\qquad
V=\begin{cases}tB+(c\bmod B)&q'=0,\\N+(q'-1)B+(c\bmod B)&q'>0.\end{cases}
\]

The checked `six_count_code` identifies division by six with the first five symbols, reduction modulo \(B\) with the last five, and \(c\bmod6+1\) with the entering symbol. The checked `stateCode` is exactly the displayed piecewise formula, with range below \(1601856\). Its nonzero branch omits the explicit shape because history compatibility determines that shape. The final state's five counts are at positions \(m-5,\ldots,m-1\), so its counts remain internal.

Positivity of the actual internal counts and truncation give symbols in \([1,6]\), which is required for those arithmetic lemmas. Symbol six still represents the original-count interval \([6,21]\). The source state's counts at positions three through seven are stored for constraints; their appearance in a state does not charge them as entering counts in the global sum.

## What remains after the selector equality

1. Assemble one actual state sequence using the common direction shape, numeric history and five-count code; prove that consecutive encoded endpoints agree.
2. Prove that every actual direction/count/history triple survives the builder's reference exclusions, recovered local rules and history exclusions. Then connect it to an index in the exact retained arrays, including the later milestone72 interval filters.
3. Interpret each recognized three-ID signature through every compatible eleven-direction word. Correct history recognition does not remove coordinate-forgetting ambiguities.
4. Interpret every applicable geometric, count-specific and count-independent credit as a bound on the same five shares, and use their maximum. The later share updates preserve endpoints but change weights.
5. Connect the resulting walk to the complete finite potential and global accounting. The selector and state identities supply no new upper bound alone.

## Pinned source evidence

| Source | SHA256 |
| --- | --- |
| Milestone70 builder | `bffe9f3d541a807841d564a85bc3f5d2523ae73ee7b8218b79facdac9a4987db` |
| Milestone67 full metadata | `08fc18347eff9065d873cb8be01b4b72129e1ee939b4bf1474d04640cc8bc274` |
| Milestone77 NumericHistory | `6ce3a0d435def01ac8118296764571ddec51c6d5960c3469327c709b201e4e8d` |
| Milestone77 HistoryShape | `07f2c3dbac1305e7838812369954e105c7e82854bd72a898e8414b881c9d427d` |
| Milestone75 CountStateCode | `76511c647e280e8da66998622e1ac9d673c10ae8ca0dcd1396fd2724bfb7a1bc` |
| Milestone75 HistoryPrefix | `989b08a3f9ee7b751a7ae68e232855d6d3590e2d815e12893f594f496a89facb` |
| Milestone75 ExactHistory | `0cbb26994f0b6372ee107529c1406fd0c64028137ac94a0e6c4f63671185016c` |

Successful receipts inspected: NumericHistory `d184ac20db41fd280461f9bbe90226fe08ee58f22d172f8c7d1e5bb12306c27f`; HistoryShape `220dd06eb0a26b90b375d5ec6759988e593b6e9e432f6d0275e2aa66f0e4bc26`; CountStateCode `0a15983120ce3503751f8d65307077cb8631d87bacdb47548469722d5a86d29c`. These establish their stated interfaces using pinned inherited objects; this audit did not rebuild that dependency closure.
