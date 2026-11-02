# Retention covers and edge indices

Length is measured in edges. This note concerns the structural interpretation
of the finite comparison graph. It establishes no new upper bound.

## Candidate identity

A candidate edge has the key

\[
 k=(d,q,c),\qquad 0\le d<505,\quad 0\le q<75,\quad 0\le c<6^6.
\]

The entries record the oriented nine-direction word, remembered history and
six encoded count symbols. Let \(K(d,q,c)\) mean that the candidate passes
the source-history test and the reference, short-rule, history and interval
filters. Its source and target are determined by this full key.

The saved graph has 4,947,008 distinct keys. Endpoint pairs alone do not
identify edges: 206,589 pairs have two entries. An edge weight must be read
at the index belonging to its full key. No proof here assumes distinct
endpoint pairs.

## Retention cover

**Definition.** A list \(L\) of candidate keys is a *retention cover* for
\(K\) if every bounded key satisfying \(K\) occurs in \(L\).

This is a one-sided condition. If \(L\) is a retention cover and every row
of \(L\) occurs in a larger list \(L'\), then \(L'\) is also a retention
cover. Indeed, each permitted key belongs to \(L\), hence to \(L'\).
This observation concerns membership. Every additional edge still needs
the weight and potential inequalities used in an upper-bound argument.

The exact ordered generator traverses \(d\), then \(q\), then increasing
\(c\), retaining precisely the keys satisfying \(K\). Its membership
condition is exactly the conjunction of the three ranges and \(K\).
Equality of a saved list with this generator implies retention coverage.
The weaker coverage condition is sufficient for mapping a snake into the
saved graph.

## Indexing lemma

Let \(A_{d,q}\) be the ordered list of count codes saved for the block
\((d,q)\), and let

\[
 O_{d,q}=\sum_{(a,b)<(d,q)} |A_{a,b}|,
\]

where the pairs are ordered lexicographically. If \(c\in A_{d,q}\), its
edge index is

\[
 I(d,q,c)=O_{d,q}+\operatorname{pos}_{A_{d,q}}(c).
\]

Here \(\operatorname{pos}\) denotes the zero-based position of the code.
The saved lists are strictly increasing, so this position also equals
the number of saved codes smaller than \(c\). The concatenated list
consists of the preceding blocks, this block, and the following blocks.
An index equal to the preceding length plus the within-block position
therefore retrieves the intended row. A list with no duplicate full keys
gives a unique such index.

Lean checks the generator membership characterization, the retention-cover
equivalence to inclusion, its monotonicity, the prefix/within-block index
formula, uniqueness under a duplicate-free list, and indexed endpoint
mapping. The concrete sortedness and all row endpoints have separate
computational checks against the saved arrays.

## Actual snakes and the finite obligation

For a snake with \(m\) edges and \(r+9\le m\), earlier proofs assign
the key \((d_r,q_r,c_r)\) and the numbered state \(s_r\). They establish
all four families of exclusions and source-history compatibility. The
reference family retains the two explicit premises that the complete
235 and 236 reference catalogues are refuted. The short, history and ten
interval families use their checked local theorems.

The numeric acceptance theorem specializes these statements to the actual
table ID, history ID and count code. Given a retention cover for that
numeric predicate and the saved endpoint-column identities, every actual
step has an in-bounds edge index with source \(s_r\) and target
\(s_{r+1}\). Selecting one such index for each \(r<m-8\) gives the whole
state walk. Weight interpretation and potential summation remain separate.

The independent executable comparison reconstructs all exclusion families
and exactly matches every compatible block: 36,904,896 candidate keys,
791 compatible blocks and 4,947,008 retained rows. All 37,084 incompatible
blocks are empty. This calculation checks more than one-sided coverage,
but it is not a Lean proof of the concrete array contents. The universal
walk theorem must keep finite coverage and endpoint equality as premises
until their corresponding checked data certificates are available.

## A smaller certificate target

Coverage can be certified by showing that every bounded key omitted from
the saved graph violates at least one established filter. It is unnecessary
to prove that every saved row passes every filter. This permits a certificate
organized by excluded count regions, with a rule and placement witnessing
each rejection. The reference premises remain explicit in the mathematical
argument. Constructing and checking such a finite certificate is future work;
no running-time improvement is claimed here.

## Exact shared membership representation

The 791 nonempty blocks use only 127 distinct accepted count-code sets.
The six base-six digits admit a shared decision diagram with 3,981
nonterminal nodes and two constant leaves. Each nonterminal records its
remaining digit count and six child indices. Constant leaves accept or
reject every remaining suffix. The levels are retained explicitly.

The complete diagram, its 127 roots and all 791 block assignments occupy
105,941 bytes as compact JSON, or 29,924 bytes compressed. Expanding every
root and comparing every block recovers the exact saved code lists.
This gives a small reproducible representation of membership. It has not
yet been related to the numeric retention predicate by a Lean proof.
The next finite certificate can aim to prove that predicate acceptance
implies acceptance by the corresponding diagram root, then recover a
stored-row index using the already checked assembly.
