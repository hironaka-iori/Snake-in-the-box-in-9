# Complete interpretation of history share signatures

The history model records three overlapping canonical direction words of length nine. This note resolves which canonical eleven-direction words can produce each of its 55 share signatures and states the remaining geometric credit obligations.

## Compatible configurations

For a direction word $w$, write $\operatorname{can}(w)$ for its first-occurrence labelling. A **history signature** is a triple $\sigma=(d_0,d_1,d_2)$ indexing saved nine-direction words $E_{d_j}$.

Define the **compatible set** $\mathcal C(\sigma)$ to contain the canonical words $w$ of length eleven that use coordinates $0,\ldots,8$, describe an induced path and satisfy

$$
\operatorname{can}(w_j,\ldots,w_{j+8})=E_{d_j}\qquad(j=0,1,2).
$$

Canonicality forces the first nine letters of $w$ to equal $E_{d_0}$. Every compatible word therefore has the form

$$
w=E_{d_0}\mathbin{\|}(a,b),\qquad 0\le a,b<9,
$$

where $\|$ denotes concatenation. Each compatible set can thus be checked through 81 continuations. This reduction does not assume uniqueness.

The 55 distinct share signatures have 69 compatible words in total: 41 signatures have one word and 14 have two. The eight older rules stored with a single representative all have singleton compatible sets. The remaining 47 rules already stored complete lists, which agree exactly with reconstruction.

Two numerical enumerations agree: all 11,162 canonical induced eleven-direction words, and the separate 81-continuation test for every signature. The Lean certificates use the latter test for coverage, then separately check every listed word and prove the reverse inclusion. The resulting compatible-set characterization is exact for these local words.

## From recognition to an actual snake

Let $p$ have $m$ edges, and suppose its transition at index $r$ emits a share signature, with $r+9\le m$. The history theorem implies $r\ge2$ and identifies the signature with the three windows starting at $r-2,r-1,r$. Consequently

$$
\operatorname{can}(d_{r-2},\ldots,d_{r+8})\in\mathcal C(\sigma).
$$

This implication applies to every actual snake under the window-fit hypothesis. It does not assume that separately chosen local configurations can be combined into a longer snake.

## Credit and centre positions

For an eleven-direction window starting at $s$, the relevant share sum is

$$
S(p,s)=\sum_{i=0}^{4}s_{12}(p,s+i+6),
$$

where $s_{12}$ is the existing scale-12 empty-square share. A per-word bound means that every occurrence of that canonical word has $L\le S(p,s)$.

For an emitted signature, $s=r-2$, so the same centres are $r+4,\ldots,r+8$. If every word in $\mathcal C(\sigma)$ has bound $L$, the emitted history rule has that bound on those five centres. A single representative suffices only after uniqueness is proved.

The eight count-conditioned rules also impose caps. A cap at six-count position $k$ concerns the actual count at $r+k+3$, equivalently $s+k+5$. For $k<6$ and $c<6$,

$$
\min(6,\alpha_{r+k+3})\le c\quad\Longrightarrow\quad\alpha_{r+k+3}\le c.
$$

The implication fails at $c=6$. The checked transport retains the strict cap bound. All current history caps belong to $\{1,2,5\}$.

## Remaining geometric obligations

Coverage establishes which configurations can occur. The credit-dispatch statements still require an explicit geometric bound for each listed word. These premises must be instantiated before claiming the complete history-credit inequality.

The provenance audit maps the old credits to their existing local proofs. Rule edge 58 obtains its uncapped credit 6 from a nine-direction suffix theorem and its capped credit 12 from an eleven-direction theorem. Their centre positions need separate transfers.

The audit identifies duplicate declarations of the share constants in distinct old and current modules, together with colliding instance-module names. The inspected core share definition has identical text in both modules; this is an import-ownership conflict, rather than evidence of different share values. A compatible port must reuse the current declaration, preserve each local theorem statement and be checked before its credit is adopted.

The next step is to instantiate the per-word bounds and prove that the maximum of applicable history credits is bounded by the same five-centre total. Other weight components and the complete defined-graph potential remain separate. No new numerical upper bound follows from this classification alone.
