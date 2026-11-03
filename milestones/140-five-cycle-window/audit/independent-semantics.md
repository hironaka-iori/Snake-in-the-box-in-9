# Independent encoding and certificate-semantics audit

The necessary encoding of canonical `012032` with five exact counts
`(3,5,4,5,3)` passed this bounded audit. The core omits the lower bounds at
the two positions having count 5. This identifies a possible stronger
statement requiring a separate Lean semantic check.

The audit independently reconstructed the encoding using only Python's
standard library. It did not import either project generator, invoke a solver,
or run Lean. Parent scripts and proof inputs were unchanged. Detailed checks
are in `data/independent-semantics.json`, SHA256
`be17d7498b663079f9294d97aeff9dde0beef79abe46bc2b202fd3fb07aeb087`.

The six transitions give `[0,1,3,7,6,14,10]`, an induced path. The centres
`[1,3,7,6,14]` are at actual offsets 1 through 5. Each has two distinct path
directions. The other seven coordinates give 21 distinct opposite square
corners. The two side vertices of each square cannot be selected, because
the centre already has its two selected path neighbours. Thus the square
has exactly one selected vertex if and only if its opposite corner is absent.
For exact count `a`, the upper counter permits at most `a` absent corners;
the lower permits at most `21-a` selected corners. These impose equality.

The independent reconstruction reproduced all 100,253 clauses byte for byte
against both input copies, all 4,253 meanings and all 11 counter tables. The
variables comprise 512 selection flags, 512 endpoint flags and 3,229 registers.
The clauses express the selected window, degree at most two and positive
degree, endpoint degree/selection conditions, at most two endpoints, the exact
counts, and standard square/six-cycle exclusions. These are necessary for an
actual snake containing the fitting window; that window implies positive path
length. There are no endpoint-location units, parity restrictions or appended
cycle cuts. Every source pin and preserved certificate-file hash matched.

All 4,163 core clauses were reconstructed in original order. Their families
are: window 7, degree-at-most-two 1,614, positive-degree 42, low-endpoint 489,
endpoint-selected 11, endpoint-degree 30, counter clauses 1,876, cycle cuts 94.
The native receipt and saved replay agree on 18,606 deductions and 1,397,536
hints. A separate structural scan confirmed these totals, earlier references
and the final empty clause; it did not rerun RUP. There are 1,690 active
variables. The saved complete replay supplies the propagation evidence.

| Counter | Meaning | Retained clauses |
| --- | --- | ---: |
| 0 | At most two endpoints | 982 |
| 1 | First count at most 3 | 116 |
| 2 | First count at least 3 | 69 |
| 3 | Second count at most 5 | 156 |
| 4 | Second count at least 5 | 0 |
| 5 | Third count at most 4 | 143 |
| 6 | Third count at least 4 | 106 |
| 7 | Fourth count at most 5 | 119 |
| 8 | Fourth count at least 5 | 0 |
| 9 | Fifth count at most 3 | 116 |
| 10 | Fifth count at least 3 | 69 |

Counters 4 and 8 have no retained tag. None of their 672 register variables
appears in the core or retained proof. Every other count counter is used;
that does not establish necessity in every possible proof. The source row
in milestone 139 has suffix `[0,3,4,0,5,4]`, canonically `012032`, and the
corresponding five counts `(3,5,4,5,3)`.

The same core suggests exclusion under

\[
(\alpha_{r+1},\alpha_{r+3},\alpha_{r+5})=(3,4,3),
\qquad \alpha_{r+2}\leq5,\quad\alpha_{r+4}\leq5.
\]

The generic semantic checker validates every counter, so the original theorem
cannot simply be applied under weaker hypotheses. A separate table can replace
unused entries 4 and 8 with the existing valid default counter: empty literals,
endpoint kind, threshold 2. All used entries and indices remain intact. The
new bounds are `[(3,3),(0,5),(4,4),(0,5),(3,3)]`. A fresh generic semantic check
and actual-snake bridge are required. Alternatively, the two unused lower
counters can retain their literals with threshold 21 and lower bound zero.

This specialization is a candidate pending separate Lean checks. The original
exact-count actual-snake theorem is also subject to the parent's Lean checks.
Neither this audit nor the native contradiction establishes a global bound.
