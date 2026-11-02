# Certified reuse of direction patterns

The reference exclusions repeatedly compare canonical direction slices with
the same pattern. A finite table can supply those comparisons once. This
note states the condition that makes such reuse sound and records the
completed comparison with the direct checker.

## A certified shape table

For a direction index \(d\), offset \(s\), width \(\ell\), reversal flag
\(\varepsilon\), and pattern \(\pi\), write

\[
\tau=(d,s,\ell,\varepsilon,\pi).
\]

The descriptor \(\tau\) is valid when

\[
\operatorname{can}\!\left(
\operatorname{rev}_{\varepsilon}
\bigl(\operatorname{take}_{\ell}(\operatorname{drop}_{s}\delta_d)\bigr)
\right)=\pi,
\]

where \(\delta_d\) is the direction word returned by the fixed lookup.
The reversal flag and the entire pattern are part of the descriptor.

A **certified shape table** is a lookup \(H\) and a natural number \(N\)
such that every \(H(i)\), for \(i<N\), is valid. This definition does not
require distinct entries or assert anything about out-of-range lookups.

For a reference key \((\pi,\sigma)\), placement \(a\), orientation
\(\varepsilon\), and direction index \(d\), the requested descriptor is

\[
R=(d,a+2,|\sigma|+1,\varepsilon,\pi).
\]

If \(i<N\) and \(H(i)=R\), validity of \(H(i)\) supplies exactly the
reference key's original shape comparison. Catalogue bounds, fitting
placement conditions and count constraints are still required.

**Certified shape substitution.** Replace a reference shape comparison
by the bounded index test and complete descriptor equality above. Keep
every other guard and count condition. A successful substituted witness
check implies the original witness validity check.

**Proof.** The bounded index gives validity of \(H(i)\). Substitution using
\(H(i)=R\) gives the original reference shape equality. Conjoin it with
the unchanged catalogue, placement, direction and history bounds. This is
the original compatibility condition. Conjoining the unchanged box/count
condition gives witness validity by the separation identity from milestone90.
Other witness families retain their original compatibility checks. For a
list, require one supplied index per entry; equal lengths ensure every
entry occurs in the zipped check. Apply the argument entry by entry.

Lean checks this argument for arbitrary supplied lookup functions and
indices. The finite table validity and descriptor equalities are separate
concrete obligations, discharged for the pilot below.

## The same six-case certificate

The pilot retains exactly the original six direction/list assignments:

\[
d\in\{1,3,307,308,310,312\}.
\]

Each assignment uses 640 boxes, 622 reference witnesses and 18 witnesses of
other families. The 3,732 reference occurrences require only 156 distinct
shape descriptors, 26 for each direction. Two count lists serve the six
assignments. Nonreference witnesses use their original compatibility checks.

Lean checks all 156 table values, the two count-condition lists, all six
index-list lengths, every requested descriptor equality and every remaining
guard. The resulting membership theorem has exactly the direct pilot's
hypotheses and conclusion: for a listed assignment, \(q<75\) and
\(c<6^6\), the original numerical retention predicate implies membership
in the original class-1 diagram. Neither proof assumes the other's result.

This adds eight new theorem audits: three generic substitution/list results
and five concrete cache/pilot results. The two direct pilot theorems are
rechecked for the timing comparison and are not new mathematical results.

## Cost comparison and decision

The source of the direct proof is byte-identical to milestone90. Fresh
compiler processes ran in the order direct, cached, cached, direct. Each
used the same machine and inherited proof environment. Two other Lean
proof processes remained active; their workloads were not controlled.

| Method | First proof run | Second proof run |
| --- | ---: | ---: |
| Direct | 18.812 s | 37.875 s |
| Cached | 24.203 s | 28.016 s |

Each cached proof time includes table-value validity, count-list validity,
all descriptor correspondences, remaining guards and final theorem assembly.
Its additional generic theorem compilation took 46.125 seconds, and the
concrete cache-data module took 45.219 seconds. Generation and preexisting
shared dependencies are outside these proof timings.

The samples give no consistent timing order. The direct runs also show
substantial variation under the concurrent load. No speed advantage is
established. The next full witness batch will therefore use the direct
balanced-lookup checker, preserving the simpler certificate and avoiding
additional cache setup. The certified substitution theorem remains available
if a later representation produces a measurable benefit.

The result closes this optimization experiment. It does not certify all
791 contexts, complete the actual-snake graph interpretation, strengthen a
local share, or lower the numerical upper bound. The maintained interval
is \(191\le a(9)\le235\); the proposed bound 234 remains conditional.
