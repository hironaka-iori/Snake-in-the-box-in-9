# Review of the new six-count and local-result statements

The complete inserted direct six-count section in `scripts/revise.py`
(lines 22–134 of the reviewed version) and the complete
`data/local-results.tex.txt` fragment were read. The associated milestone122,
124 and 125 mathematical notes and successful proof reviews were consulted.
No source fragment, manuscript, compiler, solver or earlier audit was changed.
The reviewed SHA-256 hashes are
`61b8a384f248c9be2bcd2d4716fa5872aed993c14fab78d55aeb597a7bbcffcb`
for the revision script and
`1370081413ab6cb98d8412bbc68c2fffa4ea172c725b8cf3f6cdb9c4a39b067c`
for the local-results fragment.

The statements pass the bounded mathematical review. No algebraic error,
indexing error, omitted geometric premise or new unconditional length bound
was found. The verification wording concerning ordinary empty squares merits
the small precision adjustment recorded below.

## Direct six-count section

The local-floor convention

$$
\sum_{j=1}^{6}\alpha_{r+j}\ge L
\qquad(r\ge0,\ r+7\le m)
$$

covers exactly all groups of six consecutive internal vertices. Its fitting
condition gives $r+6<m$, and conversely every such internal group has a start
of this form.

For $m\ge229$, the first 38 disjoint groups occupy positions 1 through 228.
There are $m-229$ remaining internal positions and two endpoints. Thus
$T\ge38L+m-221$. The draft's substitutions are correct:

| Assumption | Derived retained-square inequality | Excluded lengths |
| --- | --- | --- |
| $L=25$ | $36m+764+2s_0\le9214$ | $m\ge235$ |
| $L=26$ | $36m+802+2s_0\le9214$ | $m\ge234$ |

At $L=25$ and $m\ge234$, the same inequality gives $2s_0\le26$, so
$s_0\ge14$ is incompatible. No empty-square lower bound is inferred.

For $m\ge235$, the first 39 groups occupy positions 1 through 234.
The lower total is $39L+(m-235)+8$. At $L=24$ this is $m+709$;
at $L=23$ it is $m+670$. At $m=235$, the respective extra premises
$s_0\ge6$ and $s_0\ge25$ make the retained-square expression at least
9216 and 9215. Both exceed 9214. The proof correctly handles larger lengths
by monotonicity and smaller lengths directly.

The shortfall theorem is also correct. For $m\ge235$,

$$
T+\sum_{b=0}^{38}\max\left\{0,25-\sum_{j=1}^{6}\alpha_{6b+j}\right\}
\ge m+748.
$$

Combining with the retained-square inequality gives a shortfall of at least
$36m-8431+2s_0\ge29+2s_0$. Therefore a shortfall upper bound of $28+2s_0$
at those lengths excludes them. This theorem requires no universal six-count
floor, reference catalogue or potential certificate.

The sufficient example with every group sum at least 23 and at most 14 groups
below 25 is correctly stated. Each such group contributes at most two to the
shortfall, giving at most 28. The draft explicitly leaves both hypotheses
unproved and distinguishes these groups from endpoint-equality occurrences.

For closer correspondence with the new checked proof, the sentence beginning
“Substitute $T=9179-35m-2s_0$” may be replaced by:

> Combining this estimate with $T+35(m+1)+2s_0\le9214$ gives a shortfall
> of at least $36m-8431+2s_0\ge29+2s_0$.

The exact identity used by the present wording is available earlier in the
paper, so this is a dependency simplification rather than a correction.
The title “Necessary total shortfall for at least 235 edges” would also state
the theorem's actual range more precisely than “at length 235.”

## One proved six-count class

The $0123041$ statement matches the completed actual-snake theorem and reversal
theorem from milestone124. The normalized vertices
$(0,1,3,7,15,14,30,28)$ are correct. The six count lists have 126 occurrences
on 105 distinct corners, with $85+19+1=105$ distinct corners and
$85+2\cdot19+3=126$ occurrences. Keeping repetitions is essential and is
stated correctly. The draft's 3649 retained inputs and 5746 deductions agree
with the saved certificate account.

“No additional cycle exclusion is needed” correctly describes the selected
certificate. It does not remove the ordinary path and cycle conditions in the
underlying necessary encoding.

The status paragraph correctly distinguishes 34 canonical words, 21 reversal
classes, one completed six-count class, eighteen other native-negative classes
still requiring checked deductions, and two unresolved classes. The bank
minimum 31 is explicitly described as finite evidence. The exact-four
exclusions are correctly distinguished from a lower bound on the sum.

## Pair theorem and endpoint occurrences

The $012032$ proof correctly uses the exclusions of second count at most one,
pair caps $(2,5)$ and pair caps $(3,4)$, together with reversal. Both counts
are at least two. Ordering a hypothetical sum-at-most-seven pair leaves
precisely the two cap cases used in the proof. The three complete witnesses
attain $(2,6),(3,5),(4,4)$; reversal gives the other ordered pairs.

The endpoint paragraph correctly treats $(2,6)$ and its reversal as completed,
while retaining the two pending cases needed for the universal equality
statement. A witness satisfying the stronger assertion is not promoted to
a general theorem.

The conditional occurrence bound 13 is correct. With a nonempty set of
qualifying starts, all first counted vertices are distinct, and the second
counted vertex at $\max I+4$ is distinct from every one of them. They all
belong to the same intersection of two distance-two spheres, of size at
most 14. Nonempty qualifying starts imply a nontrivial snake, so its two
endpoints are distinct. The empty case is handled separately. This argument
does not count low-total six-block exceptions, as the draft explicitly notes.

## The unresolved 0120324 class

The prefix/suffix indexing is correct. The prefix is $012032$ at start $r$;
the suffix is canonically $012314$ at start $r+1$. Its middle internal count
is $\alpha_{r+4}$. If this equals two, the checked prefix exclusion forces
$\alpha_{r+1}\ge3$, and the suffix theorem supplies
$\alpha_{r+2}+\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}\ge19$.
The total is at least 24, contradicting a cap of 22. The resulting six
intervals exactly match the completed actual-snake result in milestone125.

The abstract tuple $(2,4,3,4,2,3)$ is used only to show insufficiency of the
explicitly reviewed inequalities. The draft does not claim it is a snake or
that the review covers every historical exclusion. The three timeouts remain
inconclusive and are accurately distinguished from a complete model or proof.

## Precision of verification wording

The new global Lean statements use the existing count that records every
empty square at its four corners. The conversion to the paper's ordinary
empty-square count $s_0$ was mathematically inspected and independently
enumerated. The milestone125 proof review expressly states that no new Lean
conversion lemma was compiled. The factor four is correct, and this creates
no mathematical gap in the paper's ordinary-square inequalities.

For exact reporting, prefer:

> The corresponding actual-snake count and incidence deductions have
> passed Lean.

to an unrestricted claim that the newly printed ordinary-$s_0$ statements
themselves were compiled verbatim. The verification appendix or archive can
state that each ordinary square contributes four corner incidences. There is
no need to add an implementation identifier or a new mathematical definition
to the main text.

The fragments introduce no unnecessary named mathematical object. Their
existing counts, explicit shortfall sum, ordinary indices and conditional
premises are sufficient. No substantive mathematical correction is required.
