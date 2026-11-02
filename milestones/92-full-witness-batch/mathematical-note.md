# From shared witness checks to assigned contexts

The finite retention proof has two components. Each geometric class must
contain every code retained in its assigned contexts, and every retained
step must be assigned to its correct saved class. Successful receipts specify
which finite checks have finished; generated sources alone are not proofs.

## Shared witness jobs

Let \(B_1,\ldots,B_r\) be the ordered rejection boxes of a geometric class.
A base job is a direction index \(d\) and an equally long witness list.
Its check requires every witness to be independent of history and valid
at history zero. The transport lemma then gives validity at every \(q<75\).

The original geometric cover accepts a count vector or puts it in a
rejection box. A retained vector cannot lie in a box with a valid exclusion
witness. A checked base job and the original cover therefore imply

\[
\operatorname{Keep}(q,d,c)\Longrightarrow\operatorname{Accept}_{k}(c),
\qquad q<75,\quad c<6^6,
\]

where \(k\) is the geometric class. The retention predicate and its history
guards are unchanged.

Three contexts require a history witness at position zero. Check each tail
as a history-free base job and the leading witness separately at its original
history. Restore the leading box and witness together, preserving the full
ordered cover and length condition.

The saved plan contains 507 base jobs, 210 base lists and three history
heads. It reconstructs all 791 original contexts, preserving box positions
and witness indices. The six previously checked class-1 jobs are reused by
definitional equality. The other generated validity checks use the direct
balanced-lookup validator selected in milestone91.

## Per-class context keys

For each class \(k\), publish the ordered list of direction/history pairs
assigned to it. Write its membership set as \(K_k\). Finite checks connect
every listed pair to a checked base job and any required history witness.
Further equalities identify the list with the shared class table and its
original diagram root with the shared root table.

The common per-class interface is

\[
(d,q)\in K_k\ \land\ c<6^6\ \land\operatorname{Keep}(q,d,c)
\Longrightarrow\operatorname{Accept}_{k}(c).
\]

This exposes the direction/history pair rather than a private witness-list
choice. The full family becomes available only after every class passes.

## Count-independent context assignment

For bounded indices, the source condition is

\[
q=0\quad\text{or}\quad h(q)=s(d),
\]

where \(h\) is the recorded compatible source shape and \(s(d)\) is the
direction word's source-shape index. History zero is an explicit exception.
The retention predicate implies this condition. Recovering the supplied
direction index from its decoded word uses \(d<505\).

An independent comparison of all \(505\cdot75=37\,875\) bounded pairs shows
that this condition selects exactly the 791 saved contexts. The assignment
certificate consequently needs no count-code enumeration. The target-history
condition remains in the retention predicate; the source condition suffices
for this particular necessary-condition argument.

Let \(\kappa_0(d)\) be the saved class at history zero. Define

\[
\kappa(d,q)=
\begin{cases}
85,&d=177\text{ and }q\in\{43,70\},\\
89,&d=180\text{ and }q=68,\\
\kappa_0(d),&\text{otherwise}.
\end{cases}
\]

The default vector has 505 entries. Its classes at directions 177 and 180
are 84 and 88. The three overrides correspond to the three history witnesses.

For every bounded source-compatible pair, the finite certificate must show
\(\kappa(d,q)<127\), membership in \(K_{\kappa(d,q)}\), equality to the saved
block's class, and agreement with that block's root. Union membership alone
would leave the saved-class correspondence unresolved. Missing lookups use
an explicit absent value because class zero is valid.

Those facts and the complete per-class family imply acceptance by the correct
saved diagram for every retained bounded step. The assignment plan and proof
receipts distinguish the independent computation from the checked certificate.

## Suffix expansion for an exact saved-row comparison

For the next row-coverage proof, define the accepted suffix list recursively.
Write \(N(u,a)\) for the next diagram node after symbol \(a\), where symbols
run from 1 to 6. Set \(L_0(u)=[0]\) when \(u=1\), and \(L_0(u)=[]\)
otherwise. For \(j\ge0\), define

\[
L_{j+1}(u)=\mathop{\Vert}_{a=0}^{5}
  [\,a6^j+c:\ c\in L_j(N(u,a+1))\,],
\]

where \(\Vert\) denotes concatenation in increasing order of \(a\).
The intended induction states that, for \(0\le c<6^j\), membership in
\(L_j(u)\) is equivalent to diagram acceptance of the length-\(j\) radix-six
digit word, with each digit increased by one. Terminal 1 then supplies every
remaining suffix. The recursion uses the remaining length, so its definition
does not require an assumption about the numbering of diagram nodes.

The proof plan has two simultaneous induction statements. First, every
entry of \(L_j(u)\) lies in \([0,6^j)\). Second, membership is equivalent
to acceptance of the corresponding length-\(j\) digit word. At length zero,
the only possible code is zero and acceptance tests whether \(u=1\).
For the induction step, write uniquely
\(c=a6^j+b\), with \(0\le a<6\) and \(0\le b<6^j\).
The first digit selects \(N(u,a+1)\); the induction hypothesis identifies
the suffix \(b\). The range statement ensures that different leading
digits occupy disjoint intervals. It also supports a separate induction
showing that the lists are strictly increasing and have no repetitions.

This is a proposed next proof, not a checked result of this milestone. Its
purpose is to reduce the next concrete obligation to 127 equalities between
\(L_6\) at the saved roots and the independently exported ordered code lists.
The 791 block bindings would then supply full keys. Equality with the saved
row array and its endpoint columns would still require separate checks.

## Preferred definition of the proof graph

A separate equality to the external row array can be avoided if all later
certificates are checked on a graph defined directly in the proof. For each
bounded triple \((d,q,c)\), consult the saved block-class assignment. Reject
a missing block; otherwise accept precisely when its assigned class diagram
accepts the count digits. Let \(R\) list these triples in the fixed direction,
history and count-code order. Define the endpoint columns by applying the
existing source and target functions to each full key in \(R\).

The class-family and context-assignment hypotheses imply that every numerically
retained key belongs to \(R\). The endpoint-column identities follow from
their definitions. The previously checked walk-assembly theorem then applies
under the same two reference-catalogue hypotheses. `DefinedProofGraph.lean`
states these three conditional results; its successful receipt, when present,
determines whether the implementation has been checked.

This construction is the preferred continuation. Its essential requirement
is that all local-credit, weight, potential and budget certificates apply to
this defined graph. A certificate checked only on an external array cannot be
transferred by naming the two graphs alike. The raw state encoding is the
existing 1,601,856-state namespace; temporary cyclic-component renumbering used
by a search algorithm must not be mistaken for that namespace. The suffix
expansion and saved-row comparison above remain available for an exact
representation audit, without being a prerequisite of the defined-graph route.

The potential can be treated as a function on all natural-number state keys,
using a specified default outside its finite table. If every stored value and
the default lie in a common interval of width \(R\), that range bound holds
for every lookup. A potential inequality checked on every defined edge then
telescopes along the actual walk without a separate assumption that its state
key is present in an external table. Choosing zero as the default requires
zero to lie in the verified interval. This observation does not replace the
edge-inequality checks or certify any particular stored potential.

The current row definition is a specification using the bounded full-key
generator. The conditional proof does not execute that entire enumeration.
For subsequent finite certificates, work over the 791 present block bindings
and their accepted codes. A successful lookup implies membership in that
binding list, so a generic membership argument can transfer a checked
block-level inequality to every defined edge. This avoids evaluating all
\(505\cdot75\cdot46656\) candidate triples merely to reject missing blocks.

## Remaining obligations

Complete the class family and finite context assignment, instantiate the
defined-graph walk, and check the pending local shares, credit interpretation
and full potential on that graph. The two reference-catalogue premises remain
explicit. A partial class batch or a conditional graph theorem supplies no new
numerical upper bound.

The maintained project interval is \(191\le a(9)\le235\), using the inspected
contributor theorem and saved audit for the upper bound. Its complete
independent rebuild remains pending. The proposed improvement to 234 remains
conditional on the outstanding obligations.
