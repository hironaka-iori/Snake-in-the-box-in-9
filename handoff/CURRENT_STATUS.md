# Current mathematical status and continuation priorities

## Result and evidence boundary

Length means edges. The maintained project interval is

\[
191\le a(9)\le235.
\]

The lower bound has an explicit checked witness. The upper bound uses the
inspected contributor theorem and saved audit; this continuation has not rebuilt
that entire proof independently. The exact optimum remains unresolved.
The conjecture 196 has neither a matching construction nor an optimality proof
in this work. The proposed improvement to 234 remains conditional.

The current paper is revision 76, with authors Iori Hironaka, Tommy Ma and
Steven Zhan. Its repository and editor copies have SHA256
`3c67d4c168ee7fe463f2ea49da3459f2178ee2a655fd45f9ed374f88126f43dd`.
Source checks preserve all 116 previous statements and add seven, giving 123;
all 13 printed paths and 118,673 vertex pairs were checked. The built-in
compiler failed before source compilation. No new PDF or layout check is
claimed. Milestones 77 through 80 add proof interfaces and a completed local share theorem without revising the paper.

## Chosen route: charge empty squares

Let a nontrivial snake have \(m\ge1\) edges and \(v=m+1\) vertices. Let \(T\) be the total
singleton-square count and \(s_0\) the number of empty squares. The accounting
identities and charge budget are

\[
T+2s_0+35v=9214,\qquad
\Sigma\le48s_0,\qquad
24T+\Sigma+840(m+1)\le221136.
\]

Here \(\Sigma\) is the sum of scale-12 empty-square shares. Combining the
five-centre window charges and the boundary contribution 21, for \(m\ge9\), gives

\[
W+4200m\le1098960.
\]

The full proposed finite graph has 1,601,856 states and 4,947,008 edges. Its
recorded potential gives the conditional inequality

\[
496(m-8)\le W+600,
\]

so \(4696m\le1103528\). At \(m=235\), the left side exceeds the right side
by 32. This yields 234 only after every local premise, actual-snake graph
interpretation and complete potential check has been supplied.

Completed local shares, now including the checked 012310 share-12 theorem,
give mean 483 and potential range 551. The exact comparison is 157625/669,
with integer bound 235. Its weight and potential hashes match the earlier
comparison that assumed this lemma. The previous completed subset had mean 480
and range 536. These finite-model calculations do not independently replace
the contributor's global theorem; graph interpretation and Lean potential
replay remain required.

## Local share catalogue

The shapes below use canonical direction labels. The listed floor is the sum
of the five internal scale-12 shares, independently of their singleton counts.

| Shape | Target floor | Final target theorem status |
| --- | ---: | --- |
| 012031 | 16 | Checked, case7300 |
| 012032 | 16 | Pending, case7301 |
| 012034 | 20 | Pending, case7302 |
| 012301 | 16 | Pending, case7303 |
| 012304 | 16 | Checked, case7304 |
| 012310 | 12 | Checked, including reversal, case7305 |
| 012314 | 16 | Checked, case7306 |
| 012340 | 16 | Pending, case7307 |
| 012345 | 16 | Pending stronger target, case7308; the weaker floor 12 is checked |

Case 7305 completed all 465 source modules and 100 printed theorem audits,
including geometry and reversal. Its selected sources and compact proof were
archived and restored byte-for-byte. No case7305 proof process remains active.
The combined catalogue passes 35 audits and retains exactly five local targets:
7301, 7302, 7303, 7307 and 7308. Earlier pending checkpoints remain historical evidence.

## Proof interfaces and remaining work

Milestone 75 supplies longest-suffix history recognition, credit lookup and
count coding. Milestone 77 supplies direction-table coverage and the numeric
history interface. Milestone 78 proves the actual numeric history update and
assembles the direction, history and counts into one consistently numbered
state sequence, with 29 theorem audits. A direction window uses the oriented table ordering:
132 eight-direction states and 505 nine-direction edges. Reversal classes are
different objects and cannot be used as these IDs.

For \(m\ge9\) and edge start \(r<m-8\), the six count symbols are at centres
\(r+3,\ldots,r+8\). The source retains the first five and the target the last
five. The entering count is at \(r+8\), and credited shares lie at centres
\(r+4,\ldots,r+8\). There are \(m-8\) direction edges and \(m-7\) shape states,
including the terminal state. Shorter paths already satisfy the intended upper
bound. Count symbol six means the interval \([6,21]\).

Milestone 79 adds 31 theorem audits. Its count-slice, digit, encoding-injectivity,
reversal and saturation results connect encoded graph tests to actual counts.
Every actual snake survives the ten completed milestone 72 interval filters,
at all three offsets and in both orientations. The closed local certificates
are imported from pinned existing objects, without a clean dependency rebuild.

The remaining retained-edge work is the 1,378-key reference union, forty
recovered short rules, three history exclusions and the exact retained-array
index. The reference theorem sources and contributor logs were audited; their
complete union is still uninstantiated in the current environment.
Every three-ID credit needs every compatible eleven-direction interpretation;
forgotten coordinate returns can produce several variants. Alternative lower
bounds on the same five shares combine by maximum. Complete the finite
potential replay and the five remaining target share theorems before removing the 234
qualification.

An executable audit checks the exact Python selector assignments on all 37,875
history/direction pairs and agrees with the strict scan proved in Lean. It is
separate from the Lean theorem; the Python interpreter is not encoded there.
Neither check proves retained-edge membership or credit validity.

## Results that constrain further optimisation

Milestone 74 gives exact short-walk obstructions for six specified weakenings
of the target share rules. Under the current boundary budget, a different
constant slope or potential on each entire weakened graph cannot exclude 235.
These are graph obstructions; actual snake realizability was not established.

Productive alternatives therefore require additional information: exclude a
walk through a new geometric fact, restrict to reachable or realizable states,
or improve the boundary contribution with state-dependent endpoint information.
These remain research directions, with no promised numerical improvement.

## Preservation and environment

Use the repository sources and milestone receipts as the reproducible record.
The dated handover contains detailed environment paths and earlier evidence.
Milestone 77 saves its coverage checks, superseded memory-intensive attempts
and replay snapshot. Milestone 78 saves the selector/state checks. Milestone 79 saves the encoded
guards, interval-filter assembly, catalogue audit and a later replay observation. Build objects remain local and are excluded from Git. Reproduction
uses Lean4.19.0 with hash-checked inherited support; it does not rebuild the
whole inherited dependency closure.

The smaller coverage implementation splits at six directions, then splits the
largest branch once more. All twelve branches, its seven subcases, rejected
prefixes and their assembly require Lean proofs. The
generation script itself is outside the trusted proof argument. Preserve the
completed case7305 receipts; inspect actual processes before starting any
new case. Do not repeat its successful unchanged replay. Tool session numbers are local to the original execution context.
