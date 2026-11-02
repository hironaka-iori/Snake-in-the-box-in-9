# Current mathematical status and continuation priorities

## Milestone 103 checkpoint

Lean checked the general implication from successful joint traversal to
the existing prefix checker. Both source and target digit schedules, the
rejected-branch rule and the potential-width checks are covered. There are
11 checked modules and 26 distinct theorem axiom audits.
Only two reusable implementation definitions were added: branch selection
and joint traversal. No mathematical terminology or manuscript definition was added.

Four matched sequential comparisons passed, including transfer to the
original full context checker:

| Profile | Direction/history | Baseline seconds | Joint seconds |
| --- | --- | ---: | ---: |
| completed | 99/37 | 58.703 | 83.422 |
| completed | 0/0 | 59.734 | 85.609 |
| conditional | 99/37 | 61.734 | 29.969 |
| conditional | 0/0 | 122.250 | 71.766 |

Each pair uses the same imports, weights, potential roots, clipping bound,
acceptance root and candidate codes. No other Lean compiler was active at
launch. These are end-to-end module times from one pair per profile and
context; unrelated system activity was not isolated. They do not establish
a universal performance ordering.

The provisional batch choices, based on total time for the two contexts in
each profile, are completed: baseline; conditional: joint.
The batch should preserve a fallback for a context that exceeds its limit.

These contexts were already certified. Coverage therefore remains six of
791 contexts per profile: 34,701 accepted edges for the completed profile
and 34,148 for the conditional profile. There are 785 contexts per profile
still pending. Comparisons do not add distinct graph coverage.

Prepare one resumable sequential batch for all remaining contexts, reusing the six existing certificates per profile. Reuse one verified reduced check per identical acceptance root, weight expression and potential-root pair, then prove each original context by the bounded transfer. Select the baseline or joint method from the measured evidence, with a fallback for timed-out contexts. Assemble the original complete-graph theorem only after every context and every missing block are covered. Do not start another series of isolated timing pilots.

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

The current paper is revision 96, by Iori Hironaka, Tommy Ma and Steven Zhan.
Its existing editor and repository sources both have SHA-256
`7d4d974bc353ca723e4a5362b0960610d959dfe622b115b629968818c178875c`.
The 134 statement blocks, 199 resolved labels, 55-row history table and all
printed witnesses pass source checks. The original appendix body and all
metadata are preserved. The compiler could not start before processing the
source. The next scheduled full paper revision is milestone 106.

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

Milestone 97 also verifies the weaker profile with 012034 floor 18, keeping
the other eight original target floors fixed. Its potential has slope 496 and
range 602, giving $4696m\le1103530$ and conditional integer bound 234.
The least pending floor vector inside the original integer box is
$(16,18,16,16,16)$. The original stronger profile below remains valid as a
separate sufficient comparison with range 600.

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
| 012034 | 18 suffices; original target 20 | Pending; case7302 retains the stopped target-20 replay |
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

Milestone 83 prepared the case7302 target-20 proof. Its replay is currently stopped. All 121 semantic shards and
their combined interpretation passed, giving 127 modules before refutation
replay. The generated compact refutation, original export simulation and
reduced export simulations passed. Selected Lean replay and final geometry
remain pending. Inspect its saved checkpoint and actual
process before restarting anything.

Adding only this unproved floor gives exact finite mean 9259/19 and scaled
potential range 11301 at denominator 19. Its bound 20965613/89059 still
rounds down to 235. It raises 1,043,097 weights over the completed-share
model. All-edge checking and three Lean arithmetic audits do not discharge
the added local premise or the full graph interpretation.

## Earlier proof interfaces and development record

The following paragraphs preserve earlier milestone observations. Their
pending-job statements describe those snapshots. The milestone 103 checkpoint
above supersedes them: both 127-class batches and their assembly are complete;
case7302 is stopped. The remaining tasks are listed in NEXT_AGENT_PROMPT.md.

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

Milestone 81 closes the forty recovered short-rule filters: 66 theorem audits
across eight modules, covering both orientations and every fitting represented
placement. A separate exact builder-loop comparison checks 23,561,280
direction/count pairs, with source reconstruction and complete input hashes.
It reuses 970 pinned certificate objects and freshly checks three small support
sources. It does not rebuild the entire inherited closure.

Milestone 84 closes all three history-exclusion guards, with 38 audits across
eight modules. The actual emitted IDs recover each unique eleven-direction
word, and its count lower bound three excludes the digit cap two. All three
count proofs and five small helper lemmas were checked afresh against the
current window bridge. An exact isolated-loop comparison covers all 37,875
history/direction pairs and all count codes for the three active guards.

Milestone 85 supplies the exact 1,378-key reference table: 1,287 keys from the
235 catalogue and 91 additional keys from the 236 catalogue. Twenty-seven
modules passed 103 Lean audits, including the full table and retention in
both orientations at every fitting offset. The final theorem retains the
two closed catalogue-refutation premises. The key data and their membership
proofs are checked; their closed refutation dependencies have not been imported
into the current local environment. A bounded provenance search and exact
source pins document this distinction. The isolated builder-filter comparison
agrees on all 23,561,280 direction/count pairs.

Milestone 87 adds 27 Lean theorem audits across four modules. It combines
all retention families, defines an executable bounded numeric predicate and
proves that every fitting actual snake step passes it under the same two
reference-catalogue premises. A retention cover contains every accepted key;
exact table equality is a stronger sufficient condition. Given finite coverage
and the two endpoint-column identities, the checked assembly assigns an
in-bounds saved edge to every step of the complete actual state walk.

Two independent executable audits verify exact accepted-code equality on all
36,904,896 compatible candidate keys, the 4,947,008 saved rows, their ordering
and every endpoint. All 791 compatible blocks match; all 37,084 incompatible
blocks are empty. Full candidate keys are unique, while 206,589 endpoint pairs
have multiplicity two. Keep edge identity as (direction, history, count code).
The Python checks do not discharge the concrete Lean coverage or endpoint
premises, and do not certify equality with the executable Lean predicate.
The 791 blocks share only 127 distinct count-code sets. A shared six-way
decision diagram with 3,981 nonterminal nodes reconstructs every set and
block exactly, occupying 29,924 compressed bytes. Milestone 88 supplies the generic coverage implication and one concrete
checked context; the complete finite certificate remains open.
The combined imports reuse hash-checked existing proof objects; no complete
dependency rebuild is claimed.

Milestone 88 adds 26 Lean theorem audits. A rejection box is a product of
six count intervals with a checked original-rule witness. A six-way coverage
tree proves that every vector is either accepted by a membership diagram or
contained in one of these boxes. The generic theorem proves numeric retention
implies diagram acceptance; its actual-snake specialization retains the two
reference-catalogue premises. The direction-0/history-0 pilot supplies the
finite premises: Lean checks all 375 witnesses, the coverage equation and the
resulting retained-code theorem. It has 723 distinct tree nodes and 6,123
accepted codes; the three concrete proof checks took 92.594 seconds.

The computational reconstruction still matches every saved block. Moreover,
all 127 membership classes have a common box cover available across every
context of that class. Pruning yields 82,659 class-box occurrences, compared
with 356,548 direct direction-box occurrences. This suggests 127 shared
geometric checks. Each context still needs its own rule witnesses; milestone 88 stored example
witnesses, and milestone 89 supplies every context-specific list. The full all-context Lean
certificate and identification with the saved full-key rows remain open.
These generic and pilot results do not give a new global bound.

Milestone 89 records 28 additional Lean theorem audits. History-free
witnesses transfer across bounded history IDs of the same direction. Shared
assembly pairs an equally long witness list with the fixed geometric box list,
including the three contexts whose history witness occupies position zero.
All 543,827 witness occurrences in 791 contexts have been materialized and
checked computationally, compressing to 211 aligned lists and 4,387 witness
constructors. Their complete concrete Lean validity equations remain open.

All 127 shared cover trees are generated and pointwise replayed on 5,925,312
class/code pairs. A balanced table lookup is proved equivalent to the original
list at every index and default. Its concrete graph table and the geometric
coverage equations for classes 0 and 1 pass Lean. The class-1 proof module took
51.828 seconds; earlier direct and array-box experiments were stopped without
completion after 685.187 and 475.312 seconds. These concurrent timings do not
give a controlled speed ratio. The sequential full-class batch is active in
tool session 23168; its frozen checkpoint covers only classes 0 and 1.

Case 7302's original replay stopped at Check66 after its 300-second limit. A
first resume failed while replacing a stale temporary output. Both attempts
are preserved. The unique-output resume, tool session 14427, uses a 900-second
limit and has passed Check66 in 130.02 seconds. It reuses unchanged proof
sources and completed modules. Inspect actual processes before any restart.
Final geometry, reversal and the local-share audit remain pending.

Milestone 90 adds 17 Lean theorem audits. Balanced lookups preserve the exact
505-direction and 1,378-reference tables, including out-of-range defaults.
The class-1 certificate now gives retained-code membership for directions
1, 3, 307, 308, 310 and 312, for every bounded history under the original
predicate. Its six assignments contain 3,840 witness checks, and the proof
module passed in 21.125 seconds, excluding data and shared table checks.

Compatibility and count conditions are separated by a checked general
identity. A normalized direction-pattern expression permits reference keys
with the same shape and count-list length to share the shape calculation.
Concrete compressed descriptors and their full assembly remain unchecked.
The computational plan has 507 base validity jobs and three history heads,
covering all 791 contexts. Its 357,823 entries contain 15,353 distinct shape
tests and 2,651 count tests, together with 508 outer and 2,329 catalogue
guards. Every saved direct/factored Boolean comparison passes. These are
valid saved entries; the experiment alone proves no general equivalence or
speed improvement. Test reference-shape reuse on the same six-job pilot
before expanding it throughout the finite batch.

At the milestone90 snapshot, the existing geometric process has successful
receipts for classes 0 through 12; its full 127-class batch remains active.
The case7302 replay has 449 distinct successful modules
(455 raw successful rows). Its local-share theorem and
final audit remain pending. Both live processes must be inspected before
any restart. The checkpoint contains immutable observations and a delta log
archive. The upper-bound and reference-premise limitations remain unchanged.

Milestone 91 completes the reference-pattern reuse experiment. Three generic
Lean audits certify bounded cache lookup with complete descriptor equality;
five concrete audits check 156 patterns, two count lists, all six assignments
and the same membership conclusion as the direct pilot. The original 3,732
reference entries and 108 nonreference entries remain covered. The two direct
theorems are rechecked for timing and are not new results.

Direct proof trials took 18.812 and 37.875 seconds; cached trials took 24.203
and 28.016 seconds. Cached timings include descriptor correspondence and
assembly. Additional generic and data setup took 46.125 and 45.219 seconds.
Two other Lean processes were active throughout; the small concurrent sample
does not establish a speed advantage. The selected method for the full witness
batch is the direct balanced-lookup checker. Do not repeat the cache benchmark
without a materially changed representation or a new reason.

The milestone91 snapshot records geometric classes 0 through 19 and 493
distinct successful case7302 modules. Both existing processes continue; the
full geometry batch and local-share theorem remain pending. Use the newer
snapshot and actual process state when continuing. The complete context
assignment, full-key membership and endpoint identities remain open.

The remaining structural work is to supply the two closed reference
catalogue proofs and a concrete Lean retention cover with endpoint-column
identities. The universal conditional indexing argument is now supplied.
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

Milestone 82 supplies another exact obstruction on the completed-share graph.
A four-edge cycle of mean 483 has every count symbol below six. Nonnegative
bonuses that vanish on such edges preserve this mean. Even range zero cannot
meet the current 234 criterion: 227*483 falls short of 111960 by 2319. Six
Lean audits check the arithmetic, separately from the exact array checks.
This does not establish that the graph cycle occurs in an actual snake.

On this witness, the pending 012034 floor 20 occurs twice and 012340 floor 16
once. Assuming both increases its mean to 497. This concerns one cycle only;
the full graph mean and the other pending targets remain unresolved. These
two targets are useful next tests within empty-square charging.

## Preservation and environment

Use the repository sources and milestone receipts as the reproducible record.
The dated handover contains detailed environment paths and earlier evidence.
Milestone 77 saves its coverage checks, superseded memory-intensive attempts
and replay snapshot. Milestone 78 saves the selector/state checks. Milestone 79 saves the encoded
guards, interval-filter assembly, catalogue audit and a later replay observation.
Milestone 81 saves the forty-rule theorem, independent review and exact comparison.
Milestone 84 saves the three-history theorem. Milestone 85 saves the exact reference
table, conditional theorem, provenance review, exhaustive comparison and a later
case7302 observation. Milestone 86 incorporates these results into the paper; its manifest identifies that revision. Milestone 92 contains the current shared handover versions and later proof-process observations.
Build objects remain local and are excluded from Git. Reproduction
uses Lean 4.19.0 with hash-checked inherited support; it does not rebuild the
whole inherited dependency closure.

The smaller coverage implementation splits at six directions, then splits the
largest branch once more. All twelve branches, its seven subcases, rejected
prefixes and their assembly require Lean proofs. The
generation script itself is outside the trusted proof argument. Preserve the
completed case7305 receipts; inspect actual processes before starting any
new case. Do not repeat its successful unchanged replay. Tool session numbers are local to the original execution context.

Milestone 88 freezes 348 successful case7302 replay rows, including 84 newly observed since milestone 87. The log archive and hash scopes are explicit. This is a partial snapshot; the final local-share theorem remains pending.

Milestone 89 freezes 389 distinct successful replay modules, including 41 newly observed since milestone 88. The raw record contains 395 successful rows because the inherited driver repeats composition rows when resumed. Duplicate rows are not counted as new modules.
