# Milestone 138: a checked exclusion on the competing seven-edge cycle

## Completed result

For every snake in Q9 and every fitting nine-transition window with canonical
word 012301430, the six singleton-square counts at positions3 through8 cannot
be (x,3,3,3,5,2) with x at least6. The statement allows any path length parity
and any fitting start. It has no endpoint-location assumption.

The final checked source is lean/ActualBase138Minimal.lean. Its four reported
theorems use only propext, Classical.choice and Quot.sound. The complete
chain includes14 checked CNF, semantic and LRAT modules plus this actual-snake
wrapper. The separate Credit138 arithmetic module also passed, with three
reports. data/proof-completion.json identifies all16 successful modules.

Normalize by translating the first vertex to zero and relabelling coordinates.
The window is 0,1,3,7,15,14,12,28,20,21. An actual snake supplies a selected
vertex set, endpoint indicators, the prescribed window, degree constraints,
at most two endpoints, singleton counts and the necessary cycle exclusions.
All retained2353 clauses have checked interpretations under those conditions.
The refutation has1340 deductions and106510 hints. Both the independent
Python replay and all Lean checks passed. The generic normalization proof
then transfers the contradiction to arbitrary snakes.

The core happens not to use the counter for x>=6. The proved theorem retains
that hypothesis. Removing it requires a checked semantic specialization;
it must not be silently dropped from the statement.

## Consequence for the saved graph

The seven-edge cycle in milestone131 contains the prohibited forward row:
edge992157, canonical word012301430, symbols(6,3,3,3,5,2).
The symbol6 denotes the whole interval[6,21]. Its original mean is3453/7
under the completed-share weights, and496 under the additional-share weights.

Deleting every row matching this full-nine condition removes that cycle.
The proof does not by itself assert a higher minimum mean. The completed
four-cycle survives with mean488 and the old potential restricts to the
remaining graph, so deletion alone leaves that profile's minimum exactly488.
The archived eighteen-cycle also survives. Its current completed-share mean
is3011/6, and it has no low-pair suffix occurrence.

Only the forward rule is justified from the six counts stored in each
nine-transition row. Reversing those six counts is not a valid full-nine
reversal: the reversed row needs two original counts absent from the state.
The shorter-window mask in audit/graph-next.md remains pending. The applicable
mask and source hooks are in audit/graph-base-next.md.

## Selected next calculation

Combine the new full-nine deletion with milestone137's proved allowance
of at most24 canonical012032 windows whose second and fourth internal
counts have sum at most9. Give credit C once per suffix occurrence, never
again for its overlapping prefix representation.

The saved four-cycle has two such events in four rows and mean488+C/2.
The eighteen-cycle has none and stays at3011/6. Their means meet atC=83/3.
This identifies a concrete first graph experiment; other cycles may prevent
attainment. Use exact integer weights by multiplying the entire credit
calculation by3 if necessary.

The arithmetic in lean/Credit138.lean is checked. In the inherited comparison

\[
\frac{1098960+8\mu+24C+R}{4200+\mu},
\]

the choices C=83/3 and mu=3011/6 give a value below235 exactly when

\[
R<\frac{7753}{6}.
\]

More generally, mu>=3011/6 and R<7753/6 suffice. These are conditional
numerical targets. No potential with this mean and range is asserted, and
the inherited reference/exclusion, share and graph-to-snake obligations
remain explicit. Evaluate both saved weight profiles, keeping their distinct
hypotheses and targets. Do not claim a smaller upper bound from removal of
one cycle or from the arithmetic theorem alone.

## Stronger short-window evidence

The canonical six-transition word012301 with five upper caps(3,3,3,5,2)
also has a native contradiction, after19 necessary cycle clauses were added.
Its retained proof uses13 of those clauses and has19338 deductions,
2329967 hints and4358 original clauses. Every deduction passed independent
Python replay. The initial replay guard was an implementation choice of
2000000 hints; a separate saved replay used a3000000-hint guard on the same
proof. No solver was rerun for that replay. Lean export and checking of
this stronger claim remain pending.

The sole-main-eight-cycle experiment was SAT. The complete assignment
passed all96505 clauses and has159 selected vertices with counts(1,1,1,1,1).
Its selected subgraph contains cycles, so it is not an actual snake.
It establishes only that this one extra cycle clause is insufficient
for that relaxation. Both positive and negative experiments are retained.
The endpoint-away input was prepared but never run because the unrestricted
base query was already UNSAT.

The witness screen covered135 distinct actual snakes and found no complete
count-and-shape matches. Its endpoint tests are therefore vacuous. The saved
cycle and catalogue audit found no prior matching exclusion among the
732 completed entries and ten later interval cases; this bounded comparison
is not a claim of novelty in the literature.

## Reproduction and saved attempts

data/proof-plan-base.json records the original exported chain. Fourteen of
its modules passed; its original final wrapper failed while loading an
unrelated catalogue dependency because a new generic module directory
shadowed older directories. The replacement ActualBase138Minimal uses the
exact existing normalization proof directly with minimal imports and passed.
The original failed wrapper, logs and exact source snapshots are retained.

A bulk dependency-copy repair was stopped in favour of the minimal wrapper.
All original dependencies were preserved. Only the newly created unused
copies were removed after path and hash checks; their attempt inventory and
cleanup receipt remain. Do not rerun restore_overlay.py for normal continuation.

The initial source export encountered a Windows encoding failure. That
attempt is retained; the same exporter succeeded in Python UTF-8 mode.
All source pins, inputs, proof files, successful and failed logs, objects,
and statement reviews are indexed by the checkpoint manifest.

## Paper and scope

The existing editor source and repository paper were updated in place,
with the same three authors and complete preamble. No definition was added.
Source structure and reference checks passed. The built-in compiler failed
before TeX execution in its Windows helper, so no new PDF or layout check
is claimed. Last full revision136; targeted update138; next full revision146.

The maintained interval remains191–235, with the documented incomplete
independent rebuild of the contributor upper proof. The optimum and196
remain unresolved. Milestone115 was observed live at1017/1397 modules;
never restart it without checking its recorded process and command.
The research goal remains active.
