# Reusing the ordinary five-count certificate pipeline

The shortest route reuses the ordinary tagged semantics from milestone 72
and the original-clause-ID LRAT export used in milestone 109. No new
endpoint-unit interpretation, joint pair counter, or cycle theorem is needed.
The source inspection below identified the reusable chain. The base-window
export has since passed reconstruction and packed replay in Python. No Lean
process was run by the exporter; compilation remains a separate obligation.

## Completed base export and deferred short export

`scripts/export_base.py` imports the shared implementation in
`scripts/export_short.py`. Both reject an input without a matching successful
native replay receipt, reconstruct every original clause, preserve original
clause IDs, and refuse to overwrite an existing export receipt.

The base case is the canonical word `012301430`, with internal bounds
`[(0,21),(0,21),(6,21),(3,3),(3,3),(3,3),(5,5),(2,2)]`.
Its saved proof contains 1,340 deductions, 106,510 hints and 2,353 core clauses.
There are no appended cycle cuts. A complete bijection places the 1,485 active
proof variables first, below the checker offset 2400. All 4,568 variable
meanings and every counter literal are remapped consistently; no semantic
table entry is inferred from the old variable numbering.

The base export receipt is `data/proof-plan-base.json`, SHA256
`20863f459ee8cf7371783c1146b72bf28a8ea59d71161349a1bfea91bb0d5128`.
It provides exact source and generated-file hashes, the ordered list of 15
Lean modules, the existing checker object and its receipt, and the final
theorem name. There are 18 proof segments and five grouped checking modules.
Packed replay and checkpoints passed Python simulation. The final source
`lean/ActualBase138.lean` composes `Tags.refuted_of_sat` and `refuted_bridge`,
then normalizes an arbitrary fitting snake window. It prints axiom reports
for the finite refutation, the actual-snake bridge and the concrete row
exclusion. The source makes no parity or endpoint-location assumption.

The used counter indices are `0,2,3,4,5,6,7,8,9,10,11`: the endpoint budget
and both count bounds at internal centre indices 3 through 7. Counter 1,
which encodes the lower bound 6 at the preceding centre, is unused by this
core. The final statement retains that original hypothesis; no strengthened
claim is recorded here.

The first base export stopped on the reused generator's Windows cp932
encoding before any generated Lean source was installed. Its exact source
snapshots, transformed proof and semantic data remain in
`work/export-base-attempt1-cp932` and
`data/selected-core-semantics-base-attempt1.json`. The identical exporter
succeeded under Python `-X utf8`. No solver or Lean was run in either attempt.

For the short word, the sole main eight-cycle cut was SAT, as checked in
`data/closure-model-review.json`; it does not suffice. The final input with
all 19 added cuts has a native proof of 19,338 deductions and 2,329,967 hints,
using 4,358 core clauses and 13 of the added cuts. Its original native record
stopped before replay at the two-million-hint guard. The separate
`data/replay-short.json` records a complete replay of the same proof under
a three-million-hint guard. The shared exporter checks both receipts and
their hash link. The stronger short-window Lean export remains deferred
while the substantially smaller base proof is checked. Running
`python -X utf8 scripts/export_short.py` performs that source export and
Python simulation only; it does not launch Lean or a solver.

## Input and existing semantic coverage

Use the exact input already prepared in `work/short/encoding.json`:

- Directions: `[0,1,2,3,0,1]`.
- Window: `[0,1,3,7,15,14,12]`.
- Bounds: `[(0,3),(0,3),(0,3),(0,5),(0,2)]`.
- Radius: 9, hence the full cube.
- Variables: 2384 before adding cycle clauses; ordinary clauses: 96504.
- Endpoint location restrictions: none.

These are upper caps. A resulting theorem would exclude every fitting
`012301` window with all five counts at most `(3,3,3,5,2)`, a stronger
statement than exclusion of the exact tuple in the saved cycle.

The constructor is

```python
gen_lean_sat.TaggedEncoding(window, bounds, radius=9, ends=2)
```

It supplies the ordinary endpoint-budget counter and five individual upper
count counters. All have positive thresholds supported by the existing
generic semantics. The absence of positive lower bounds is allowed.

Add each retained cycle as

```python
assert gen_lean_sat.is_cycle_set(vertices)
assert set(vertices) <= enc.B
enc.add([-enc.var[v] for v in vertices], ('cut',))
```

The proposed set `[0,1,3,7,8,12,14,15]` is an eight-cycle: one cyclic order
is `0,1,3,7,15,14,12,8,0`. All vertices are distinct before closing, and
every vertex has two neighbours in the set. The generic tag is sufficient
for this cycle or all nineteen cycles discovered by the earlier search.

In `work/final_lean/LocalWindowTags.lean`, `ckCut` checks that a clause is
nonempty, all literals mean absent selected vertices, and every represented
vertex has at least two neighbours in the represented set. `sound_cut`
derives the clause from `Axioms.acyclic`. `LocalWindowBridge.frame_axioms`
already supplies that axiom for actual snakes. No assumption that a cycle is
a coordinate square or six-cycle is imposed by this route.

## Prefer preserving original variable and clause IDs

The prepared input has only 2384 variables. Provided the finished proof uses
no literal ID at least 2400, the existing `LratFast` offset 2400 suffices.
There is no need to solve again merely to compact variable IDs.

Use the finished full CNF and its finished LRAT proof with matching IDs.
The pure trimming function is

```python
lemmas, hints, core_ids = gen_lean_core.trim_lrat(raw_lrat, trimmed_lrat, nclauses)
```

It retains the dependency cone of the final empty clause, preserves clause
IDs, drops deletion lines, and returns sorted original input IDs. It supports
positive RUP hints; it explicitly rejects RAT hints.

Read each core clause directly as `enc.clauses[i-1]` for `i in core_ids`.
Check the entire rebuilt CNF against the pinned input, including the appended
cycle clauses. Do not infer clause provenance merely from a sorted-clause
lookup when preserving exact IDs is available.

Write `LocalWindowCnf/CycleWindow138.lean` in namespace
`Snake9.LocalWindow.CycleWindow138`, containing `window`, `bounds`, encoded
`raw`, and

```lean
def cnf : List (List Int) := raw.map (·.map decodeLit)
```

`gen_lean_sat.code(lit)` supplies the raw literal encoding. Metadata must
contain at least

```python
dict(module='LocalWindowCnf.CycleWindow138', core_ids=core_ids)
```

The original-ID arrangement is already used by
`milestones/109-relaxed-graph-test/scripts/regenerate.py`. A compact-variable
alternative appears in `milestones/72-four-count-proof-closure/scripts/certify.py`:
its `small` object remaps **every** variable meaning and **every** counter
literal, preserving counter indices and `.r` register coordinates. It is
valid, but unnecessary solely for this input's variable count.

## Semantic source generation

Set the output root and invoke the existing generator directly:

```python
gen_lean_sat.LEAN = str(output_lean)
tags = [enc.tags[i-1] for i in core_ids]
gen_lean_sat.write_module(name, 'CycleWindow138', meta, enc, tags)
```

The exact function signature is
`write_module(name, module, meta, enc, tags)`.
Required encoding fields are `nv`, `meaning`, and `ctrs`; using the complete
original `enc` is sufficient. It emits
`LocalWindowSat/CycleWindow138.lean` with:

- `meaning`, `ctrs`, and the core's ordered `tags`;
- a kernel-decided `checkAll ... = true`;
- `sat`, showing that every assignment satisfying the actual window axioms
  induces a satisfying Boolean assignment to the selected core.

No new hand-written count soundness theorem is needed. The existing `.hi`
counter interpretation checks each individual singleton-count cap. Ordinary
`.ends` semantics handles the global endpoint budget.

## LRAT source export

The pure source-export interface is

```python
gen_lean_lrat.set_width(bits, fast=True, off=2400)
gen_lean_lrat.DATA_DEF = 'noncomputable def'
stats = gen_lean_lrat.export(
    name, work, seg_hints, cp_every, group, True, output_lean, data_dir)
```

`work/name.cnf` must retain the original full CNF IDs, and `work/name.lrat`
must be the compatible trimmed proof. `data_dir/name.json` supplies the
metadata above. The exporter reads only the selected input clauses through
`core_ids`, and emits the ordinary `LocalWindowUnsat.CycleWindow138` modules.
Its `plan(core_ids, read_lrat(path))[3]` gives the number of live slots.
Choose an existing supported word width (13, 14 or 15) covering those slots
and all packed literal values. Confirm the matching checker object is present
in the pinned environment. Do not confuse the large original clause numbers
with live slot numbers: original clause numbers are mapped by the exporter.

The `check=True` argument simulates the proof and checkpoint operations in
Python; successful Lean compilation of every emitted check remains required.

## Final actual-snake theorem

Compose the two ordinary results exactly as in milestone 72:

```lean
theorem refuted : Refuted window bounds :=
  Tags.refuted_of_sat sat unsat
```

`LocalWindowBridge.refuted_bridge` takes, in order:

```lean
refuted_bridge p P r href hc hlen hr hP hb
```

Here `hc : Canon window directions`, `hlen : bounds.length + 1 = directions.length`,
`hr : r + directions.length ≤ m`, `hP` maps every actual direction through
the coordinate permutation, and `hb` gives the five actual count bounds.
The concrete window/canonical-word and length checks are finite kernel checks.

For the desired hypothesis `canon (dsOf p r 6) = [0,1,2,3,0,1]`, copy the
short normalization argument in
`milestones/132-odd-pair-endpoint/lean/ActualCounters132.lean`, theorem
`actual_normalized_frame`, changing only the direction word. It invokes
`Snake9.Guards79.actual_canonical_frame p r 6 hr` and `mkPerm_spec` to obtain
the required `P`. This avoids adding named-coordinate assumptions to the
final statement. The five caps can then supply `hb` by five cases; their
zero lower bounds require no positivity theorem.

The intended final conclusion is `False` from the fitting canonical word
and the five upper caps. Equivalently, every fitting window satisfies at
least one of the lower bounds `(4,4,4,6,3)` at its five internal positions.
No endpoint location, parity, total snake length, or unproved external
contradiction premise should remain.

## Check order and outstanding work

1. Pin and verify the finished input, every extra cycle set, proof and selected
   clause IDs; verify literal bounds and any renaming if used.
2. Check the CNF source, then the generated tagged semantic module.
3. Check the LRAT data and proof modules in their import order, then its
   final `unsat` module.
4. Check `refuted`, the arbitrary-coordinate bridge and the canonical-window
   wrapper, printing their axioms.

There is no identified missing mathematical lemma in this ordinary pipeline.
The remaining obligations are source/input identity, the complete certificate
checks, and final assembly. The saved-cycle consequence and any new minimum
mean require a separate graph update; they do not follow from source export.
