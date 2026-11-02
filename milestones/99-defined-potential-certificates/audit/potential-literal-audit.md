# Independent audit of generated potential literals

The actual generated Lean source trees reproduce both saved potential arrays exactly. All **3,203,712 values** were compared, with zero mismatches. The successful numerical run took **0.890 seconds**, below the five-minute limit. No generator, compiler, solver, or existing research script was imported or invoked.

The checker parses every `n{d}_{i}` definition in the ten `CompletedValues99D1` through `D5` and `ConditionalValues99D1` through `D5` files. It follows the actual six child expressions and references, verifies the expected interval widths, rejects missing or forward references, and expands each referenced tree. It also parses each complete `roots` expression in `CompletedPotential99.lean` and `ConditionalPotential99.lean`, checks every balanced-table left-size field, and evaluates the lookup order for all 206 roots. This check uses the literal source bytes rather than the generator's internal tables.

| Profile | Parsed definitions at depths 1–5 | Root entries | Distinct root references | Compared values | Minimum | Maximum |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Completed | 2,456; 12,359; 4,268; 974; 177 | 206 | 177 | 1,601,856 | 0 | 551 |
| Conditional floor18 | 758; 5,050; 2,804; 829; 171 | 206 | 171 | 1,601,856 | 0 | 602 |

The parsed evaluation follows `PotentialTree99.value`. Its source body is checked against the six consecutive subinterval semantics used by the independent expander. The balanced lookup semantics were inspected in `BalancedLookup.lean`, whose exact bytes are pinned. Both potential definitions are checked to select root index `s/7776`, evaluate at `s%7776`, and apply `min 551` or `min 602`, respectively. The explicit upper-bound theorem statements using `Nat.min_le_left` are present. Every expanded value already lies within the cap, so the outer minimum changes no saved value. Four sample out-of-range root lookups also return the default; the full value comparison concerns precisely the valid state range.

The expanded little-endian int64 hashes match the saved arrays:

- Completed: `90ee55c9e675275f506b947223e36cfeddafc3fcb0a56d61122a5d3ab81e35a0`.
- Conditional floor18: `04effe853d3846049e1a300f90404a4a66df79498586a34d2aa92a1a5f0bb4b8`.

The requested pilot interval is $9720\le c<11880$, containing 2,160 codes. Using the expanded literal potentials gives:

| Profile | Direction | History | Accepted | Rejected | Tight accepted edges | Minimum slack | A critical code |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Completed | 35 | 0 | 143 | 2,017 | 83 | 0 | 11206 |
| Conditional floor18 | 177 | 43 | 64 | 2,096 | 12 | 0 | 11222 |

At completed code 11206 the edge has weight 600, source potential 200, and target potential 317, giving $600+200-317-483=0$. At conditional code 11222 the corresponding values are 376, 600, and 480, giving $376+600-480-496=0$. These optional pilot counts reuse the pinned prior result that the saved accepted rows equal the defined accepted set, and reconstruct the selected weight profile from the source graph plus its count-free floor.

`data/potential-literal-audit.json` stores the exact file hashes, ordered root references, profile statistics, expanded-array hashes, pilot witnesses, runtime, and checker hash. Input-file bytes were rechecked after the computation. The reproducing source is `scripts/audit_potential_literals.py`.

No parsing errors, value mismatches, or negative pilot slacks occurred. This is an independent numerical and source-literal audit; it does not certify the generated Lean modules, the whole-graph edge inequalities, or a global snake bound in Lean. Existing generated sources and receipts were unchanged.
