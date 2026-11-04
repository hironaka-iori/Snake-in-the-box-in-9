# Round 168: undominated cube geometry and six empty squares

New result: written proof that d(q)=0 implies e(q)>=6 for every nontrivial induced path in Q9. It implies L<=71 forces domination. Full Lean verification is pending; no numerical upper-bound improvement is claimed.

- review/six-empty-squares.md: complete mathematical argument.
- review/six-empty-squares-review.md: independent challenge and review.
- data/five-pair-classification.json: exhaustive 443704 coordinate graphs.
- data/eight-cycle-check.json: all 16 triple selections.
- lean/CubeUndominated168.lean: actual path/pair/triple bridge draft.
- lean/EightCycle168.lean: finite endpoint inequality draft.
- data/local-execution.json: pinned sources and serialized module order.
- scripts/check_local.py: guarded checker, 1 GiB startup, 768 MiB reserve, 256 MiB compiler-private limit and 60 seconds.

Initial Snake9 passed under the old plan; receipt and object in review/superseded-plan are historical and not current accepted artifacts. PathStructure hit MEMORY_LIMIT; its revised algebraic irreflexivity proof awaits checking. Current modules must be rebuilt under the current plan. No sorry/admit/native_decide or new axioms are intended. The inherited manuscript and previous evidence remain unchanged except for the documented new proof and current handover.
