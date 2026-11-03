# Final actual-snake statement review

The checked minimal wrapper preserves the original actual-snake exclusion
and its proof. No change in mathematical hypotheses, count positions or
conclusion was found. This review was read-only apart from this report; no
Lean process or solver was run.

## Reviewed evidence

- Source: `lean/ActualBase138Minimal.lean`, SHA256
  `d024e01bf668a7d67b71b9c4d015be9249a187534575af6ad901d7ace3edb078`.
- Successful check receipt: `data/ActualBase138Minimal-audit.json`, SHA256
  `8fae0221b041bc53d1ae18f6f43520af51e03ea4bd7ba6d2ca891d2007c8ff95`.
- Compiler log SHA256:
  `2188a5e7c5676c6292d1b29fc62701db498e74e652af24259610ac4e144702f6`.
- Importable object SHA256:
  `00bb5ca8b7ba900e2373cd236b8b0ca53e6383781e5ab42cd366bf08b3fa004d`.

The current source, log and importable object hashes agree with the successful
receipt. Every dependency hash in that receipt was also rechecked. The receipt
reports exit code 0 and a duration of 9.344 seconds.

## Normalization and theorem comparison

The minimal wrapper imports `DirectionWindowBridge` and `Mathlib.Tactic` and
includes the existing canonical-frame proof locally. A direct text comparison
confirmed that its entire canonical-frame theorem and proof match the theorem
in milestone 79's `CanonicalExclusions.lean`, after normalizing line endings.
Only its enclosing namespace is different.

The complete source beginning with `theorem refuted` and ending at the
namespace closure is identical to the corresponding tail of the original
`ActualBase138.lean`, again after normalizing line endings. Thus the replacement
does not weaken the count assumptions or omit any normalization step. It
changes the dependency needed to obtain the canonical frame.

The final theorem excludes a fitting canonical transition word `012301430`
in any actual nine-dimensional snake when the counts at offsets 3 through 8
are respectively at least 6, equal to 3, equal to 3, equal to 3, equal to 5
and equal to 2. The first two internal counts use only their ordinary upper
bound of 21. There is no additional parity, endpoint-location, normalized
coordinate or fixed-total-length hypothesis. The ordinary two-endpoint
property is supplied by the actual-snake bridge.

## Axiom reports

The preserved compiler log contains exactly four reports:

1. `Snake9.LocalWindow.CycleBase138.actual_canonical_frame`;
2. `Snake9.LocalWindow.CycleBase138.refuted`;
3. `Snake9.LocalWindow.CycleBase138.actual_refuted`;
4. `Snake9.LocalWindow.CycleBase138.actual_cycle_row`.

Each report lists only `propext`, `Classical.choice` and `Quot.sound`.
The final wrapper contains no external refutation hypothesis, additional
axiom, unfinished proof or native-decision shortcut.

## Limits of this result

The minimal wrapper completes the actual-snake interpretation of the checked
base-window certificate. The original wrapper's import failure remains
preserved and is not counted as a successful check. The abandoned bulk import
copy is not needed for the mathematical statement reviewed here.

The stronger short-window cap exclusion remains deferred. Eliminating this
row from a graph and obtaining a new cycle mean or global length bound require
separate deductions. The source `Credit138.lean` expresses conditional rational
arithmetic: its sufficient-target theorem assumes both the stated lower bound
on the mean and the strict bound on the remainder. It does not establish those
premises or a new unconditional global bound.
