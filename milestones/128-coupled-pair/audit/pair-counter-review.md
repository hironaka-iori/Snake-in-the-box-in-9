# Independent review of the coupled pair counter

The input audit passes. The added counter contains exactly 2863 clauses and 1428 fresh variables, with the intended multiplicities and literal polarity. Its complete serialization was independently reconstructed. The first 1000 native positive-hint deductions also pass replay against this new input. The native search timed out and supplies no completed contradiction or new count floor.

The auditor imports neither the preparation script nor `TaggedEncoding`. It reads the saved data, enumerates the cube corners independently, constructs every new clause and register directly, checks the threshold interpretation, and replays the bounded proof prefix. No solver or Lean compiler was launched and no existing source, evidence or job was changed.

## Geometry and multiplicity

The normalized seven-transition word is 0120324, with vertices

\[
(0,1,3,7,6,14,10,26).
\]

The paired centres are its second and fourth internal vertices, 3 and 6. At each centre, the count uses the 21 opposite corners obtained by flipping two coordinates other than its two prescribed incident directions. An independent enumeration of all 512 cube vertices verifies the corner sets, and a separate axis-pair enumeration verifies their saved order.

The ordered list at centre 3 is

\[
\begin{split}
(&10,18,34,66,130,258,27,43,75,139,267,\
 &51,83,147,275,99,163,291,195,323,387).
\end{split}
\]

The ordered list at centre 6 is

\[
\begin{split}
(&0,20,36,68,132,260,18,34,66,130,258,\
 &54,86,150,278,102,166,294,198,326,390).
\end{split}
\]

Their concatenation has 42 occurrences and 37 distinct vertices. Vertices 18, 34, 66, 130 and 258 each occur twice; the other 32 occur once. Every occurrence is preserved in the counter. Deduplicating the list would change the count being constrained.

Selected-vertex variable \(X_v\) has identifier \(v+1\). The counter input literals are positive, so the counter limits selected corner occurrences. The number of selected and absent occurrences sums to 42, including repetitions. Therefore the actual pair inequality

\[
\alpha_{r+2}+\alpha_{r+4}\ge8
\]

corresponds to at most 34 selected occurrences. The existing checked pair theorem applies to the six-transition prefix 012032. Identifying those actual counts with these normalized corner lists and incorporating this counter into the complete input still require the concrete semantic bridge for this new encoding.

## Exact input and variable checks

The first 101666 clauses equal the milestone-127 reduced input, with identical variable numbers, clause order and literal order. The auditor also verifies its relation to the saved original formula: retain all clauses except the recorded 4917 removed clauses, then append the saved 235 direct clauses. This relation check uses the recorded removal set; it does not repeat the earlier independent audit of all removed counter families or the direct-clause derivations.

Appending the independently reconstructed pair counter gives 104529 clauses and 8705 declared variables. The full bytes agree with `work/pair.cnf`. The 1428 new variables are exactly identifiers 7278 through 8705. They are disjoint from every base variable, and each new clause refers only to a selected-vertex variable or one of these new registers. There are 6248 occurring variables in the resulting input, comprising 4820 base variables and all 1428 new variables. The previously removed 2457 register variables remain unused.

For occurrence index \(i\) from 0 through 41 and threshold index \(j\) from 0 through 33, the register identifier is

\[
7278+34i+j.
\]

Every saved register meaning and clause tag agrees with this independent allocation. The family counts are:

| Clause family | Count |
| --- | ---: |
| A selected occurrence forces the first threshold | 42 |
| Initial thresholds above one are false | 33 |
| A previous threshold remains true | 1394 |
| A selected occurrence advances a previous threshold | 1353 |
| A selected occurrence is forbidden after threshold 34 | 41 |
| Total | 2863 |

The total also follows from \(34+41(2\cdot34+1)=2863\). The register count is \(42\cdot34=1428\).

## Counter semantics

Interpret each register at \((i,j)\) as “at least \(j+1\) of occurrences 0 through \(i\) are selected.” Repeated occurrences count separately even though their selected-vertex literals have the same truth value.

If the selected-occurrence sum is at most 34, assign every register its indicated threshold value. The initialization clauses hold. The monotonicity clauses preserve thresholds, the step clauses advance them when the next occurrence is selected, and the overflow clauses hold because a thirty-fifth selected occurrence is impossible. The auditor checks every emitted clause under all feasible local combinations of previous prefix count and next input bit. This gives 1742 local assignments and 120128 clause evaluations, with no failure.

Conversely, suppose all counter clauses hold. Induction on the occurrence index shows that whenever a prefix contains at least \(j+1\) selected occurrences, its corresponding register is true. Threshold one follows from the selected-occurrence and monotonicity clauses. Higher thresholds follow from monotonicity when already attained, or from the step clause when the next selected occurrence attains them. If a thirty-fifth selected occurrence existed, the preceding prefix would force threshold 34 to be true, contradicting the overflow clause at that occurrence. Thus the counter implies a selected-occurrence sum of at most 34.

This proves the intended counter interpretation after existentially quantifying its fresh registers. The finite audit verifies every concrete clause and threshold-extension case. The general induction is the mathematical argument above; this review does not claim a new Lean semantic theorem.

## Native result and bounded proof replay

The saved search ended with status `TIMEOUT`, exit code 1, after 180.062 seconds. Its recorded CPU time is 6.25 kernel seconds plus 18.34375 user seconds, totaling 24.59375 seconds. Both output logs are empty. The raw partial proof has 176984064 bytes, and its full hash agrees with the terminal search record.

After the terminal record was available, the auditor checked the first 1000 deductions against the new 104529-clause input. It processed 9141 deleted clause identifiers and required every referenced clause to remain available. All 2643 positive references passed ordered unit propagation. The last checked deduction has identifier 105529. No empty clause occurs in the checked prefix.

The consumed prefix has SHA256 `e26ae8982b58dd32d983f522de1fa55550b5638f6b38ef66d3a8cfa7794e52e5`. This is a bounded prefix check, not a replay of the full partial file. Hashing the entire file establishes identity only. The first audit invocation stopped at the active-run guard before reading the changing trace or writing its evidence file; the successful invocation used the completed timeout record.

The new pair clauses are trusted inputs for this bounded replay. They were not proved to be RUP consequences of the old milestone-125 or milestone-127 formula. Consequently this prefix audit is not an original-input-only proof transport. The new constraint is justified for actual snakes by the proved geometric pair inequality, together with the concrete interpretation still to be completed for this input.

## Remaining proof requirements

A new actual-snake count floor would require a complete contradiction of this input, verification of its full proof, and the semantic interpretation of every input family for an actual snake with the prescribed window and six-count cap. The pair inequality is already checked, but it must be connected to the new 42-occurrence counter and its fresh registers. The inherited reduced-input and direct-clause justification must also remain accounted for.

A satisfying assignment of the local input would need separate checks before it could be described as a complete induced snake. A timeout gives neither a counterexample nor an exclusion. No improvement to the maintained global bound follows from this round's audited evidence.

## Pins and reproduction

The audit script prints a read-only summary. With `--sample 1000`, it requires a terminal search record and verifies the bounded native prefix. With `--output`, it creates a new evidence file exclusively. It verifies all recorded preparation and proposal source pins, then rehashes every pinned input after the audit to detect concurrent changes.

| Artifact | SHA256 |
| --- | --- |
| Independent auditor `audit/audit_pair.py` | `a84afe7cd5e1ff4b6c01cd427dfc373f37023c6ba273766e3ba08ff41e3a817a` |
| Saved audit `data/pair-review.json` | `ea5c8516931d96496a1d62b4817975962efdd73ca7dd8de0390094f6a58d1a7f` |
| New complete input `work/pair.cnf` | `a00f07497e7e1f4bf3e9bd31d74c1ef39999ebdc0d1019aecc860493ac05d2fc` |
| Base reduced input | `5e7e726dc2ebcc327eb1549d5cfec1ec3fe183ee5750f283d3db0af70d51389f` |
| Counter detail `data/pair-counter.json` | `5b3c79947be287b9277126e94ed2eed764dc8d43c488ecc1477ee0848afd0316` |
| Preparation record `data/preparation.json` | `5d73915a1cecf80453f2c382934e06ae9ff281b098d32738f9ce9bc2f454701a` |
| Terminal search record `data/search.json` | `d42dde1f72a14f0907d62e11ad45471907e7eab62d51a3c8e4f505fa928ca2f6` |
| Raw partial proof | `e6af53d1f85f0afc3717c00d34a9481dfdebc59a88498f6e4fae95e9cc762431` |

The successful audit completed at 2026-11-03 06:36:51 UTC. No substantive defect was found in the concrete pair counter or the checked proof prefix.
