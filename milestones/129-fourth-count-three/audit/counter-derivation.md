# Actual window and counter interfaces

`ActualCounters129.lean` extends the checked split with the interfaces needed
to interpret a tagged clause set. It introduces no new mathematical
definition and leaves the checked split module unchanged.

The normalized window vertices are
\[
0,1,3,7,6,14,10,26.
\]
The six internal centres have incident direction pairs
\((0,1),(1,2),(2,0),(0,3),(3,2),(2,4)\), respectively. A private helper
applies the existing exact count transport to each centre. Thus the absent
opposite-corner counts equal the corresponding actual snake counts.

The three public results are:

- `actual_window_axioms` supplies both the original interval axioms and the
  equality-branch interval axioms for the same normalized snake. The
  separate lists are necessary because the original and strengthened lower
  counters have different thresholds.
- `actual_total_counter_good` proves the existing counter semantic condition
  for negative literals whose ordered vertex list is a permutation of all
  six corner lists. The 126 occurrences count with multiplicity. This
  theorem assumes the six-count cap 22, which is the exclusion target.
- `actual_three_counter_good` proves that condition for negative literals
  whose vertex list is a permutation of the corner lists at positions
  \(3,5,6\). Their normalized centres and direction pairs are
  \((7,2,0),(14,3,2),(10,2,4)\). The bound 11 follows from the checked
  equality-case consequences; it is not assumed separately.

Both counter results use the already checked permutation-preserving count
identity. They therefore permit the saved sorted negative inputs and retain
all repetitions. The remaining premises concern finite encoding data: the
inputs are negative primary literals, their vertex list has the specified
permutation, and the stored upper bound equals 22 or 11. A concrete clause
certificate must discharge those metadata checks.

All three reports passed in 46.625 seconds and depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The successful launch had 5.39 GiB of
free physical memory and two other Lean processes. Source, checker, and
dependency pins remained unchanged. The actual split source, checker,
object, and successful receipt were additionally checked as dependencies.

| File or evidence | SHA-256 |
|---|---|
| `lean/ActualCounters129.lean` | `fcd0d411c8b18d32debdff24af7bc5288648b741e4548420575169c67d48b731` |
| `audit/check_actual_counters.py` | `4451ce2d6795c3509cd3b25a243d27880e9a57202c7505ed8aca99e7a55faeae` |
| `build-independent/ActualCounters129.olean` | `e3b33adf816320df652ba8b2007d1cf95e953e91d118124af57be28af6f58dcb` |
| `logs/actual-counters-1793689681725674800/compiler.log` | `2ffac493deb8bec129db01b76ec2b1e827737dae8eb984523a9b51d011ac3f29` |
| `logs/actual-counters-1793689681725674800/record.json` | `f81b4e6c9a7933843cea8f5dfac95be204fea08094d37fb3f0b9c57af7088427` |

This module does not check a selected UNSAT core or its tags, does not replay
a contradiction, and does not exclude either branch by itself. Its purpose
is to supply actual-snake meanings for the original and new counters when
the concrete clause certificate is assembled.
