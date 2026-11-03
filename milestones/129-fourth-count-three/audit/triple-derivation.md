# Independent interpretation of the three-count target

The selected native cores reported by the parent use the endpoint counter,
the fourth-count lower and upper counters, and the remaining-three counter.
The actual-snake interface can therefore be stated without the six-count cap
or the pair inequality. This note records the checked interface only; the
selected clauses and their contradiction require separate evidence.

For an actual snake with a fitting canonical window \(0120324\), the new
module provides:

- A coordinate permutation and translation that place the window at
  \(0,1,3,7,6,14,10,26\).
- The local window axioms with intervals
  \([(0,21),(0,21),(0,21),(3,3),(0,21),(0,21)]\), assuming only that
  \(\alpha_{r+4}=3\).
- The counter semantic condition for the 63 opposite-corner occurrences at
  positions \(3,5,6\), assuming
  \[
  \alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}\leq11.
  \]

The last assumption is the negation of the prospective integer lower bound
12. It is explicitly a hypothesis, and the helper does not establish that
lower bound. The three normalized centres and their incident directions
are \((7,2,0),(14,3,2),(10,2,4)\). Exact count transport identifies their
absent-corner counts with the actual snake counts. The existing
permutation-preserving count theorem allows sorted counter inputs while
retaining all repeated occurrences.

The counter's remaining premises describe finite encoding data: negative
primary inputs, a permutation of the specified three corner lists, and
stored upper bound 11. A concrete selected-core certificate must check those
premises, the ordinary counters, and every clause tag. Combining that
certificate with a checked refutation could prove the lower bound 12 under
\(\alpha_{r+4}=3\); this module alone does not do so.

`ActualTriple129.lean` imports neither `ActualSplit129` nor
`ActualCounters129` nor the round-121 or round-128 pair result. Its proof
uses no six-count-cap hypothesis and no pair inequality. The previously
checked modules remain unchanged.

The first launched check passed in 18.015 seconds. The three public reports
are `actual_normalized_frame`, `actual_window_axioms`, and
`actual_three_counter_good`. Each uses only `propext`, `Classical.choice`,
and `Quot.sound`. The fresh launch gate had 3.71 GiB free and two other Lean
processes; source, checker, and dependency hashes remained unchanged.

| File or evidence | SHA-256 |
|---|---|
| `lean/ActualTriple129.lean` | `320a55e8bd99aff15161ba8979b934e6433073aeeb01aacb46509e77c341eb66` |
| `audit/check_actual_triple.py` | `79c0ad4cf3d510f80ae1e2dc34a81f1a49a072955da4070e1d0fcecc2ec9a6de` |
| `build-independent/ActualTriple129.olean` | `4d49792820475da60e32c7e96324bc2829cc1908ba70701c1b228f04d5efe63f` |
| `logs/actual-triple-1793690025854366600/compiler.log` | `9e25547f73b10c94cc307120277d6f7ffc00884064220dbd045bde58455e7bf9` |
| `logs/actual-triple-1793690025854366600/record.json` | `ede86dcdd8e20558ca62b90d1910bec20d2d06de5bd8bd1fe2a4ca525b0c81a2` |
