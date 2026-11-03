# Milestone 134: geometric steps in the endpoint count

The geometric steps behind the endpoint occurrence argument have passed Lean.
A canonical 012032 window whose relevant pair sum is at most nine has four
alternate vertices and one endpoint adjacent to a single unselected vertex.
One normalization is valid for every window assigned to the same endpoint.
Apart from path indices zero and two, the relevant vertices are coordinate
pairs among the eight coordinates different from the first path direction.

Consecutive pairs {a,b}, {a,c} force the intervening triple {a,b,c} and exclude
{b,c} from the entire snake. An actual represented sequence of such pairs has
distinct other coordinates and missing opposite pairs between consecutive
entries. The finite pair count and the corresponding simple-list length
bound have also passed Lean. All successful receipts and failed attempts are
saved, with exact source and dependency hashes.

The full occurrence theorem remains pending. Its proposed limits of twelve
windows per endpoint, eleven without a counted boundary window, and twenty-four
in total remain written bounds whose complete actual-snake Lean proof is
unfinished. Next: construct maximal intervals, check their overlap and boundary
conventions, sum missing degrees, and combine with the checked integer reduction.

No new global upper bound is claimed. The recorded interval remains 191–235,
with the documented incomplete independent rebuild of the contributor upper
proof. Optimality and 196 remain open. Paper revision 126 is unchanged; the
next full revision is due at 136. Ordinary notation is retained, with no new
named mathematical definitions in this round.

## Saved material

- MATHEMATICAL_NOTE.md explains the checked geometric results and remaining gap.
- lean/ contains the nine checked modules.
- data/ contains successful receipts, a checkpoint and the exact file manifest.
- logs/ retains every compiler attempt with its exact source and checker.
- scripts/ verifies sources, dependencies, logs, proof axioms and staged bytes.
- audit/ contains point-in-time observations of longer proof jobs.

The pair-capacity check passed in about 107 seconds but caused substantial
transient memory pressure. Reuse its verified receipt and object; do not repeat
that exhaustive check while other substantial proof jobs are running.
