# Actual counterexamples and coupled window counts

For a window with directions $012304$, write its existing singleton counts as
$\alpha_{r+1},\ldots,\alpha_{r+5}$. No additional notation is needed.

A complete induced path with 148 edges has a window with counts
$(3,6,3,4,6)$. Thus a total lower bound 23 is false even under
$\alpha_{r+1},\alpha_{r+3},\alpha_{r+4}\le 4$ and
$\alpha_{r+2},\alpha_{r+5}\ge 6$. The normalized window starts at index 43
of the saved path, with vertices $(0,1,3,7,15,14,30)$. Lean checks all 149
vertices for distinctness and every pair for induced adjacency, followed by
its directions and singleton counts. The counterexample concerns the count
inequality; the path does not improve the known construction length 191.

A second length 148 path has counts $(4,6,4,3,6)$. A length 144 path realizes
$(4,6,2,4,6)$, exactly one of the former critical tuples. These latter two
paths have independent numerical all-pairs checks; only the first has a new
Lean witness in this milestone.

Two more restrictive full-cube searches produce negative certificates. Under
$\alpha_{r+2},\alpha_{r+5}\ge 6$, their candidate implications are

$$
\alpha_{r+1}=2,\quad\alpha_{r+3}=2,\quad\alpha_{r+4}=3
\quad\Longrightarrow\quad
\alpha_{r+2}+\alpha_{r+5}\ge 16,
$$

and

$$
\alpha_{r+1}=2,\quad\alpha_{r+3}=4,\quad\alpha_{r+4}=2
\quad\Longrightarrow\quad
\alpha_{r+2}+\alpha_{r+5}\ge 15.
$$

The three fixed counts sum to 7 and 8, respectively, so these are exactly the
total lower bound 23 used in the graph experiment. The counter retained all 105
literal occurrences; repeated corner literals were not removed. Both encoders
agree byte for byte on the full-cube formulas. Separate unit-propagation replay
checks the recorded contradictions. Concrete Lean semantics, full contradiction
replay and geometric transfer remain pending; the implications retain that status.

Canonical orientation matters because these count conditions are asymmetric.
Reversing a direction word reverses its five count entries before testing the
conditions. Both placements can be tested for exclusion; only the suffix
placement earns the stipulated excess credit. The new rules require two count
symbols 6, so they cannot delete an entire represented bucket through the sum
cap. Their deficits are charged using the existing shared budget and the maximum
applicable credit, avoiding duplicate charges.

With the two rules provisionally added,449 and 446 suffix keys receive positive
credit. The old edge-removal set is unchanged. New cycles attain the same means
$2915/6$ and 496, with potential ranges $1730/3$ and 602. All thirteen applicable
deficits vanish on these replacement cycles. Redistributing the permitted
coefficients within this fixed family cannot raise those cycle ceilings.
No new integer upper bound follows.

The earlier universal total candidates 20 through 22 also cannot suffice alone:
at total 22 their retained-cycle ceilings are $985/2$ and 512. Even at zero
potential range, their comparison margins are

$$111960\cdot 2-227\cdot 985=325>0,$$
$$116160-226\cdot 512=448>0.$$

The replacement conditional cycle uses shapes $012031$ and $012314$; the
completed cycle uses $012034$, $012301$, $012304$ and $012310$. There is no
shared five-centre shape. The next test therefore concerns the complete
nine-transition word $012031043$ and its six recorded counts simultaneously.
Its two interval symbols must remain $[6,21]$. Testing only their lower endpoints
would leave the other represented values unexamined.
