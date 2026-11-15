# Checked potential certificate for cycle inequalities

`CyclePotential219.lean` passed Lean4.19.0 on the first attempt, with four accepted dependency reports. It imports only Std, introduces no definitions, and uses signed integer arithmetic and finite list sums.

## Checked statements

`path_potential_bound` proves by induction that

\[
p_{i+1}-p_i\le w_i\quad(0\le i<n)
\quad\Longrightarrow\quad
p_n-p_0\le\sum_{i=0}^{n-1}w_i.
\]

Each induction step adds the final potential difference and edge weight. The endpoint terms cancel. Weight nonnegativity is unnecessary for this implication.

`closing_edge_bound` adds a closing-edge weight \(w_*\). The checked premise

\[
p_n-p_0+w_*\ge2D
\]

then implies \(\sum_{i=0}^{n-1}w_i+w_*\ge2D\). The premise mentions only the potential values at the two endpoints and their closing edge, not the unknown total cycle weight.

`cycle_cost_identity` proves the exact conversion for the edge costs used by the numerical certificate. For cyclically ordered vertex values \(X_0,\ldots,X_n\), assign costs

\[
w_i=2D-X_i-X_{i+1},\qquad w_*=2D-X_n-X_0.
\]

Direct list induction gives

\[
\sum_{i=0}^{n-1}w_i+w_*
=2D(n+1)-2\sum_{i=0}^{n}X_i.
\]

`cycle_occupancy_bound` combines these deductions to prove

\[
\sum_{i=0}^{n}X_i\le nD.
\]

All four statements are over integers. No whole-cycle inequality is assumed. No hypothesis that the cycle is impossible or that the selected point comes from an actual path occurs in this potential argument.

## Application to edge-deleted graph potentials

For a graph edge \(\{u,v\}\), remove that edge and supply a potential on the remaining graph. Verify the potential inequality on each oriented remaining edge and verify

\[
p(v)-p(u)+(2D-X_u-X_v)\ge2D.
\]

Any simple cycle containing the omitted edge consists of an \(u\)-to-\(v\) path in that edge-deleted graph and the omitted closing edge. Restricting the potential and vertex values to this path supplies the checked theorem's indexed hypotheses. Its vertex list contains each cycle vertex once, so the resulting bound is exactly the cycle inequality. Extra chords cause no difficulty because the argument follows the chosen cycle edges; it does not require an induced cycle.

For a rational point \(x\), choose a positive common scale \(D\) with \(X_v=Dx_v\) integral and scale the potentials consistently. Division by \(D>0\) gives \(\sum_{v\in C}x_v\le |C|-1\). If \(0\le X_v\le D\), the edge costs are nonnegative, as required by a shortest-path computation using nonnegative weights. The Lean telescoping argument itself does not depend on that algorithm or on weight nonnegativity.

If a certificate is supplied for every undirected graph edge, this reasoning covers every simple cycle by choosing any one of its edges. The numerical checker must verify both oriented step inequalities where the graph is undirected, the actual edge-deletion rule, all relevant endpoint inequalities, a common positive scale, and the association between vertex indices and saved values. The finite graph-to-indexed-path restriction described here remains a written assembly argument; this module does not enumerate cycles or load the saved arrays.

A rational point independently verified to satisfy the other relaxation constraints and these all-cycle certificates is a feasible point of that strengthened relaxation. A large objective at such a fractional point would demonstrate a limitation of that relaxation. It would not construct a snake. This module alone makes no assertion about the saved574 values, the337 potentials, their objective values, or their numerical verification status.

## Accepted evidence

- Source `lean/CyclePotential219.lean`: SHA-256 `663713a78b8ed88bd889d98e0077e81b526a8a622a36522561185c4d1a0d8a56`.
- Object `build/CyclePotential219.olean`: `bb32ad9b65f219ec2ab81038d4c38e109390fd6da26d7355d4019e3001b1413b`.
- Receipt `data/CyclePotential219-audit.json`: `654c5a67e831493f80562f811fc073e39a6779f7e90eb7973f38ffd5579a0091`.
- Log `logs/CyclePotential219-1794707988489114300/compiler.log`: `8668965d8fec23666861daac0b9fbccfa6b3142fc97ae5ac75215d9de5caeac0`.

Each theorem depends only on `propext` and `Quot.sound`. The run took3.116seconds, with one compiler, `-j1 -s8192`, a60-second limit,256MiB private-memory ceiling,768MiB free-memory reserve and1GiB startup gate. Startup free memory was1,147,748,352bytes; minimum sampled free memory was928,342,016bytes; maximum sampled compiler private memory was88,207,360bytes. No resource stop occurred. Sampled values are not exact unsampled maxima or minima.

There were no failed attempts or repairs. No solver, graph enumeration or software tests were run for this proof task. The parent was notified when the compiler became terminal, and no further compiler was launched.
