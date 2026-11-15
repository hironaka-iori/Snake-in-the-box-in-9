# Projection ports: proof scope

`ProjectionPorts229.lean` is source prepared for the parent's serialized compiler run. No compiler, solver, or tests were run while preparing it.

The existing `LayerJoining.Compatible` condition already identifies the exact pair of indices allowed to coincide across two faces. The new source supplies the missing connection from a filtered lower domain to that condition. It adds no path representation or constructor.

For a lower domain (D), own upper projections (U), actual joining ports (P), and other upper projections (O), the admissible lower vertices are

\[
D\setminus\bigl((U\setminus P)\cup O\bigr).
\]

`projection_mask_iff` proves that membership in this filter is equivalent to membership in (D), together with two geometric conditions: every adjacency to an own upper vertex has a projection in (P), and there is no adjacency to an upper vertex from (O). It holds for an arbitrary underlying adjacency relation because cross-face adjacency in the Cartesian product is equality of projections. Lists need not be duplicate-free. The theorem deliberately does not infer that every member of a supplied port list is a legitimate joining port.

`compatible_iff_projection_filter` gives that additional geometric interpretation for a single crossing. Let (p) and (q) be actual induced paths in the lower-dimensional graph, with (p)'s last vertex equal to (q)'s first vertex. Assume every vertex of (p) belongs to (D). The theorem proves that the exact indexed compatibility required by the existing joining constructor is equivalent to every vertex of (p) surviving the projection filter whose sole exemption is (p)'s last vertex.

For sufficiency, any common projected vertex must equal the exempted last vertex. Injectivity of (p) fixes its lower index, and injectivity of (q), together with the joining equality, fixes its upper index. For necessity, the existing exact indexed compatibility forces every projected coincidence to occur at those indices. Thus the theorem does not assume the desired compatibility conclusion. Applying `LayerJoining.join` to the compatibility obtained from a surviving-domain premise constructs an actual induced path with the sum of the two path lengths plus one edge. The reverse orientation follows by reversing the paths or exchanging the two face labels in the undirected cube.

`fixed_lower_anchor_excluded` addresses the correction directly. If the lower path has positive length and all its vertices survive the single-port filter, its first vertex cannot occur among the upper projections. Otherwise the filter makes its first and last vertices equal, contradicting the lower path's injectivity. The positive-length premise is essential: a zero-edge lower piece has its fixed anchor at the crossing port.

For a two-crossing excursion, the general filter theorem permits two actual ports. Their status still has to be established from the two intended joining equalities and the exact compatibility premises of the existing two-crossing constructor. For two simultaneous replacements, cross-block upper projections have no exemption; same-face disjointness and nonadjacency and retained-vertex restrictions remain separate requirements of the accepted simultaneous-replacement theorem.

The source proves no extraction of actual ports from the native template records, no preservation of domain preprocessing, no enumeration completeness, and no numerical snake bound. Those obligations remain separate. The intended compiler audit has three exported axiom reports. Source preparation uses only the already accepted `LayerJoining` dependency and `Std` through it.

## Compilation update and general crossing allocation

The parent subsequently reported that `ProjectionPorts229.lean` passed its guarded Lean compilation with all three exported axiom reports. Its accepted source remains unchanged. This status update does not extend the checked statements to the native template extraction.

The separate `CrossingAllocation229.lean` is newly prepared source; it has not been compiled. It imports only `Std` and has two intended axiom reports. For natural numbers (A\leq2) and (a), matching parity and the premise that (A=2) implies (a>0) give (A\leq a). The proof treats (A=0,1,2): nonnegativity suffices for zero; odd parity forces at least one; positive even parity forces at least two.

Applying this argument to two target counts (A,B\leq2) gives (a\geq A) and (b\geq B). If (a+b=A+B), both inequalities are equalities. This replaces repeated finite-table allocation arithmetic with a universal implication under explicit premises.

For the construction interpretation, (A) and (B) count upper anchors, while (a) and (b) count actual coordinate crossings. Endpoint parity supplies the congruences. When both anchors are upper, a separate upper-face capacity argument must exclude zero crossings. The total-crossing equality must also be established for the context. The new source neither extracts these facts from saved graphs nor automatically proves any literal context collection.

## Accepted compiler results

Both modules subsequently passed the guarded Lean compiler run. ProjectionPorts229 has three accepted reports, and CrossingAllocation229 has two. The historical source-preparation descriptions above precede these runs. Exact scopes and remaining graph-data obligations are unchanged.

- ProjectionPorts229: 3 reports; source SHA-256 e394b38fa880561845de63e83a602cb981d9ac5543d22148307894fa2c7c667e.
- CrossingAllocation229: 2 reports; source SHA-256 72fb63806cd05f817df52a4e5a94c694ab7b07feed2399378f34ef18ad833dd4.
