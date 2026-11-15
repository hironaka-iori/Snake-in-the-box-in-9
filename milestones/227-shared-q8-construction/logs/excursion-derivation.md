# A single lower excursion and the reduced construction tasks

Status: written derivation and bounded inspection of immutable saved data. No compiler, solver, native search or software tests were run. No witness or new exclusion is claimed.

## Necessary decomposition of an actual second path

An actual path beginning and ending in the upper face and crossing coordinate 8 exactly twice consists of an upper prefix, one nonempty contiguous lower excursion, and an upper suffix. Before the first crossing the face cannot change; between the crossings it is lower; after the second it remains upper. The three pieces inherit injectivity and inducedness by restriction of the actual path.

Write the upper pieces as (A,B), in path order, and the lower excursion as (L). Let (s) be the lower projection of the last vertex of (A), and (t) the lower projection of the first vertex of (B). The following are necessary:

- Every vertex of (A) is distinct and nonadjacent to every vertex of (B). Their indices in the complete path are nonconsecutive.
- The lower projections of (A) and (L) coincide only at the prescribed terminal/initial pair (s). The projections of (L) and (B) coincide only at the prescribed terminal/initial pair (t). Any other coincidence would be an unintended vertical edge.
- The ports (s,t) are distinct and nonadjacent in (Q_8). Equal ports repeat an upper vertex; adjacent ports give a chord between the two selected upper port vertices. Therefore the lower excursion has at least two edges and three vertices.

The last restriction is stronger than a vertex-count condition, but it adds no new reduction to the 18 saved configurations: their first port is always 35 and their second port is 201, 208 or 212, all nonadjacent to 35. The general upper-arm enumeration already enforces the relevant separation.

## A stronger residual condition than whole cube capacity

Fix a partial common first lower path (F_0). For a fixed upper configuration, remove the closed (Q_8)-neighbourhood of every vertex of (F_0) from its lower excursion domain. The entire excursion must lie in a single connected component of this lower graph, containing both (s) and (t). If its required edge length is (ell), this component needs at least (ell+1) vertices and the corresponding alternating colour counts.

This condition uses the exact two-crossing structure. Whole-(Q_9) component capacity can combine several lower components connected through upper vertices, although one lower excursion cannot visit several such components. Thus a successful whole-cube capacity check does not discharge this necessary condition. No measured pruning improvement is claimed for a saved prefix.

The accepted `Residual226.path_in_closed_set` supplies the path-containment argument once the actual lower subpath and the component closure are supplied. `ResidualCapacity226` supplies total and colour capacity. Extending (F_0) only deletes further lower vertices, so failure of this necessary condition persists. A common first prefix may be discarded only when every applicable upper configuration, or every justified representative task, fails.

## Precise sufficient gluing criterion

For one saved configuration, take its fixed upper lists (A,B), ports (s,t), and required lower edge length (ell). Suppose the search produces:

1. An actual induced (Q_8) path (F) of 43 edges from 18 to 224 in the configuration's `first_domain`.
2. An actual induced (Q_8) path (L) of (ell) edges from (s) to (t) in its `lower_domain`.
3. Every vertex of (F) is distinct and nonadjacent to every vertex of (L).

The fixed-template premises needed to lift these paths are:

- (A,B) are induced upper paths with the prescribed second anchors, and are mutually disjoint and nonadjacent.
- Their projections meet (L) only at the two intended port pairs. The saved lower domain excludes all upper projections except (s,t); injectivity and the fixed lower endpoints then enforce these exact intersections.
- (F) avoids every projection of (A\cup B). This is enforced by `first_domain = first_lower_domain - upper_projections`.
- The upper vertex 480 is distinct and nonadjacent to (A\cup B), and its projection 224 is absent from (L). The preparation deletes 480 and its closed neighbourhood from the second domain.
- The domain masks enforce the prescribed separation from retained outside vertices, with each replacement's own anchors treated correctly. The retained outside part is the original induced path.

Under these premises, (A,L,B) is an actual induced second replacement. Within each piece, use its inducedness. Between (A,B), use their separation. Between opposite faces, adjacency is exactly equality of lower projections, so the two port equalities give precisely the two intended connecting edges. This is the exact three-piece criterion of accepted `Dimensional188.twoCrossings`. Its Boolean layer convention is false/true/false; the physical upper/lower/upper convention is obtained by exchanging the two face labels, which preserves cube adjacency.

Likewise, (F) followed by 480 is induced: its only vertical edge to 480 is from its final vertex 224. The same-face interactions between the two replacements are precisely the (F,L) separation and the already checked upper separation from 480. Opposite-face interactions are precisely the projection exclusions above. The accepted `Simultaneous225.replaceTwoBlocks` then supplies the general actual-path assembly from the local path and retained-boundary conditions.

The numerical lengths are exact: (F) plus 480 has 44 edges. The second replacement has

\[
(|A|-1)+\ell+(|B|-1)+2=44
\]

edges, equivalently (|A|+(\ell+1)+|B|=45) vertices. Both replacements preserve the original 191-edge path length. Appending 24 gives a 192-edge, 193-vertex candidate if the retained and new vertices have the required endpoint separation. The prepared domain masks exclude 24 and its neighbours from new interiors, and the final full-witness check must verify this assembly directly. The crossing count is one in the first replacement, two in the second, and one in the retained part, totaling four.

Conversely, an actual candidate with this fixed upper configuration and crossing allocation restricts to paths (F,L) satisfying these conditions, provided the preparation's domain exclusions and peeling are necessary-preserving. The latter is a native preparation obligation; it is not inferred merely from the existence of a domain list.

## Exact transfer between the saved upper configurations

The reduced task is determined by the literal first domain, literal lower domain, lower endpoints, and lower length, together with the common first endpoints/length and pairwise separation relation. Changing the upper arms while keeping this entire tuple identical leaves exactly the same set of lower solution pairs. Each such pair lifts through every fixed template whose premises above have been verified. Equal domain cardinalities would not be sufficient for this conclusion.

A bounded comparison of the saved arrays gives six literal groups:

- Configurations 0, 2, 4, 6, 8, 10, 12: first domain 107 vertices; second domain 106; (35\to201), 33 lower edges.
- Configurations 1, 3, 5, 7, 9, 11, 13: first domain 107; second domain 106; (35\to208), 32 lower edges.
- Configuration 14: first domain 107; second domain 106; (35\to212), 39 lower edges.
- Configuration 15: first domain 106; second domain 105; (35\to208), 38 lower edges.
- Configuration 16: first domain 105; second domain 104; (35\to201), 35 lower edges.
- Configuration 17: first domain 106; second domain 105; (35\to201), 33 lower edges.

Configuration 17 has exactly configuration 0's domains with vertex 212 removed from each. Hence every solution pair of 17 is a solution pair of 0. It is sufficient to retain five representative tasks when searching for any construction, and an exclusion of task 0 would also exclude 17. A solution of 0 need not satisfy 17, so these two configurations are not equivalent.

No new Lean module was added: the needed general induced-path gluing and component/capacity results already exist in accepted modules. The remaining work is their finite instantiation, the native upper-enumeration coverage proof, and the actual full-witness verification. Adding another generic constructor would duplicate the existing theory without resolving those obligations.

## Input pins

- `data/shared-q8-plan.json`: `38b68481c0db19dee53410ac64ba25601e7d44bc35110e267e1b81f781c45eda`.
- `data/companions.json`: `301a7bc1fd4aac979d86729d9ecde695be39a808b9dbb6617a3e33390eade8dd`.
- `scripts/prepare_companions.py`: `2e556e4d76563ae01af397f96f53daa66bd810e1197070cec887cb2912618ff0`.
- `TwoCrossings188.lean`: `764efb0102a2ce2d22ef0dd7e7a923958232bb5836c203e696361f42b536ef3a`.
- `Simultaneous225.lean`: `ce2129459ff1cc31f2cce81c599a0c7c25bc31fb07dac3c5aded95ccadf71882`; its saved audit reports PASS.
- `Residual226.lean`: `2e3378ae7c7c57d4214fdeff618208fca93a1c455bfde848310edde500263e45`.

## Appendix: first-zero deduction for the further contexts

Suppose both first-replacement anchors are lower, each replacement has 44 edges, and the available crossing budget for the two replacements is one or two. Write (f,s) for their coordinate-8 crossing counts. The accepted endpoint-parity theorem gives (f=2k) for some nonnegative integer (k).

- If (f+s=1), nonnegativity immediately gives (f=0,s=1). The prescribed opposite-face second anchors agree with this odd second crossing count.
- If (f+s=2), suppose the second anchors are upper and its allowed domain contains fewer than 45 upper vertices. A zero-crossing second path would stay in that upper face and use 45 distinct vertices, contradicting the accepted zero-face capacity theorem. Thus (s>0). Since the second endpoints agree in face, (s) is even, and (f+s=2) forces (f=0,s=2).

The zero-change theorem then puts the entire first replacement in (Q_8)'s lower face. In this further family the first path has 44 lower edges and 45 lower vertices. This differs from the earlier seven contexts, where the first path had 43 lower edges followed by the fixed crossing to 480.

With one second crossing, the second replacement has a single upper arm and a single lower piece, in the order prescribed by its anchors. Enumerating that upper arm leaves a lower path with fixed endpoint, port and remaining length. Accepted `LayerJoining.join` supplies the corresponding two-piece gluing criterion. With two second crossings and upper anchors, the preceding upper-prefix/lower-excursion/upper-suffix criterion applies unchanged. Singleton upper arms remain permitted.

In both cases the lower pair must be internally induced, fit the exact reduced domains, and be mutually disjoint and nonadjacent. Projection exclusions account for all opposite-face interactions with the fixed upper arms; retained-boundary conditions remain required. Exact duplication of reduced tasks must now compare both paths' endpoint pairs, both lengths, both literal domains and the same separation relation. The first endpoints/length cannot be omitted from that comparison by relying on the previous common (18\to224), 43-edge instance.

These deductions do not assert that the numerical premises hold for an uninspected context. Each prepared context must establish its crossing budget, endpoint faces, domain inclusion and, in the budget-two case, upper-face count below 45. Enumeration completeness, native lower-pair infeasibility and full witness assembly retain their respective separate verification requirements.

The following accepted receipts were inspected, and each current source, object and compiler log matched the hashes recorded in its receipt:

- `188-dimensional-constructions/data/TwoCrossings188-audit.json`: PASS; receipt SHA256 `59f92b55528ff4adda3a9351cd0df4ef843afca8ca58a646332fb85cab83305e`. The `twoCrossings` report lists only `propext`, `Classical.choice`, `Quot.sound`.
- `225-replacement-widths/data/EndpointParity225-audit.json`: PASS; receipt SHA256 `5e484f6c4edef5faabcf23809f621c47da0d3e6367e21bec3fb302368bd13ea3`. Both reports list only `propext`, `Quot.sound`.
- `226-connected-replacement-search/data/ZeroFace226-audit.json`: PASS; receipt SHA256 `35331cfbafb03e96839b7825233d6a02dcec35a76c9820ad5fd5b7848f7a43be`. Its three reports use subsets of `propext`, `Quot.sound`.

This appendix adds a written composition of existing checked results; no new Lean source, compiler invocation, solver query or search was required.
