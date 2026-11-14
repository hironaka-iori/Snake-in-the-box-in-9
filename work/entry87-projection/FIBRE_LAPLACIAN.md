# Reconstructing snakes from a coordinate projection

**Finite rigidity theorem.** Choose any of the 131 stored 191-edge snakes and erase any one of its nine coordinates. Keep the unordered list of addresses, including multiplicities. The list determines the full labelled snake up to exchanging the two faces and reversing its traversal. This was checked for all 1,179 source and coordinate choices. The order, endpoints and face assignments are recovered from the list.

## The cut equation

Write the cube as two copies of a base cube. Let W contain every occupied base address and let R contain addresses used in both faces. For a path with at least three vertices, the two copies at each r in R are adjacent and hence consecutive. Contract the edges between these pairs. The result is a simple path through W, so its bipartition counts and its endpoint colours must agree with those of an alternating path.

Two doubled addresses cannot be adjacent because they would induce a square. A doubled address r has one or two neighbours in W. Its two copies already use one edge each for their common vertical edge. One base neighbour makes one copy an endpoint. With two neighbours, one lies in each face.

Form the induced graph G on the singly occupied addresses W minus R. For a singleton x, let c(x) be its face bit and define z(x) to be c(x) plus the parity of x, modulo two. For neighbouring singletons x and y, the lift contains their horizontal edge exactly when z(x) and z(y) differ. Write m(x) for the number of doubled addresses adjacent to x. They contribute exactly m(x) further edges to its degree. Writing e(x)=1 for a singleton endpoint and e(x)=0 otherwise, the cut-degree condition gives

    L_G z = m + e   over the field of two elements.

Here L_G is the graph Laplacian reduced modulo two. Each doubled address with two neighbours u,v adds the equation z(u)+z(v)=1, because u and v have the same base parity and must occupy opposite faces. Fix z=0 at the first singleton to account for the global face exchange. A valid path of at least three vertices has a singleton.

Every lift satisfies these equations. Conversely, generate the allowed endpoint choices using the projected path parity, and solve the linear equations for each. Keep the assignments giving actual degree one or two at every vertex and a connected lifted graph. The linear equations fix degree parity at each singleton, and the equations at doubled addresses fix their incident degrees. With the prescribed two endpoints, a connected surviving graph is exactly one induced path. Traversal recovers its order. The connectivity test removes possible extra cycle components.

One elimination with symbolic endpoint indicators handles all endpoint choices. Consistency conditions become binary signatures. When both endpoints are unknown, one signature lookup finds the compatible partners for each singleton. Enumerating the kernel of the reduced matrix then gives every candidate phase for that choice of endpoints.

## Verification

The independent small-cube control grew every induced path with at least three vertices in the four-dimensional cube. It found 2,400 distinct vertex sets. The resulting counts agreed with the algebraic method for all 6,516 admissible assignments of multiplicities 0, 1 and 2 on the eight base addresses. [Control result](fibre-laplacian-control.json).

On the 1,179 nine-cube projections, the pinned kernel dimension was zero in 1,012 cases, one in 136, two in 24 and three in seven. In total, 253,438 compatible endpoint choices produced 411,703 phase assignments. Each projection yielded exactly one solution after the face normalization. Its full transition sequence agreed with its source up to coordinate relabelling and reversal. Since the source is itself a lift of the labelled multiset, uniqueness gives the stated labelled result. [Decision procedure](fibre_laplacian.py), [bank driver](fibre_phase_bank.py), [all results](fibre-phase-bank.json).

Run `python fibre_laplacian.py --control` and `python fibre_phase_bank.py` from this directory. The next constructive application changes occupied addresses before solving for both faces and the order. This permits the whole path to rearrange after a small change in its projection.

## Keeping just the set of addresses

Now forget which addresses occurred twice as well. There are 1,043 distinct labelled address sets among the 1,179 projections. At length 191 edges the exact multiplicities of full labelled paths, up to reversal and face exchange, are as follows.

| Number of lifts | Number of address sets |
|---:|---:|
| 1 | 916 |
| 2 | 95 |
| 3 | 1 |
| 4 | 30 |
| 6 | 1 |

In 475 sets the number of possible doubled sites already equals the number required. For each of the other 568 sets, an exact degree-and-connectivity solver searches for further doubled sets, blocking each complete choice after enumeration. The Laplacian method independently enumerates every lift of each feasible choice. This recovered 56 additional labelled placements beyond those originally registered against those exact sets. Every placement is cube-isometric to a member of the original bank, allowing reversal. For example, the address set obtained from source 2 by erasing coordinate 3 also admits a placement equivalent to source 20. Thus the finite bank is closed under this operation at 191 edges even though unweighted projections can have multiple lifts. [Enumeration and all-pairs checks](unweighted_fibres.py), [0–260](unweighted-fibres-0-261-150000.json), [261–521](unweighted-fibres-261-522-150000.json), [522–782](unweighted-fibres-522-783-150000.json), [783–1042](unweighted-fibres-783-1043-150000.json).

The 568 final exclusions have independent resolution cores, verified in 12,471,987 resolution steps. The 97 geometric cycle clauses used by these final proofs are checked directly from their cube vertices. The replay program regenerates each complete formula and checks its hash against the receipt. [Proof cores](unweighted-proof-cores.zip), [reconstruction and replay](unweighted_replay.py).
