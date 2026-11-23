# Opposite endpoint colours in the three-crossing Q9 catalogue

All 1,496 lower configurations have an integer certificate with total Q9 vertex bound strictly below 194 when the two global endpoints have opposite colours. Thus an odd-length path in this family has at most 191 edges. Both 193 and 195 edges are excluded. The result is confined to one intact catalogue donor and one isolated additional lower vertex, with exactly the indicated three crossings.

A frozen donor word specifies a Q8 path starting at zero. For that donor P, enumerate all lower vertices x distinct and nonadjacent to every vertex of P. The lower set is P together with x. Both endpoints of P and x are mandatory crossings. These three upper vertices are mandatory, and no column above an interior point of P may be selected. The lower endpoint of the full snake is x. If its Q9 parity is m then the unique upper endpoint must have Q9 parity 1−m. On the upper facet, Q9 parity is reversed relative to the Q8 inner coordinate. Since opposite-colour paths have equally many vertices of both colours, the signed Q8 parity sum of the upper set equals that of the lower set. The two thresholds are 194 and 196 vertices.

For each allowed upper vertex there is a local table over its incident upper edges. A selected vertex must have total degree two or be the allowed endpoint of degree one, counting the crossing if applicable. For each chosen family of parallel Q3 faces, enumerate the induced forests within each face and their incident-edge signatures. An integer price indexed by vertex, face family and local signature contributes with opposite signs to the vertex and face tables. The prices cancel on every genuine path. The endpoint and parity prices also cancel against their known totals. Replacing the contribution of each table by its greatest possible value therefore gives an integer upper bound. The largest selected bound is 1,939,998 divided by 10,000. An opposite-colour path has an even number of vertices, hence at most 192 vertices.

The manifest lists one certificate per required pair. Some prices were rounded from a local LP or adapted from prior configurations; others were generated directly by transferring integer prices between local tables. All bounds in the manifest are evaluated using integer arithmetic. The two verifiers reconstruct the donor paths, constraints and Q3 forests. The independent positive construction found 165 edges with the required three crossings and opposite endpoint colours.

For the standalone archive, extract it and run

    python3 verify_bundle.py

To run both integer backends after extraction, compile and pass the native executable

    c++ -std=c++20 -O3 replay.cpp -o replay
    python3 verify_bundle.py --native ./replay

The local full run additionally records exploratory prices, intermediate output and the deterministic positive search. The archive contains the frozen catalogue, selected prices, manifest, positive coordinates, summary and replay sources.
