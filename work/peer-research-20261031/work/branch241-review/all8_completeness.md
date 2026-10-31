# Complete short-cycle cuts inside a window domain

Let Q_n have vertex set {0,1}^n and Hamming-distance-one adjacency. A selected snake is an induced path, so it cannot contain every vertex of any induced cycle. Consequently each induced cycle C gives a sound clause OR_{v in C} not selected(v). Such clauses are geometric consequences, not arbitrary SAT strengthening.

## Lemma 1: the unique four-dimensional face

An induced cycle of length eight uses exactly four coordinate directions, each twice. Indeed, every used coordinate is flipped a positive even number of times on a closed walk, so at most four directions occur. If at most three occurred, the eight distinct cycle vertices would fill a coordinate Q3 face. Every vertex then has three neighbors among those eight vertices, contradicting the degree-two induced-cycle condition. Thus exactly four occur, with two flips each.

The four varying coordinates and the fixed values of all other coordinates specify a unique Q4 face. Therefore enumerating all induced eight-cycles in every Q4 face lists every cycle exactly once.

## Lemma 2: finite template enumeration

There are C(16,8)=12,870 eight-vertex subsets of Q4. all8_cycles.templates checks every subset, rejecting those whose induced adjacency graph is not connected and 2-regular. The retained count is exactly 168. A finite connected 2-regular graph is a cycle; with eight vertices its length is eight. Thus the test is both necessary and sufficient, without a search-heuristic assumption.

The implementation separately validates every embedded retained cycle by enumerating all unordered vertex pairs, recomputing its induced adjacency, checking degree two and checking connectivity. It also checks that no vertex set appears twice.

## Corollary 3: all Q9 eight-cycles

Q9 has C(9,4)*2^5=4,032 coordinate Q4 faces. By the unique-face lemma, the total number of induced eight-cycles is

    4032*168 = 677376.

This count is exhaustive for induced eight-cycles, not for longer cycles. Removing all these cycles does not in itself prove that the remaining selected graph is connected or acyclic.

## Corollary 4: all eight-cycles inside one radius-four ball

Translate the centre to 0. Fix the four free coordinates of a Q4 face. Let k be the Hamming weight on its five fixed outer coordinates. A point of internal weight j lies in the ball exactly when j+k<=4.

For k=0 every Q4 template is retained, giving 168. For k=1 only the all-one internal vertex is forbidden. By vertex symmetry, every internal vertex lies in 168*8/16=84 templates. Thus exactly 168-84=84 templates avoid it.

For k=2 only internal weights 0,1,2 are allowed. An induced eight-cycle cannot contain 0: its two selected singleton neighbors would each require an additional selected neighbor of weight two; any selected weight-two vertex must have both its singleton neighbors selected. With just the two singleton neighbors selected at 0, a cycle through 0 therefore closes after four vertices. In an eight-cycle without 0, the bipartite graph alternates singleton vertices and weight-two vertices. Eight vertices require all four singleton vertices and four pair vertices. This is precisely an undirected Hamiltonian cycle on K4, with each edge subdivided by its corresponding pair vertex. There are (4-1)!/2=3 such cycles, and each embedding is induced.

For k>=3 only weights at most one remain, giving a star or an empty graph, hence no cycle.

There are C(5,k) outer fixed words of weight k. Multiplying by the 126 choices of free coordinates gives

    126*(168 + 5*84 + 10*3) = 77868.

all8_cycles.py independently obtains exactly this count by direct embedding and ball membership tests. It does not use the numerical formula to select which cycles are retained. The formula is checked afterwards.

## Artifacts and scope

all8_B4_manifest.json.gz contains every one of the 77,868 cycle vertex sets for the radius-four ball centred at vertex 1. The JSON summary records the exhaustiveness and verification counts. The generic enumerate_all8(allowed) function can instead use the union of balls of any fixed window or the full cube.

These clauses are valid additions to the project's window/global CNF. An ensuing UNSAT result still requires its own checked proof, and its mathematical application still requires the score/window aggregation bridge. This document does not claim a tighter numerical upper bound on a(9).
