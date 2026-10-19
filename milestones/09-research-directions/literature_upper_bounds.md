# Published upper bounds for snakes in Q9 (literature check, 19 October 2026)

Search-engine based survey; arXiv, OEIS and publisher sites were not reachable from the build machine, so items marked *[unverified]* still need a check against the primary text.

## Bottom line

- **Upper bounds:** no published upper bound for the longest **snake** (open induced path) in Q9 beats **256 edges**. That figure is Danzer–Klee's 2^(n-1).
  - The repository's kernel-checked **241** is new: `work/spectral/stronger/UpperBound241.lean:16` (`upper_bound_241`) and `:19` (`verified_interval_191_241`).
  - The targeted **238** would also be new: `work/spectral/stronger/UpperBound238.lean:13` (`upper_bound_238`), with `upper_bound_239` at `UpperBound239.lean:13`.
  - Neither improves on an earlier Q9 number. There is no earlier Q9 number below 256.
  - The repo's own earlier bounds also beat everything published that I found: 255 from Huang's theorem (`paper/snake9_research.tex:175-177`), 254 from square counting (`milestones/03-square-incidence/square_investigation.md:21`), and 245 to 251.
- **Lower bound:** the best known lower bound is **191 edges**, from Orland et al., arXiv:2607.15270 (v3, 30 Sept 2026). They found 131 classes. The previous record was 190, by Wynn (2012).
- **Units:** the repo measures length in edges. `work/final_lean/Snake9.lean:3` and `:18-21` define `Snake m` as a path with m+1 vertices, so it matches the edge convention of OEIS A099155 and Orland et al.

**Access caveat.** The egress proxy refused arXiv, OEIS, Wikipedia, ScienceDirect, Springer, combinatorialpress, uoguelph, ai.uga.edu and u-bordeaux; WebFetch failed with DNS errors on arxiv.org and oeis.org. I read only two sources directly, through raw.githubusercontent.com: the Math-AI-Caltech dataset README and DeepMind's formal-conjectures `SnakeInTheBox.lean`. Everything else comes from WebSearch result summaries. Formulas marked *[unverified]* could not be checked against a primary text.

## Published results

| Source | Object (snake/coil; units) | Statement | Value at n = 9 | Method |
|---|---|---|---|---|
| Danzer & Klee, *Lengths of snakes in boxes*, JCT 2 (1967) 258-265 | snake (open induced path), Theorem B as cited by formal-conjectures | s(n) <= 2^(n-1) for n >= 1 | **256** | combinatorial counting |
| Douglas (1969); Deimer, Combinatorica 5 (1985) 109-120 | coils ("circuit codes of spread 2"); Deimer's abstract is about circuits | upper bounds of the form 2^(n-1)(1 - f(n)) *[exact formulas unverified]* | not a snake bound | counting / spread arguments |
| Solov'eva, Metody Diskret. Analiz. 45 (1987) 71-76 (Russian) | cycles (coils) | upper bound on cycle length *[formula unverified]* | not a snake bound | counting |
| Snevily, *The snake-in-the-box problem: a new upper bound*, Discrete Math. 133 (1994) 307-314 | coils (older papers say "snake" for an induced cycle) | S(d) <= 2^(d-1)(1 - 1/(20d-41)) **for d >= 12** (the WVU source; the CRC entry says d <= 12, which looks wrong) | does not apply; formally 256·138/139 ≈ 254.2 | counting with square/neighbourhood structure |
| Zémor, *An upper bound on the size of the snake-in-the-box*, Combinatorica 17 (1997) 287-298 | "snake = simple cycle without chords", so coils | 2^(n-1)(1 - 1/(89√n) + O(1/n)). Formal-conjectures uses the explicit form 1 + 2^(n-1)·6n/(6n + √n/(6√6) - 7), which their issue #5714 flagged as misformalized in an earlier version | explicit form gives ≈ **293.9**, weaker than trivial | isoperimetric / Fourier-type counting |
| Emelyanov & Lukito, *On the maximal length of a snake in hypercubes of small dimension*, Discrete Math. 218 (2000) 51-59 | "snake" (cycle convention, as in their school) | abstract: the new bound beats all earlier bounds for **37 <= n <= 19079** | gives nothing better at n = 9 | counting |
| Lukito & van Zanten, *A new non-asymptotic upper bound for snake-in-the-box codes*, JCMCC 39 (2001) 147-156 | coils | square-face counting with >= 2 singleton squares per coil vertex (as summarized at `paper/snake9_research.tex:182`) *[closed form unverified]* | see note below | square counting |
| Abbott & Katchalski, JCT B 45 (1988) 13-24; Utilitas Math. 40 (1991) | lower bounds | s(d) > λ·2^d; coils >= (77/256)·2^d for d >= 21 | lower bound only | construction |
| Östergård & Pettersson, *Exhaustive search for snake-in-the-box codes*, Graphs & Combin. 31 (2015) 1019-1028 | snakes, edges | **s(8) = 98** exact | n/a | exhaustive orderly generation with canonical augmentation, not SAT/ILP |
| Östergård–Pettersson (dimension 7, and coils in dimension 8) | snakes and coils | s(7) = 50, c(7) = 48, c(8) = 96 (c(8) = 96 is as cited in Mütze's survey) | n/a | exhaustive search |
| Allison & Paulusma, arXiv:1603.05119 (2016) | both | "for n >= 9 only lower bounds ... are known" | none | beam-search lower bounds |
| Mütze, *Combinatorial Gray codes – an updated survey*, EJC DS26 (2nd ed., 2024) | both | Zémor's bound is the best known coil bound; s(n) >= c(n) - 2; exact values for n <= 8 | none for snakes | survey |
| Orland et al., arXiv:2607.15270 v3 (2026) | snakes in edges, coils in vertices (= edges) | **a(9) >= 191** (131 classes); coil c(9) >= 192; "for n >= 9, only lower bounds are known"; whether a 192 snake exists in Q9 is listed as open | lower bound 191 | snakepit surgery and learned construction |
| Taylor, arXiv:2609.27483 (23 Sept 2026) | snakes and coils | s(d) >= (17/48)·2^d for d >= 21, improving 77/256 | lower bound only | compatible paths in Q20 |
| DeepMind formal-conjectures, `FormalConjectures/Wikipedia/SnakeInTheBox.lean` | snake (Mathlib induced path, edges) | `snake_upper_bound : LongestSnakeInTheBox n <= 2^(n-1)` (cites DK67 Thm B); `snake_dim_nine_lower_bound : 190 <= ...` (out of date); PR #6763 (Sept 2026) set 2^(n-1) as "the best upper bound I could find in the literature" | **256** | sorry-stubbed statement, not a proof |

**Note on coil bounds versus snake bounds.** Using the repo's census identity (`milestones/03-square-incidence/square_investigation.md:25`) with the endpoint correction dropped, a coil satisfies 2·A0 + A1 + 35v = 9216. A Lukito–van Zanten-type condition A1 >= 2v then gives v <= 249, i.e. 2^(n-1)(1 - 2/(n²-n+2)) at n = 9. This is my own arithmetic, not a cited value. It applies only to coils. The paper shows the per-vertex condition fails for open snakes: there is a 137-edge snake with an internal vertex of singleton count 1 (`paper/snake9_research.tex:184-195`). `RESEARCH_LEDGER.md:33` also warns: "Do not transfer cycle upper bounds to paths without proving a bridge."

None of these cycle bounds needs to be transferred to compare novelty: even the strongest one at n = 9 (about 249) is weaker than the repo's 245, 241 and 238.

## Answers to the specific questions

- **n = 8:** s(8) = 98 edges, from Östergård–Pettersson (2015), by exhaustive search with canonical augmentation. That is a computer search, not SAT/ILP. The 98-edge snake was constructed earlier by Carlson–Hougen (`paper/snake9_research.tex:60`). For coils, c(8) = 96.
- **n = 9 upper bound in the literature:** 256 (Danzer–Klee 2^(n-1)) is the only explicit snake bound I found. Asymptotic coil bounds (Snevily, Zémor, Emelyanov–Lukito) give nothing better at n = 9. I found no SAT, ILP or LP upper-bound computation for n = 9.
- **Comparison:** the repo's 241 (kernel-checked through 22 window certificates) and the targeted 238 (175 five-centre windows) are, as far as I could find, the first published or claimed snake upper bounds for Q9 below 256. They do not improve on a prior Q9 bound, because none existed below 256.
  - **Caveat 1:** I could not read the full texts of Emelyanov–Lukito (2000), Lukito–van Zanten (2001), Lukito TR 98-07 (Delft, 1998), *Upper and lower bounds for the length of snake-in-the-box codes*, or Drapela's 2015 UGA thesis (Appendix B, a timeline of coil upper bounds). A small-dimension table in one of them could contain a coil number for n = 9. A coil number would still not bound open snakes unless a bridge is proved.
  - **Caveat 2:** UpperBound238 depends on the replay build still running. Only call 238 "proved" after its `#print axioms` audit (`UpperBound238.lean:24-25`) passes.
- **Lower bound:** **191 edges**, from Orland, Fagan, Tarquini, Passaro, Manko, Heyes, Gruen, Butbaia, Tan and Gukov, arXiv:2607.15270 (earlier versions were titled "A Census of New Snake-in-the-Box Records"), with data at github.com/Math-AI-Caltech/Snake-in-the-Box. It improved Wynn's 190 from 2012 (arXiv:1201.1647). The same work gives a 192-vertex coil in Q9, up from Wynn's 188. I found no report of a 192-edge snake in Q9 as of Oct 2026.

## URLs

- Orland et al.: https://arxiv.org/abs/2607.15270 and https://arxiv.org/html/2607.15270v3 ; dataset README (read directly): https://github.com/Math-AI-Caltech/Snake-in-the-Box
- Taylor 2026: https://arxiv.org/abs/2609.27483
- Östergård–Pettersson 2015: https://doi.org/10.1007/s00373-014-1423-3 ; https://research.aalto.fi/en/publications/exhaustive-search-for-snake-in-the-box-codes/
- Coil-in-the-box, dimension 8: https://www.sciencedirect.com/science/article/pii/S0166218X14003114
- Zémor 1997: https://link.springer.com/article/10.1007/BF01200911
- Deimer 1985: https://link.springer.com/article/10.1007/BF02579373
- Snevily 1994 formula: https://math.wvu.edu/~jwojciec/research/10erdos.pdf ; https://archive.lib.msu.edu/crcmath/math/math/s/s453.htm
- Danzer–Klee 1967: https://sciencedirect.com/science/article/pii/S0021980067800267
- Emelyanov–Lukito 2000: https://research.tudelft.nl/en/publications/on-the-maximal-length-of-a-snake-in-hypercubes-of-small-dimension/
- Lukito–van Zanten 2001: https://combinatorialpress.com/article/jcmcc/Volume%20039/vol-039-paper%2012.pdf
- Abbott–Katchalski 1988: https://www.sciencedirect.com/science/article/pii/0095895688900512
- Allison–Paulusma: https://arxiv.org/abs/1603.05119
- Mütze survey: https://arxiv.org/abs/2202.01280 ; https://www.combinatorics.org/ojs/index.php/eljc/article/view/ds26
- Wynn 2012: https://arxiv.org/abs/1201.1647
- OEIS A099155: https://oeis.org/A099155
- Wikipedia: https://en.wikipedia.org/wiki/Snake-in-the-box
- Drapela thesis: https://ai.uga.edu/sites/default/files/inline-files/theses/drapela_thomas_e_201505_ms.pdf
- formal-conjectures: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/SnakeInTheBox.lean ; PR https://github.com/google-deepmind/formal-conjectures/pull/6763 ; issue https://github.com/google-deepmind/formal-conjectures/issues/5714
