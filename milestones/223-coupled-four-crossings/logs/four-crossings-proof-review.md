# Five-path constructor: source preparation

Status: source prepared only. No Lean compiler, native worker or software tests have been run for this module. Compilation awaits the parent's resource-slot release and staging of accepted imports.

## Statement and premises

`FourCrossings223.fourCrossings` accepts five actual `LayerJoining.InducedPath` objects of lengths `a,b,c,d,e` and constructs an induced path in the product with one binary edge, of length `a+b+c+d+e+4`.

The order and layers are `p(false), q(true), r(false), s(true), t(false)`. The four consecutive pairs satisfy the existing exact `Compatible` predicate: their projected equality occurs precisely at the terminal index of the first path and the initial index of the next path. The four nonconsecutive same-layer pairs `(p,r)`, `(p,t)`, `(r,t)`, `(q,s)` are disjoint and nonadjacent. The two remaining opposite-layer pairs `(p,s)` and `(q,t)` have disjoint projections. Projected adjacency for these last two pairs is permitted because it does not create a cross-layer cube edge.

These ten premises cover every component pair. No general connectivity or degree assumption replaces the constructive ordering. The lengths are arbitrary natural numbers, so singleton outer components remain permitted. A zero-length interior component would force an equality forbidden by the same-layer separation premises; no unnecessary positivity hypothesis is imposed.

## Reused source and proof plan

The source imports the accepted `TwoCrossings188` module, which in turn imports `LayerJoining`. It reuses `appendEdge`, `appendVertex`, `inLayer`, `LayerAdj`, `Compatible` and `InducedPath` without redefining them. Their current source hashes were inspected:

- `188-dimensional-constructions/lean/TwoCrossings188.lean`: `764efb0102a2ce2d22ef0dd7e7a923958232bb5836c203e696361f42b536ef3a`.
- `188-dimensional-constructions/lean/LayerJoining.lean`: `30687e190d96818b64569e90faaff50eba28acf7698e4ffa8c6d89d8fe640a74`.

Private lemmas propagate separation through an existing append and derive the single final contact with a new component. Three small layer lemmas translate the original projection premises into the actual product graph. Four applications of the accepted append constructor then supply bounded injectivity and induced adjacency for the entire ordered path. A final arithmetic equality states its length. The module adds one public constructor and no new compatibility or graph definitions.

The resulting path uses every input component vertex in order. Its layer is constant within each component and alternates at the four appends. The exported type checks inducedness and total length; a separate numerical crossing-count theorem is not requested in this source.

## Scope and remaining work

This would supply the indexed assembly absent from the round-195 written two-forest criterion. It does not generate compatible components, prove a target allocation exists, certify an arbitrary component-incidence graph, or verify a native search. A finite candidate must still supply the five oriented paths and all ten pairwise premises. The existing `8+25+10+25+26+4=98` decomposition fits the signature; no concrete instantiation has been added here.

The parent must stage the accepted import source/object/receipt closure. Once the compiler slot is granted and the ordinary round-223 helpers are available, the intended commands are:

```powershell
& 'C:\Users\hironakaiori\AppData\Local\Programs\Python\Python314\python.exe' 'E:\Snake-in-a-box\milestones\223-coupled-four-crossings\scripts\prepare_proof.py' FourCrossings223
& 'C:\Users\hironakaiori\AppData\Local\Programs\Python\Python314\python.exe' 'E:\Snake-in-a-box\milestones\223-coupled-four-crossings\scripts\check_core.py' FourCrossings223 --timeout 60
```

No compilation or accepted axiom claim is made at this preparation stage. No new numerical bound, witness or novelty claim follows from the source alone.
