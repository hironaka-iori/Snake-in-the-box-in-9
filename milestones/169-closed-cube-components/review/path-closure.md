# Generic path closure and the isolated-edge application

## Lean source

PathClosure169.lean imports only PathStructure. The statement closed_selected_contains_all uses a predicate A on cube vertices, a selected vertex in A, and closure under adjacency between selected vertices. It proves that every selected vertex lies in A. There is no requirement that every vertex satisfying A is selected; only its intersection with the path matters.

The proof first propagates membership backwards to index zero by induction on the starting index, then forwards to each index. It uses path_adj_iff and arithmetic, with no enumeration or new axioms. The companion closed_selected_no_outside packages the contradiction from a selected vertex outside A.

Status: source drafted by this worker; compilation is delegated to the coordinating agent. No compiler was invoked here.

## Written review of the eight-cycle application

Under absence of all unit vertices, take two isolated edges {a,a'} and {b,b'} of the missing-pair graph. Let A be the four cross-pairs and the four candidate triples supported on these two coordinate blocks. All four cross-pairs are selected. As reviewed in milestone 168, every selected neighbor of a selected vertex in A is again in A: the pair vertices allow only partner-added triples, and each selected triple already has its two cross-pair neighbors, excluding selected weight-four neighbors. Thus A meets the path and is closed under selected adjacency.

The generic closure theorem confines the whole path to these eight vertices. Counting alone gives m <= 7. Since selection of all eight produces a cycle, one vertex must be absent, strengthening this to m <= 6. In fact all four alternating pair vertices must occur, and connectivity permits exactly three selected triple vertices, so confinement forces m = 6. These sharper counting statements are written deductions only; the generic source does not prove them.

There is a stronger and simpler contradiction specific to Q9. Choose any coordinate k outside {a,a',b,b'}. Because a has exactly one incident missing pair, namely {a,a'}, the pair {a,k} is selected. Its support includes k, so it lies outside A. This contradicts closed_selected_no_outside directly. Therefore two isolated edges in the missing-pair graph are impossible at an undominated center of an actual nontrivial Q9 snake, without a snake-length threshold.

The support-distinctness assertion and the actual-cube closure proof still need Lean assembly. They cannot be replaced by the generic closure theorem alone. The argument works in any dimension at least five where an outside coordinate exists, under the same actual-path and absent-unit hypotheses.
