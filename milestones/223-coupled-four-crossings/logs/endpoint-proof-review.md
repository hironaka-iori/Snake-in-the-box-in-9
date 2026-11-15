# Endpoint-neighbour exclusion: prepared source

Status: source prepared only. No compiler, native worker or software tests have been run for this module. Compilation awaits the parent's resource-slot release.

The module imports the accepted `LayerJoining` source and introduces no definitions. It uses its actual indexed induced-path structure, with explicit irreflexivity and symmetry of the ambient adjacency relation.

`last_neighbour_unique` first derives that any selected vertex adjacent to the last endpoint has index exactly one before the final index. Irreflexivity excludes the final index itself. Every other index is smaller, so symmetry and inducedness force it to be consecutive with the last index. Two such neighbours therefore have equal indices and equal vertices. No endpoint-degree bound is assumed.

`distinct_neighbour_not_selected` then derives exclusion from the entire path: if one selected neighbour is retained and a distinct candidate is also adjacent to the final endpoint, selecting that candidate would contradict the first theorem. The conclusion quantifies over every path index.

The intended application takes the last endpoint to be vertex 80 and a retained selected neighbour to be 88. Supplying adjacency of 208 to 80 and inequality of 208 and 88 then excludes 208 from the path. These concrete cube facts and the identification of the actual final endpoint are application premises, not checked numerical assertions in this module. No heavy cube data are imported.

The statement also covers a one-vertex path: its neighbour premises are impossible by irreflexivity. A component's temporary boundary vertex must not be substituted for the actual final endpoint of a longer path. In a four-crossing construction, the theorem is applied to the appropriate full path or to an explicitly fixed component endpoint, with membership restricted to that same path.

Two exported axiom reports are requested. No accepted compiler or numerical-construction claim is made at this source-preparation stage.
