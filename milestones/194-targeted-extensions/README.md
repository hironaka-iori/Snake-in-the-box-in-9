# Round 194: targeted endpoint extensions

One contiguous replacement of at most 44 edges followed by one endpoint addition is computationally excluded for all 131 saved Q9 snakes. This is a one-operation result, distinct from round 193's repeated-move closure through 33 edges.

A known suboptimal48-edge Q7 lift resists the same operation through 37 edges, yet an explicit43-edge replacement produces49. Both paths and their retained coordinates pass Lean. This comparison shows why local obstructions cannot establish global optimality.

Read [the argument](MATHEMATICAL_NOTE.md), [coverage](data/completion.json), [input audit](data/input-audit.json), [aligned49-edge path](data/aligned-lower49.json), and [handoff](../../handoff/CURRENT_STATUS.md). Numerical exclusions remain native. Solver models are packaged in data/solver-models.zip; extract it into this milestone folder before replaying recorded model paths. Local raw models are also retained.
