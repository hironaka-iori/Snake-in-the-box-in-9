# Next construction if one exchange is excluded

This is a proposed experiment, not an executed search or a proof of existence.

Allow two replacements in a saved 96-vertex minority class. Direct enumeration has 145 times binomial(96,2) times binomial(160,2) descriptions. A joint exact model can choose the class and ordering together instead.

Select 96 cube vertices of the minority parity and 97 of the majority parity. Relative to a fixed saved class U, select exactly 94 of U and two same-parity vertices outside U. Allow every ordering and crossing pattern. Both endpoints lie in the majority class.

Every selected vertex has exactly two selected cube neighbours, except two flagged endpoints have exactly one. Endpoint flags imply selection and are allowed only in the majority class. These degree conditions prohibit chords, although they alone still permit disconnected paths and cycles.

Enforce connectivity with one optional-vertex circuit on all 512 cube vertices and a dummy. Unselected vertices take self-loops and selected vertices cannot. Allow both directions of each cube edge. Join the dummy only to flagged endpoints, with exactly one dummy incidence per endpoint. The dummy has no self-loop. Removing it from the single circuit gives a path through every selected vertex. The selected-neighbour conditions make that path induced.

Decode any candidate as 193 distinct actual cube vertices and check every unordered pair. This independently establishes a witness. Infeasibility excludes only the chosen two-exchange family; a time limit leaves it unresolved. Inspect existing optional-vertex circuit models in the repository before implementing this experiment.

Begin with a small number of saved classes under a bounded search, then choose the next step from the resulting evidence. The projected-class view allows additions beyond one lower-dimensional path. Partial greedy growth remains optional when useful. No global upper-bound work is proposed here.
