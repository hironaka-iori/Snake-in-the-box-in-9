# Counting embeddings with two coordinate histories free

This is a written proof review. No numerical computation or compiler was run.

Let $P=((z_i,u_i))_{i=0}^{m}$ be a nonempty ordered induced cube path, where $u_i\in Q_2$ and $z_i$ contains all other coordinates. For $\varepsilon\in\{0,1\}$, let $B_\varepsilon$ be the occupied base words at block parity $\varepsilon$, with adjacency inherited from the base cube. Let $c_\varepsilon$ be its number of components, taking the empty graph to have zero components, and put

$$
r=\bigl|\{\varepsilon:B_\varepsilon\ne\varnothing\}\bigr|.
$$

The proposed counts are correct:

$$
\#\{Q=((z_i,v_i))_{i=0}^{m}:Q\text{ is an ordered induced path}\}
=2^{1+c_0+c_1},
$$

and the number of classes under global isometries acting only on the two block coordinates is

$$
2^{c_0+c_1-r}.
$$

## Exact parametrization

Fix a flip $X$ of the first block coordinate. In any target path, the difference between source and target full-vertex parities is constant, since both parities change at every step. Their indexed base words agree, so this is also their constant block-parity difference $\delta\in\{0,1\}$.

After applying $X^\delta$ to the target, its selected correspondence in each base fibre is an injection preserving block parity. On each occupied two-element parity diagonal it therefore extends uniquely to the identity or its transposition $\tau_\varepsilon$. This gives one binary selector on every occupied base word of each parity.

The selector must be constant on each component of $B_\varepsilon$. For neighbouring active base words, unequal selector values toggle equality of any selected pair of block words in that parity diagonal, and consequently toggle full adjacency. Both paths' inducedness excludes this change.

Conversely, choose a selector independently for each component, apply the corresponding diagonal transpositions, and then apply $X^\delta$. This preserves every selected-pair relation. Opposite block parities always have block distance one, so their adjacency is unaffected. For equal block parity, only neighbouring base words can have their adjacency changed, and those active base words lie in one component and receive the same transposition. Each slice map is injective, so all full vertices remain distinct. Thus the resulting indexed sequence is an induced path.

Different parity offsets give different block parities at every index. With offset fixed, different component choices change a selected word in that occupied component. The parameters therefore give a bijection, proving the first count.

## Restricted global-isometry classes

The eight isometries of $Q_2$ act on these ordered target paths. This action preserves the family because every base coordinate remains fixed. Its parity-preserving subgroup is

$$
K=\{1,\tau_0,\tau_1,\tau_0\tau_1\}.
$$

An isometry with odd parity offset fixes no block word, so it cannot stabilize a nonempty ordered target. Within $K$, switching an occupied parity diagonal changes every selected word of that parity; switching an unoccupied diagonal has no selected effect. Hence every target has stabilizer size $2^{2-r}$ and orbit size

$$
\frac{8}{2^{2-r}}=2^{r+1}.
$$

The number of occupied parities is unchanged by the group action, although the two parity labels may be exchanged. Dividing the first count by this common orbit size proves the second count.

Equivalently, every orbit has a unique representative obtained by normalizing the parity offset to zero and fixing the selector on one chosen component of each occupied parity to zero. Two normalized representatives can be related only by a parity-preserving block isometry, which complements all component selectors of one parity together. No additional identifications occur within this restricted group action.

## Degenerate cases and scope

- For one vertex, exactly one parity graph consists of a single vertex. The counts are four ordered targets and one restricted isometry class.
- If only one block parity occurs anywhere on a connected path, no path step changes a block coordinate. The block word is therefore constant, and the occupied base graph is connected. Thus this case always has $r=1$ and $c_0+c_1=1$, again giving four targets and one class.
- If both block parities occur, $r=2$. The global block-isometry action is free, with orbit size eight, and the class count is $2^{c_0+c_1-2}$.

These are counts of ordered paths preserving every indexed base word, without imposing a fixed initial block word or fixed endpoints. Additional such conditions change the count. The class formula concerns only global isometries of the two chosen block coordinates. Allowing base-coordinate isometries, exchanges between base and block coordinates, or reversal can merge further classes and is outside the asserted formula. No finite component counts for a saved research witness are certified by this proof alone.
