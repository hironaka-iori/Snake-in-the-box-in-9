# Two ways to rebuild the opposite arm to 188 edges

## Keeping the 97-edge arm of Casella’s 186-edge example

Casella’s example crosses the ninth coordinate once. Keeping its 97-edge arm and the same crossing endpoint leaves an 88-edge opposite arm to replace. The reconstructed partner has 90 edges. In the rooted coordinates of the saved parent, the following digits specify the axes to flip, starting from zero. The parent and its full ordered nine-dimensional lift are in the construction file. [Casella, Appendix A.1](https://www.ai.uga.edu/sites/default/files/inline-files/theses/casella_darren.pdf) · [Original parent and partner](../270-optimal-seven-dimensional-arms/historical-q9-controls.json) · [Rebuilt 188-edge path](casella-rebuilt-188.json)

```text
310214321023541346021034106312634521024302107346025413421043142541302136245214310231430521
```

The fixed eight-dimensional arm uses axis 7 exactly once. The new opposite arm also uses it exactly once, after 44 edges and before the remaining 45 edges. This divides each of the two eight-cubes into two seven-cubes. Each piece of the opposite arm must avoid the corresponding fixed piece, except for the shared starting vertex at the ninth-coordinate crossing. The two pieces of the opposite arm must themselves share only their crossing point when projected along axis 7. Matching pieces under these conditions produced the 188-edge construction. All 17,766 unordered pairs of its vertices passed the induced-path check. The original 88-edge partner crossed that internal axis twice. [Search over seven-dimensional pieces](matched.py) · [188-edge target run](matched-188.json)

### Exact maximum when both arms use the same internal coordinate once

At the original Casella crossing the maximum under this additional restriction is **188**. To reach 189 the opposite arm would need at least 91 edges. Write its two seven-dimensional lengths as $u$ and $v$. Then $u+v\ge90$. Either $u\ge45$, or $u\le44$ and $v\ge46$.

In the first case every eligible first segment from the outer crossing was enumerated. There were 15 of length at least 45. Five ended at a permissible crossing point, distributed over three different points. At each point, every sufficiently long second segment was sought after blocking the fixed arm and the shared sites of all candidate first segments. None could complete the join. In the second case the longer segment was enumerated first at all 31 permissible crossing points. This gave 30 candidate segments of length at least 46. Enumerating the shorter segment between its specified endpoints gave no compatible pair.

A second traversal used occupied-neighbour counts for free endpoints and reversed the traversal between two specified endpoints. The first segment was divided by its initial edge to finish the independent replay. A longer join at this crossing must make at least two uses of the internal coordinate in the rebuilt arm, since a path staying on one side has at most 50 edges. The unrestricted opposite-face search permits those additional crossings. [Complete enumeration](balanced-Casella-A1-189.json) · [Second-endpoint replay](balanced-Casella-A1-189-replay.json) · [Completed first-step replay](balanced-first-replay.json)

## Keeping the 96-edge parent of the 187-edge example

A second construction keeps the 96-edge parent and crossing of the previous round’s 187-edge snake. Its original 90-edge partner occupied 91 sites. An unrestricted 91-edge partner in the opposite face was sought while allowing at most nine of those sites to be omitted. The solution kept 82 sites, omitted nine and added ten. The joined path has 188 edges. The comparison concerns occupied sites, so the search can also change the order in which the retained sites are visited. [Earlier 187-edge path](../270-optimal-seven-dimensional-arms/best-187.json) · [Search and witness](retained-sites.json) · [Checked paths](retained-site-replay.json)

Nine omissions are necessary and sufficient for this improvement. A contradiction certificate excludes every 91-edge partner omitting at most eight old vertices, and the construction omits exactly nine. The replay reconstructed the selection constraints and verified the saved contradiction. It also checked the entire ordered path for each positive result. [Minimum-omission result](minimum-omissions.json) · [Reconstruction method](retain.py)

## Why the two constructions have different shapes

A nine-dimensional snake using two different coordinates exactly once would split at those two edges into three seven-dimensional paths. Each has at most 50 edges, giving at most $3\cdot50+2=152$ in total. A 188-edge one-crossing snake therefore has a unique coordinate used exactly once. Its unordered pair of arm lengths is invariant under cube symmetries and path reversal. The two splits here are $97+1+90$ and $96+1+91$, so they give inequivalent snakes. Independently normalizing both transition sequences gives different representatives. [Crossing counts and symmetry comparison](comparison-188.json)
