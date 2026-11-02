# Minimum 012034 floor and the resulting integer floor box

The least nonnegative integer floor for 012034 that retains conditional 234 in this fixed graph argument is 18, with all other eight full-profile floors unchanged. The adjacent floor 17 is obstructed for every constant slope and global potential range under the same boundary budget.

Exactly five additional candidates were tested by binary search:

|012034 floor|Result|Certificate|
|---:|---|---|
|9|Obstructed|10-edge walk, weight 4324, deficit 636|
|14|Obstructed|16-edge walk, weight 7304, deficit 632|
|16|Obstructed|27-edge walk, weight 12760, deficit 632|
|17|Obstructed|51-edge walk, weight 24663, deficit 633|
|18|Sufficient|Slope 496, potential range 602, strict margin 30|

The unchanged three-edge cycle has total weight 1488. Floor 18 has a potential satisfying

\[
496+\pi(v)\le w(u,v)+\pi(u),\qquad 0\le\pi\le602
\]

on all 4,947,008 edges. The independent verifier checks every edge, the potential bytes and range, and every saved full-key walk. Consequently the exact minimum cycle mean at floor 18 is 496 and the conditional comparison is

\[
4696m\le1103530,
\qquad
m\le\frac{551765}{2348}=235-\frac{30}{4696}<235.
\]

At floor 17, the cycle gives $\mu\le496$ for any admissible slope. The 51-edge walk gives $51\mu-24663\le R$. Therefore

\[
227\mu-R\le176\cdot496+24663=111959<111960.
\]

The required 234 criterion $227\mu-R>111960$ is impossible. The edge weights are nondecreasing in the 012034 floor, since each is the maximum of a fixed base credit and the floor-dependent credit. Thus the 18 potential remains sufficient for every higher floor, while the 17 obstruction remains valid for every lower floor. This proves the threshold among integer floors for this exact edge set, weight formula and boundary argument.

## Re-evaluation of the saved seven-edge path

The milestone 93 full-profile seven-edge path remains weight 2872 at floor 18. Its deficit is 600, not 602. It therefore does not certify that range 602 is least, and it does not establish joint slope/range optimality for the modified profile. No replacement tight path was sought. The check and exact source hash are recorded in `saved-seven-edge-path-check.json`; no new range-optimality certificate is claimed.

An initial verification assertion tentatively tested the requested 2870 possibility and failed. The corrected verifier records the actual 2872 result explicitly. The adjacent-floor threshold is established by separate certificates and is unaffected.

## Complete consequence inside the integer floor box

Use case order 7301,7302,7303,7307,7308, and keep the completed target floors 012031,012304,012310,012314 fixed at 16,16,12,16. Among nonnegative **integer** vectors bounded componentwise by the original target vector $(16,20,16,16,16)$, the vectors that admit the current 234 potential criterion are exactly

\[
(16,h,16,16,16),\qquad h\in\{18,19,20\}.
\]

Necessity follows by comparison of weights. If any of the four 16 coordinates is at most 15, the vector lies componentwise below the corresponding independently checked one-unit obstruction profile from the parent experiment. If the 012034 coordinate is at most 17, it lies below the new17 obstruction profile. A potential valid for smaller edge weights would also be valid for larger ones, contradicting the appropriate obstruction.

For sufficiency, each displayed vector is componentwise at least $(16,18,16,16,16)$. The checked floor 18 potential therefore remains valid.

This consequence assumes the same full-key edge set and endpoints, the same fixed base weights, the pointwise nondecreasing maximum rule, and the same boundary inequality. It concerns the original integer floor box; intermediate real-valued floors are not classified. It neither proves local share minima nor excludes improvements from new graph restrictions, different boundary estimates or another global argument. The saved supporting assertions and receipt hashes are in `integer-floor-box.json`.

## Evidence and scope

- `search.py`: binary search using the existing exact integer potential/path method. Run with Python's `-B` option to avoid bytecode cache output.
- `input-pins.json`: immutable graph inputs, explicit baseline floors and hashes of every pre-existing parent experiment file.
- `known-zero-obstruction.json` and `known-nineteen-feasible.json`: rechecked initial bracket.
- `floor9.json`, `floor14.json`, `floor16.json`, `floor 17.json`, `floor 18.json`: full-key certificates for the five additional candidates.
- `floor 18-potential.i64.gz`: complete little-endian 64-bit potential table.
- `verify.py` and `verification.json`: independent reconstruction, all-edge potential verification, adjacent obstruction, original-file preservation and separate saved-path check.
- `results.json`: completed search with no unresolved interval.

Discovery took 20.875 seconds. The verification receipt records its own elapsed time; the root researcher also reran the independent verifier successfully. An earlier short verification attempt stopped at the extra saved-path assertion described above. Total additional numerical work remained below 30 seconds, within the 600-second allowance. No extra candidate, Lean compiler, SAT/LRAT replay or background daemon was started.

Every pre-existing parent research file remains hash-identical. A generated Python cache beside the parent script is left in place as instructed and excluded from evidence manifests.

The 602-range potential is evidence on the saved finite arrays. Its transfer to the graph defined by acceptance tests, including possible extra edges, remains separate. Local share proofs, reference premises, graph coverage, complete weight interpretation and the potential replay retain their existing status. The global interval remains $191\le a(9)\le235$; 234 remains conditional.
