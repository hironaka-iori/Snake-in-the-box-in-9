# Round 5: three-centre target arithmetic and the two live shapes

The requested arithmetic and mathematical scope are proved in target_thresholds.md. The exact independent program is triple_bound_arithmetic.py, with results in triple_bound_arithmetic.json.

The 255 threshold for every three-centre window would imply at most 234 edges. The proposed threshold 268 for 233 edges can be reduced to 267 when the completed single-centre lower bound 22 is used for the two leftover internal vertices. Strict exclusion margins are respectively 8/7 and 2/21. Remainder transitions have positive increments, so these contradictions exclude all longer snakes as well, not merely the single critical length.

Exactly two direction shapes are possible: 0120 and 0123. An independent check of all 6,561 four-direction words gives 504 instances of the first and 3,024 of the second. Both are needed before making a universal three-centre statement.

The project endpoint theorem was verified in source: endpoint_alpha_ge_four is a proved theorem under the nontrivial-snake and endpoint-index premises. Its alpha definition agrees with the one in the new score. I independently checked the 121-vertex sharpness example and confirmed endpoint alpha exactly four. No Lean kernel was rerun here.

The static8-fold optimization is sound. A removed cycle clause contains at least one literal whose negative selected unit is already in the fixed-path CNF. I confirmed those units are present. The CNF hash is calculated from the actual filtered clause list, so RUP hint indices retain their meaning.

I independently regenerated both full eight-cycle manifests, compared exact vertex-set lists, reconstructed the filtered static CNFs and matched their checkpoint SHA256s. Complete proof-prefix replay gives:

- 0120: 94,557 active static eight-cycle cuts; 7,628 checked RUP steps and 980,059 unit hints; no empty clause and no SAT model.
- 0123: 94,280 active static eight-cycle cuts; 7,408 checked RUP steps and 1,076,943 unit hints; no empty clause and no SAT model.

Both remain unresolved after the initial finite budgets. Thus neither 234 nor 233 has been proved by these experiments. There is currently no decoded local SAT counterexample at cap 254 either. Continue from the verified proof checkpoints rather than conflating search difficulty with infeasibility.
