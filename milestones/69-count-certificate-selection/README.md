# Milestone 69: select count exclusions for the target bound

**Completed research round.** The conditional empty-square estimate 234 can be retained with 18,788 additional count keys, compared with the 25,279-key basis recorded in milestone 68. The reference catalogue now reuses 1,378 keys from the completed contributor 235 and 236 proofs. The additional selected keys remain proof obligations. The maintained global interval is still 191 ≤ a(9) ≤ 235.

## Restore transitions before selecting exclusions

The selection begins with every canonical nine-direction word and every six-symbol count assignment. The reference exclusions are applied at every contiguous position where their counts are present, including both orientations. Three previously checked eleven-direction count restrictions are also retained. This leaves 6,086,947 candidate transitions with the existing history states.

The earlier graph applied its count catalogue only at the entering suffix. Applying the reference at all positions removes additional impossible transitions. Consequently raw edge counts are not a direct measure of the effect of deleting additional numerical keys. Every new local filter is an occurrence of a retained reference key.

For a potential π, integer numerator p and denominator 29, define the transition slack by

\[
29w(e)+\pi(u)-\pi(v)-p.
\]

A negative-slack transition must be excluded to use this particular potential. For each such transition, the selection records every additional key occurring within it. At least one of these keys must be selected. A singleton list forces its sole key to be selected.

For the original numerator 14392, the mandatory singleton keys already cover every negative transition. Thus they constitute the unique least cover within this fixed candidate basis. The independent verifier checks every mandatory witness and reconstructs the complete graph after applying the selected keys.

## Reuse completed proofs

The initial 1,287-key reference came from the contributor's 235 proof. Cross-checking the earlier 732-key catalogue from the completed 236 proof finds 91 additional distinct keys. Their union has 1,378 keys. These earlier contributor proofs and receipts are reused; their complete dependency chains were not rebuilt this round.

With the larger reference, the original potential requires 18,825 additional keys. This includes 16 four-count keys, 1,506 five-count keys and 17,303 six-count keys. All 18,825 are mandatory for this potential within the candidate basis. The initial reference-only comparison, before adding the 91 keys, is preserved in `data/base235-summary.json` and `data/base235-verification.json`.

## Use only the strength required for 234

The full minimum mean is stronger than is required for the target integer bound. Keep the potential and its range 18984, but lower its required numerator from 14392 to 14387. The potential premise becomes

\[
14387(m-8)\le29W+18984.
\]

Together with the established boundary budget W+4200m≤1098960, this gives

\[
136187m\le32003920,
\qquad
m\le\frac{32003920}{136187}<235.
\]

At m=235 the left side exceeds the right side by 25. With this denominator, potential range and boundary constant, any integer numerator at most 14386 would allow 235 in the final inequality. Lean checks both the sufficient numerator and this limitation.

This relaxation removes 37 further six-count keys. The final selection is:

| Internal counted positions | Additional selected keys |
|---|---:|
| 4 | 16 |
| 5 | 1,506 |
| 6 | 17,266 |
| Total | 18,788 |

There are 839,898 negative candidate transitions. Their 21,528 distinct key lists are all covered by the 18,788 singleton-forced keys. Each selected key has an independently checked witness showing why that key is necessary when the candidate basis, potential and target numerator are fixed.

The resulting graph has 4,028,578 retained transitions. Every one satisfies the relaxed potential inequality. The value 14387/29 is a sufficient slope for this certificate; no claim is made that it is the exact minimum cycle mean of the resulting graph.

## Verification scope

- `data/selection-14387.json.gz` records the final selected keys, negative-transition clauses and mandatory witnesses.
- `data/verification-14387.json` records independent reconstruction of all candidate and retained transitions and every mandatory witness.
- `data/selection.json.gz` and `data/verification.json` retain the comparison at numerator 14392.
- `data/provenance.json` pins the input catalogues, geometry, history model, potential and contributor snapshot manifest.
- `data/lean-audit.json` records two successful Lean modules and eight standard-axiom audits. These prove the general least-cover argument, exclusion-to-potential implication and target arithmetic. They do not check the concrete graph enumeration or establish impossibility of the selected count keys.

The least-cover conclusion is limited to the fixed potential, numerator, reference rules and candidate basis. Other potentials, stronger proved count properties, different boundary inequalities or a different candidate family may reduce the proof workload further. No minimality claim is made for a proof of the global bound.

## Next step and reproduction

The next round will test a model using only proof-supported exclusions and shares, in accordance with the requested alternation between conditional and unconditional optimisation. Varying the potential remains a subsequent conditional task. The current 18,788-key set is a sufficient finite target, and a different potential may require fewer keys.

Run `select.py` and `verify.py` for the original numerator, then `select.py 14387` and `verify.py 14387` for the final target. Run `replay.py --resume` and `audit_lean.py` for the generic selection and arithmetic proofs. Existing input datasets and compiled Lean dependencies from preceding milestones are required. Generated graph arrays and proof objects are ignored.

This is research round 3 of 10 after manuscript revision 66. The paper and its editor mirror remain unchanged; the next full manuscript revision is scheduled for milestone 76. GitHub was refreshed and the contributor branch remains at `97851813`.
