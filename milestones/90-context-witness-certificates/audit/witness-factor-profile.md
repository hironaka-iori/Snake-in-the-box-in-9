# Witness factor profile

The existing validator can be represented on the saved planned entries by four explicit factors: the outer bounds, the catalogue/placement guards, the direction or history shape test, and the box/count test. Every one of the **357,823 planned entries** was evaluated directly and compared with the conjunction of these factors. All comparisons agree and all original entries are true.

This is a proposed proof-factorization opportunity. It is not a new Lean equivalence theorem or a measured speed improvement. All tested saved entries are valid; the computational comparison does not establish equivalence on arbitrary invalid inputs.

## Exact counts

| Family | Planned occurrences | Unique catalogue-indexed shape calls | Unique normalized shape tests | Unique box tests |
| --- | --- | --- | --- | --- |
| reference | 338697 | 337485 | 12560 | 2319 |
| short | 16341 | 4624 | 2260 | 282 |
| interval | 2782 | 2780 | 530 | 48 |
| history | 3 | 3 | 3 | 2 |

Factor catalogue sizes: outer_guards: 508, catalogue_guards: 2329, shape_factors: 15353, box_factors: 2651.

There are **4,609** unique full box/witness pairs and **356,595** distinct direction/history/box/witness calls in the plan. Normalizing only the tested box conditions gives **2,651** distinct box factors. The full descriptor tables include usage counts and first-occurrence provenance.

## Conditions retained

The outer factor retains box length 6, history below 75 and direction below 505. Catalogue factors retain the exact index/length comparisons and placement constraints. Reference shape descriptors keep the actual direction word, drop offset, slice length, reversal and target pattern; only the count-symbol values and catalogue index are removed from that shape key. The omitted values remain in the box/count factor and catalogue guard. Thus keys sharing a direction pattern can reuse shape evidence without sharing their distinct count assertions.

Reference box factors check both interval endpoints equal the oriented symbol. Short cap factors retain each tested upper bound and its cap. Short sum factors retain every position, multiplicity, actual interval, total cap and the strict condition that every tested upper endpoint is below 6. Interval factors retain the reversed position computation, its bound below 6 and both containment inequalities. No cap-6 or saturation exception is dropped.

History descriptors retain the source word and prefix, recompute `extensions.idxOf` from the original direction table, append the decoded index, require length at least three and compare the final three IDs. The decoded result is recorded explicitly and checked. The three history catalogue/box tests retain their rule indices, count positions and upper cap 2. Natural subtraction is truncated at zero exactly where used by the Lean definitions.

## Reproduction and scope

Run `scripts/profile_witness_factors.py` to reproduce the profile. It consumes the existing pinned materialization and 507-job plan, reads catalogue data in their checked ordering, and validates their source mappings. It does not regenerate rule occurrences or geometric covers. Every entry map records four factor IDs in the declared order and preserves the original class position. Together with the hash-pinned source plan and payload, these maps reconstruct the original Boolean test without loss of guards.

A subsequent Lean implementation would still need generic factorization lemmas, exact descriptor-to-source correspondences, checked concrete factors and assembly for each planned entry. Counts indicate repeated work that may be shared; compilation cost and proof overhead were not measured.

## Recommendation before the complete batch

A bounded reference-shape reuse pilot is justified before committing the entire 507-job batch. References account for 338,697 of the 357,823 planned entries, about 94.7 percent. Their 337,485 catalogue-indexed shape calls can be expressed using 12,560 normalized shape-only tests. This is a count of distinct predicates, not a runtime speedup estimate. The first comparison should prove the same class 1 statement with the same trusted assumptions and record completed check times for both routes. Adopt the factor route only if that comparison supports it; the existing direct route remains available.

A compatibility/box split alone does not ensure the large shape reduction. If its compatibility factor still includes the catalogue index, the reference compatibility obligations remain indexed by those 337,485 calls. Reusing the 12,560 shapes requires an additional shape-only expression or a lemma reducing each catalogue-dependent match to the normalized direction, slice, orientation and target pattern. The separate 2,329 catalogue guards must still be supplied. Combining the profile's outer and catalogue guards with shape conditions, or moving box length or interval position bounds between factors, preserves the conjunction but changes which individual factor IDs can be reused.

- Script SHA-256: `fd40c213446194b53fee8b0b464337516cf6b712e20cff33ac78db6a57f77eaa`.
- Profile SHA-256: `885f4f4ed241c52979cd5daac7a9c9d72e7d255440652bfaa9c85e933bd8ac44`.
- Original and factored Boolean stream SHA-256: `b2d59493b9277767ca3fbb8de61416bdbf08540942cc771765e82afb5c43184d`.
- All input pins, factor descriptors, multiplicities and entry maps are stored in the JSON profile.
