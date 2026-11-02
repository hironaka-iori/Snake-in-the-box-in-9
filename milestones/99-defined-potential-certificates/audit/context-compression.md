# Exact context reuse calculation

The 791 contexts reduce to **582 distinct tuples for the completed profile**, **564 for conditional floor18**, and **582 jointly**. This would save 209 combined context checks if the required Lean equality and transport statements are established. The numerical analysis took 1.360 seconds; no solver or compiler was invoked.

A tuple consists of the exact acceptance-class root, the ordered source potential block of 7,776 values, the ordered target potential block of 7,776 values, and the weight values on **all 46,656 count codes**, including rejected codes. Potential arrays use the existing 206 blocks and raw state numbering. Each profile is classified separately. The joint classification pairs its two profile-group IDs.

SHA-256 hashes index the candidate groups. Every reused context was then checked by direct equality of both potential blocks and the complete weight array against its representative, so the reported reuse does not rely only on hash equality. All source-file hashes from the independent potential audit were verified before reuse. The reconstructed accepted-weight hashes equal that audit's hashes for both profiles.

| Profile | Distinct potential blocks | Distinct context tuples | Redundant context checks |
| --- | ---: | ---: | ---: |
| Completed | 177 of 206 | 582 | 209 |
| Conditional floor18 | 171 of 206 | 564 | 227 |
| Both profiles jointly | — | 582 | 209 |

The following representatives span low, median, and high accepted-code counts among the distinct groups. The median is the middle group after sorting by accepted-code count, with group ID breaking ties. The critical code attains the stated minimum slack.

| Profile | Size selection | Direction ID | History ID | Accepted codes | Minimum slack | Critical count code |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Completed | Low | 223 | 0 | 3,165 | 0 | 6045 |
| Completed | Median | 183 | 52 | 6,512 | 0 | 6036 |
| Completed | High | 66 | 0 | 8,389 | 0 | 6031 |
| Conditional floor18 | Low | 223 | 0 | 3,165 | 0 | 6045 |
| Conditional floor18 | Median | 183 | 42 | 6,512 | 0 | 6042 |
| Conditional floor18 | High | 66 | 0 | 8,389 | 0 | 6036 |

`data/context-compression.json` contains every group, representative, member context, source/target block hash, full weight hash, critical count code, and joint-group assignment. `scripts/context_compression.py` reproduces the classification. The previous audit and its numerical receipt were preserved; only explicitly requested prose spacing was corrected in its Markdown report.

The required reuse theorem is elementary: contexts with equal acceptance roots, equal source and target potential blocks, and pointwise equal weight functions have identical edge slack for every count code. The numerical equality results still require a checked Lean representation and proof. No reduction of local refutation premises or improvement to a global snake bound follows from this grouping alone.
