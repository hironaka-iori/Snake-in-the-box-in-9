# Round 213 geometry and concrete support bridge review

Scope: independent source inspection and bounded extraction recomputation on 15 November 2026. No compiler, solver, search, or traversal was run. Compilation receipts remain the parent's separate evidence. No source-level mathematical defect was found in the inspected version.

## Concrete data and complete pair coverage

The 99 source vertices equal the saved Q8 lower-dimensional input. The retained coordinates are exactly 0 and 6; their two-bit projections equal every saved model z entry. All 99 group identifiers equal the round212 model and extraction record. They cover groups 0 through 77. First and second representative tables equal the first and last occurrence of every group. Both chosen/outside lists and all 22 partner lists agree exactly with the round212 support file and case22 census. The even family has 30 chosen and 9 outside variables; the odd family has 26 chosen and 13 outside variables. Each pair of lists partitions all 39 group identifiers of its parity.

Reconstructed requiredPairs in the exact Lean order. The even family contains 435 chosen pairs, 36 outside pairs, and 189 nonpartner cross pairs, totaling 660. The odd family contains 325, 78, and 228, totaling 631. The combined list has 1291 distinct ordered pairs. This numerical cardinality is an independently recomputed extraction fact; this review does not claim a standalone checked Lean length-1291 theorem.

Recomputed the current makeCertificate algorithm for all 1291 pairs. Every result satisfies both index bounds, group membership, distinct groups, equal identifier parity, and nonopposite base corners. The algorithm changes the first representative 84 times and the second 104 times. Its tuples differ from 19 earlier first-found tuples in concrete-extraction.json. This is harmless: the current coverage identity and validity proofs concern the current algorithm. The old extraction tuples must not be advertised as byte-identical to the final proof data.

The final assembly imports the six accepted five-chunk modules _00 through _05 and twelve single-statement modules for chunks30 through40 and the tail. The old _06 through _08 sources remain historical source attempts and are not imported. Independently inspected their statements as well. Imported chunk statements cover exactly offsets 0,32,...,1280. Forty chunks have32 pairs, the last has11, and drop1312 is empty. All41 valid_step compositions appear once in descending order and conclude the full all predicate. The take/drop argument includes the tail and has no uncovered segment. ConcreteCoverage213 proves exact map coverage through certificate_pair, independent of the numeric cardinality.

## Geometry and the resulting interface

IndexedCubePath includes common coordinate width, consecutive distance1, and nonconsecutive distance at least2. The general proof derives injectivity. Equal-parity distinct group identifiers cannot occur at adjacent indices under the stated same-or-next group rule. If their free words agree, their remaining two-coordinate distance is at least2, forcing opposite corners. This supports shared_word_conflict, singleton membership of a group sharing a word, and exclusion of three distinct equal-parity groups sharing one word. No unproved global monotonicity or actual free-word parity identification is used in these arguments.

For the concrete source, the consecutive group rule is obtained from literal data. Assuming the reconstructed 99 indexed vertices form an induced Q8 path, required_words_ne derives every one of the required inequalities. The two public support_conditions theorems then derive (1) distinct assigned words on the chosen list, (2) distinct assigned words on the outside list, and (3) completeness of the listed partners for any equality between those lists. These are the geometric hypotheses previously supplied to the generic round212 support argument. The helper requires only the stated induced-path premise; it does not assume the desired pair inequalities or partner completeness.

The decoder word reads only the low six bits of a raw Nat. The implication used is sound without decoder injectivity: unequal decoded words imply unequal raw Nats by congrArg applied to an assumed raw equality. However, equal decoded words do not imply equal raw Nats without a range premise; values differing by64 decode identically. No raw range, alphabet parity, or pool membership theorem is supplied here.

## Remaining boundaries

The public premise is the induced-path property of a fixed reconstructed Q8 path with this source's two retained coordinates and literal groups. It does not establish that all relevant snakes normalize to this model. Connecting the native assignment to this path still needs the six free coordinates' placement, raw-word range and parity-alphabet membership, domain fitting, binary-table meaning, nogoods/symmetry scope, and eventual complete search coverage. The generic spare-budget theorem is not instantiated in ConcreteSupport213 itself. Native masks and committed traversal records remain outside this bridge. No global Q9 bound, search exhaustion, or completed normalization follows from these source files alone.

The source headers saying prepared/uncompiled describe authorship history; acceptance must be read from the parent's current receipts. This report does not replace that acceptance audit. Final small compiler repairs after the hashes below require a refreshed source comparison.

## SHA-256 snapshot

- `213-interval-geometry/lean/IntervalGeometry213.lean`: `762fe2903835fc78028b0c5e23c6019227d993896f72b161b7a2ea9ab8e59cdf`
- `213-interval-geometry/lean/IndexedCriterion206.lean`: `64d1272dfe373326429a61883343a2644a3a54fef698770bfa27572f8ac5e256`
- `213-interval-geometry/lean/Square209.lean`: `3cf0de2d62f26ce2f3322e538c46457543f089553b70e399c714766d4a92c7bd`
- `213-interval-geometry/lean/ConcreteData213.lean`: `907f02481b99bc5b53aa81a63dc3e6d554229c4034dc21a5188737b2997affa6`
- `213-interval-geometry/lean/ConcreteRelations213.lean`: `34a2f14155b90f993f96dc7e42f35ac44f9b759cc77f130acd6214a65f5eb00e`
- `213-interval-geometry/lean/ConcreteCoverage213.lean`: `c884f65a73d5c76b7d8c19aed8a436d1182563fb4b1e61dfe824bcdefcd53914`
- `213-interval-geometry/lean/ConcreteGeometry213.lean`: `9eab8394b4dc7b68c8d657aa0fee0ae3065dfe805fcb8d7bda0958c56d68a8d6`
- `213-interval-geometry/lean/ConcreteSupport213.lean`: `f9ea49968b4cb6d014fdbc700f74ba8c0692bbf68ab29e46e31f3cf5239ecb2f`
- `213-interval-geometry/lean/ConcreteChunk213_00.lean`: `2bd39782edc14db641734eaadc85b5e67335791156cb1e37fab5418285ddd388`
- `213-interval-geometry/lean/ConcreteChunk213_01.lean`: `c16a74699b3ab3242a95a56d4bcac672fd23fd28ae957b8e5113762fad02886a`
- `213-interval-geometry/lean/ConcreteChunk213_02.lean`: `7f09a87a1e7ad03fc1267e7615ca36d33a1ca2d8db3d4bcd9573972a0442da0a`
- `213-interval-geometry/lean/ConcreteChunk213_03.lean`: `b978a1f6fef9df9b9469156e67fc48f1f0c4d1b238814b364e3f6f2863119576`
- `213-interval-geometry/lean/ConcreteChunk213_04.lean`: `fc20d91f3e89550303ba9fc3846981d366a526035f978af88f09e9a63b0cdca2`
- `213-interval-geometry/lean/ConcreteChunk213_05.lean`: `a8199c6916769c8dfd6fc1d2d0672432eb90c533e664a35a75b98484be220f56`
- `213-interval-geometry/lean/ConcreteChunk213_06.lean`: `cf94e37a39643a3440a7ef04173329e752ec007cfe2c8b8b64eec32eb061647b`
- `213-interval-geometry/lean/ConcreteChunk213_07.lean`: `32aea2f314ce492f36e0bb47953799f5512696c6713dcb3d783c5123cbf5d8d1`
- `213-interval-geometry/lean/ConcreteChunk213_08.lean`: `fec7005ab0938eeabbbd0889f965265d643887018fa78825a0669d9407aa7f0d`
- `213-interval-geometry/lean/ConcretePart213_chunk_30.lean`: `4c2639f0304e0641a3f9ac8008df5f556db8a7a7edc2dd6739a8903787e34362`
- `213-interval-geometry/lean/ConcretePart213_chunk_31.lean`: `cdf3c76f5c5c1e336590050e1ac8d268f9a0187d7881a0b5cebb6c92ee73e03c`
- `213-interval-geometry/lean/ConcretePart213_chunk_32.lean`: `1609ec4aaf6ca07540ab1d59801bd4ca736f739e92165689450daca31e464c37`
- `213-interval-geometry/lean/ConcretePart213_chunk_33.lean`: `195692154fcedba6706b94d8de750afefc7eb70950a5c85eab6f04c201daa842`
- `213-interval-geometry/lean/ConcretePart213_chunk_34.lean`: `af26f63894796b90ac2f388f683bde63159c700513e6c295b00a11a3f1f68f3a`
- `213-interval-geometry/lean/ConcretePart213_chunk_35.lean`: `5b68b5f296cd91502f9a41b82ab88afde14d761207da24c59fdc507d2d2aa7e7`
- `213-interval-geometry/lean/ConcretePart213_chunk_36.lean`: `713a6c7f81633009ce71fb3736046db1e25fea4eb36936fb4f7121b9a04f7ba3`
- `213-interval-geometry/lean/ConcretePart213_chunk_37.lean`: `a8d186c5335fd6bdf442989204f45eb13968804d5baf80fa1d5354e1dc886479`
- `213-interval-geometry/lean/ConcretePart213_chunk_38.lean`: `2f5eb73031b938e898339ba58d383b434df18feb109f6891705bb7c158c8da6c`
- `213-interval-geometry/lean/ConcretePart213_chunk_39.lean`: `0bba2076c2ac75d4c83654bdcde310a0f4a5e608fe0b0675823624175faf65c7`
- `213-interval-geometry/lean/ConcretePart213_chunk_40.lean`: `1d8a90e926475ea5e902eefa8f6cee5b4c3cd20e775b2d61b88e62de847e18b0`
- `213-interval-geometry/lean/ConcretePart213_tail.lean`: `49703e38ae3929b79d769a329fb654898a94d8dd91966d723854fe3dd934a628`
- `213-interval-geometry/data/concrete-extraction.json`: `d94ac6486ca81cf7f74a6d52640c17737b28cb4042a48e299061067e39134e62`
- `212-spare-support/data/case-22/model.json`: `1a4d81c600d104347a501cfc9bf82db91a3aa04a6ebfd3ea20fcb1ca283aa95b`
- `212-spare-support/data/case-22/support-constraints.json`: `0362c97affd2b4b19405f2a05747327a703b55459b6f1cb3d7bc455c72bce040`
- `212-spare-support/data/lower-dimensional-input.json`: `d62c92cc97eae196b21aeefe2111adfb03cc3121b9b62ba7e3e2c6ee6920c20d`
- `212-spare-support/data/square-capacity.json`: `400753eef4c691333e5e03d87239d93fe63ea9f7fc870ac1d742a01afb21bb10`
