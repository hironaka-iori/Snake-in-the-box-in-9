# Round 216: joint pair support and two-step geometry

The hypothesis was that simultaneous compatibility among three successive free-word groups supplies restrictions missed by independent support. The saved analysis finds additional forbidden pairs, and the new native engine retains them during branching. No new parent, longer snake, complete coordinate-case exclusion or global numerical bound is obtained.

## Mathematical argument

Two consecutive cube edges flip either the same coordinate twice or two different coordinates. Their outer words therefore have Hamming distance0 or2. For distinct decoded outer words the distance is2. Lean checks the equal-length Hamming triangle inequality, the two-step conclusions and their connection to the literal reconstructed path. The actual path supplies each consecutive free-word edge. No zero normalization or raw integer bound is needed for the decoded-distance statement. Raw natural-number inequality cannot substitute for distinct decoded words.

For three current domains A,B,C and necessary binary relations R_AB,R_BC,R_AC, retain an allowed pair(a,b) only when there is some c in C with both(b,c) in R_BC and(a,c) in R_AC. Apply the analogous restriction to the other two relations. The actual third value of a fitting complete assignment witnesses all three supports. Hence each restriction preserves the same assignment; repetition follows by induction. Any later assignment in smaller domains also lies in the root domains, so the restriction remains valid for every descendant.

Joint216 checks pair preservation, preservation under subdomain containment, and contradiction from absent triple support. PathJoint216 composes this with the actual successive free edges; domain fitting and a necessary outer relation remain explicit. LiteralJoint216 checks a concrete support distinction. Four new modules pass with eleven dependency reports using only propext, Classical.choice and Quot.sound. The first triangle-inequality attempt failed because simplification discarded useful context; a goal-only simplification repairs it. The failed attempt is retained and is not part of the accepted proof evidence.

## Why the distinction matters

In frozen region20 at groups(6,7,8), the outer words5 and6 are allowed and have distance2. Their only common six-bit neighbours are4 and7. The analyzed middle domain is

\[
\{19,21,22,25,26,28,35,37,38,41,42,44,55,59,61,62\}.
\]

It excludes both common neighbours. Yet5 has available neighbours21,37, and6 has22,38. Both values survive independent support, while their pair has no common middle support. The literal finite checks establish the common-neighbour list and independent-versus-joint support distinction. They do not independently certify the entire saved CSP or its extraction.

The five saved regions reach fixed points under binary and four-family Hall propagation. Adding the static outer distance0-or2 condition deletes no value. Joint projection excludes940 pair occurrences:896 outer occurrences and44 consecutive ones. Installing one projection pass and repeating those baseline rules still removes no individual value. Counts are by region/triple and may repeat a pair. This comparison omits partner-capacity, lexicographic and higher-order nogood rules. It supplies stricter explicit pair information, without a demonstrated speed advantage or a reproduced full native fixed point.

## Native use and proof boundary

The new engine first runs ordinary root propagation. It then computes all three support tables for each consecutive triple before modifying that triple's relations, maintaining both relation orientations. Missing relations mean universal relations. Only pairs within the current root domains are deleted. Up to four sweeps are interleaved with ordinary propagation. Relation tables then remain fixed for the entire descendant search. Every submitted job starts a fresh process with the original input relations; forgetting inferred restrictions between jobs can cause extra work without losing a valid completion.

The source review found no blocking defect under the existing model assumptions. The new operation preserves solutions of arbitrary binary relations; its correctness does not depend on the variable numbers actually being consecutive snake groups. Applying it to snakes still requires every intended path to satisfy the supplied tables, family restrictions, symmetry and other constraints. The native bitmask/list correspondence, arbitrary-input normalization and complete C traversal remain separate proof obligations. Neither this source review nor the generic Lean result certifies a full native exclusion.

## Saved search and evidence structure

The original round 215 state and its740 receipts remain in their published milestone. The new version2 ledger copies only four pinned model files and a source-state snapshot, preserves all five unfinished domain vectors and next_id, and stores explicit hashes of the predecessor state, audit and publication manifest. Its committed_jobs,nodes,seconds and receipts describe only work performed in round 216. Cumulative quantities in search-summary.json add the history_parent baseline. This is a new local ledger contract, not a silent reinterpretation of older files.

The continuation accepts 400 local jobs, with outcomes {'LIMIT': 47, 'EXHAUSTED': 353}, 2,044,830 new nodes and 236.214 reported solver seconds. It records 3,706,395 repeated pair removals over 1,090 root projection sweeps. These counts do not establish a controlled speed gain.

The audited final state remains OPEN with 9 regions. Cumulative totals are 1140 jobs, 6,496,107 nodes and 658.343 reported solver seconds. State SHA-256: 4599f3f699d81ee7e14295d537715d621db8a9bb5584ea8a9121d4f2ed592480. All predecessor state files remain unchanged. Only retained[1,4] is exhausted among 28 six-coordinate choices; 27 remain unresolved.

## Next step and goal state

Continue the retained(0,6) search with the current joint engine using longer bounded jobs, initially 30 seconds, to spend less time reloading and journaling small subtrees. Preserve the same resource limits and exact saved-frontier accounting. Assess completed cases or an actual new parent before adding further propagation. Pair information is demonstrably stricter in the saved comparison, but a controlled speed gain remains unproved. For any further mathematical extension, require an explicit relation or geometric witness beyond the existing root projections.

The recorded interval remains191<=a(9)<=233. Contributor revision b0521e1d and the saved final audit b65d30ca are unchanged; the original233 theorem is unconditional, while independent full rebuilding remains pending. The196 conjecture remains unresolved.

Goal ACTIVE. Continue across rounds under the user's own-work pause condition; contributor work alone cannot trigger a pause. No email was sent because no sending connector is available. Both existing editor manuscripts compile and exactly match their paper mirrors. All three authors and local hyperlink settings are preserved. Last full-paper review210; next scheduled220.
