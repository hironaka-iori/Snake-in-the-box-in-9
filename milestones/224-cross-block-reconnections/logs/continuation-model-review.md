# Round 224 continuation model review

Review date: 15 November 2026. Finding: the contact-free width-33 rerun removes the native round-193 closure dependency from that numerical exclusion. The biconnected refinement changes no actual input geometry. The selected width-44 flow models impose necessary connectivity constraints on only the sixteen recorded contexts. No invalid restriction or inflated coverage claim was found.

## Material and verification limits

Read the complete `prepare_contact_free.py` (18 lines), complete semantic difference from the reviewed original solver to `joint_regions33_free.py` (74 lines), `prepare_biconnected.py` (40 lines), imported `terminal_blocks` helper, `prepare_flow.py` (34 lines), and all 83 lines of `joint_regions44_flow.py`. Compared every contact-free context with the independently reconstructed width-33 input, all 92 refined contexts with the original width-44 input, and all 16 selected flow contexts with both sources. Inspected the saved contact-free native records and execution receipt, including all 53 initial-model hashes.

Only this log was written. Earlier reviews are preserved. No optimizer, compiler or software tests were run. Read-only comparisons of the saved geometry and evidence are independent artifact audits, not solver replays. The flow search was live when inspected; no terminal flow outcome is asserted here.

## Contact-free width-33 exclusion

The preparation script removes every `NO_CROSS_CONTACT` entry and recomputes each context's static status. The generated solver removes the sole contact-candidate selection inequality. Its complete source difference otherwise changes only the input path and scope description. The retained `contact_candidates` arrays are unused metadata and impose no condition.

Every one of the 224 resulting context records equals the original independently reviewed context after precisely those rejection/status changes. All domains, anchors, retained positions, crossings, parity restrictions and window coverage remain unchanged. All 171 static exclusions retain a geometric reason. There is no residual contact-only static exclusion.

The saved `pair33-free.json` contains exactly one entry for each ID 0–223: 171 `STATIC_EXCLUDED` and 53 `INFEASIBLE`. Every static entry matches its geometric rejection lists. Every nonstatic entry corresponds to a pending input and has a terminal native `INFEASIBLE` iteration. All 53 serialized initial-model hashes agree; all cycle-cut lists are empty. The execution receipt reports `ACCEPTED_NATIVE_RESULT`, exit code zero and no stop reason. Its result hash and every input pin agree with the saved files. The recorded solver-loop total is approximately 4.234 seconds, with no witness.

Thus this numerical family exclusion no longer uses the round-193 closure census. It remains a native result for the fixed seed, retained anchors/outside positions, two equal-length replacements of at most 33 edges, endpoint-24 extension and exactly four bit-8 crossings. It has no Lean solver contradiction certificate and is not a global snake bound.

## Biconnected refinement

The original width-44 result has 107 static exclusions, 102 native infeasibility results and 92 unknown contexts. The refined input contains exactly those 92 unresolved IDs. Every retained set, interval, anchor, initial domain, final domain, required parity count, target size, combined crossing count and pending status is identical to the corresponding original context. The added `previous_allowed` lists also equal the original domains.

Across all 184 parts, the refinement removes zero vertices and generates zero rejection reasons. Its source/input/execution pins agree. No native search using the refined solver is needed to establish this lack of change; it supplies no additional exclusion or progress in the remaining count.

The helper's intended deductions concern the anchor-to-anchor chain in the block incidence tree. A simple path cannot enter a branch off that chain and return through its articulation vertex. Within a block whose entry and exit are adjacent, an induced path must use their direct edge. The block parity counts bound the possible internal length. These are appropriate geometric deductions. For the current continuation, however, the identity comparison above avoids depending on that helper's implementation: all solver-used geometry is exactly the independently reviewed original input.

## Selection and flow-input identity

The selected IDs, in execution order, are

`159, 202, 116, 30, 73, 158, 201, 157, 203, 153, 154, 155, 156, 160, 200, 196`.

Independent reconstruction of the ranking gives exactly this list. The available unresolved first-window starts are 0, 1, 2, 3 and 4. Selection first takes the largest total-domain context for each distinct start, with ID breaking ties, then fills to sixteen from the remaining contexts in the same domain-size ranking. Every selected ID belongs to the original unresolved set. There are 76 other unresolved contexts untouched by this run.

For every selected part, all original geometric fields agree exactly with `regions44.json`; retained sets, intervals, combined crossing counts and pending status also agree. The selection-source hash matches `regions44-refined.json`. Consequently the flow continuation depends on neither an effective biconnected reduction nor a contact/short-closure premise.

## Necessity of the added flows

For each replacement separately, the source adds an integer flow $f_{zw}$ for every directed allowed cube edge. The root is that replacement's first anchor $u$, which need not be global vertex 0. The capacities and balances are

\[
0\le f_{zw}\le44x_z,\qquad f_{zw}\le44x_w,
\]

\[
\sum_w(f_{wz}-f_{zw})=
\begin{cases}
-44,&z=u,\\
x_z,&z\ne u.
\end{cases}
\]

These equations are necessary for every actual replacement path $q_0=u,q_1,\ldots,q_{44}$. Assign $f_{q_iq_{i+1}}=44-i$ for $0\le i<44$ and zero to every other directed arc. The first anchor sends 44 units, each other selected vertex receives one net unit, and every unselected vertex has zero flow. All capacities and integer ranges are satisfied. The existing cardinality equation selects exactly 45 vertices, so the total supply and demand match.

The flow also enforces connectivity: a selected component not containing $u$ would have positive total demand and no permitted flow across its boundary. Summing its balances gives a contradiction. Together with the existing degree-one anchors and degree-two selected nonanchors, the selected graph is therefore an anchor-to-anchor path. Retaining the generic cycle handling and final all-pairs witness audit is valid, though disconnected cycle components cannot satisfy the flow constraints.

The rest of the width-44 model is unchanged: both domains may use either face; only the combined replacement crossing count is fixed; all cross-part equalities and adjacencies are prohibited; the original outside positions are retained and 24 is appended. The generated source describes the run as sixteen selected unresolved contexts. It does not claim to cover all 92 remaining contexts or all 301 original contexts.

## Status interpretation

The flow input and executable source were frozen and hashed below. The live output was not frozen as a terminal result during this review. Its native exclusions, if any, must later be combined by context ID with the original outcomes. Unknown or timed-out flow contexts remain unresolved, and all 76 unselected contexts retain their earlier status. `COMPLETE_COVERAGE` would mean the selected input list was visited; exclusion still requires inspecting every individual status.

No new witness, full width-44 exclusion, Lean numerical certificate or global numerical bound follows from this model review.

## Artifact hashes

| Artifact | SHA256 |
|---|---|
| `scripts/prepare_contact_free.py` | `2f6e59dbbafceaf7654d55576d12222f5eb7fdea09f220efcf51a7868d5a2bbf` |
| `scripts/joint_regions33_free.py` | `45a37f5f65a2cba9de5c0bcc87f5d2a9d83631b11e31caf2d3758d99c31eb3f9` |
| `data/regions33-free.json` | `95c9e269d80cb4586de10c702a726e5e6c373efbfd9b423a28699c5e7cb0cd31` |
| `data/pair33-free.json` | `f6dc740343f3a56a838d556b63ec3d5a990bcc1fbd23900940c75e162011383f` |
| `data/pair33-free-execution.json` | `599d27ac82a12f5efc2b73939b9628d7fb5290183c82d8dc264dc5777109c802` |
| `scripts/prepare_biconnected.py` | `9181e720f6fed41f1356b3b6d0594601f8371ce4a0ed0971abec136144e3c9f2` |
| `data/regions44-refined.json` | `238fcffe86740fa4885cc70f267eb2adb31e2612ae4cab7d3d75f4b94bbdd152` |
| `scripts/prepare_flow.py` | `ce9795ea6f3f0a8e9f731bce21738e36f097e3efda8b5b55cbceda741db952b4` |
| `scripts/joint_regions44_flow.py` | `9b7c7e4ef3b63a1932fe8743182054ef8e19ed65aa420adc40e544fa7901adb1` |
| `data/regions44-flow.json` | `e00ea0fc5dd34bb66591bd28cae918db6c14a275e2212ccef9545dc79253e156` |
