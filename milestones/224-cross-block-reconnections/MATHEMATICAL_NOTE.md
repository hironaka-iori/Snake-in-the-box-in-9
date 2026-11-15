# Round 224: simultaneous replacements in two regions

The goal remains active and the investigation remains constructive. The working hypothesis is that simultaneous, mutually interfering changes can escape the blocked 191-edge bank and yield 192 edges. No longer snake was found in this round. The useful result is a checked conditional interaction theorem and complete computational exclusion of a specified two-short-block family. The maintained interval is unchanged at 191 to 233.

## Necessary interaction

Let a family of equal-length induced paths be closed under every length-preserving replacement of one block of at most K edges. Suppose none of its members admits an endpoint extension. Let P belong to that family and let Q be an induced path agreeing with P outside two ordered, disjoint open index intervals A=(a,b) and B=(c,d), where b<=c and each block has at most K edges. If Q admits extension, then its new A interior must equal or be adjacent to an original B interior vertex; the corresponding new B to old A contact is also necessary.

If the first contact were absent, using Q on A and P elsewhere would already form an induced path. Pairs outside A inherit P, pairs inside A inherit Q, and the only remaining old/new pairs not controlled by Q are new A against old B. Their separation is the hypothesis. The first replacement can therefore be performed alone, followed by the second. Closure would keep Q inside the blocked family, a contradiction. Exchanging the order gives the other contact.

TwoBlocks224 constructs this actual indexed intermediate path. TwoBlockEscape224 proves both contact conclusions under the explicit closure and blocked-extension premises. Both modules passed Lean, reporting only standard axioms. The latter's first attempt had two incomplete simplification steps; the failed source/log remain preserved, and the repaired accepted source is separate. No admitted statement is accepted.

Contact includes equality. Old vertices can move from one block into the other, so the conditions use original positional interiors rather than only vertices globally omitted from the final snake. Shared anchors are allowed, overlapping interiors are not. The application with K=33 uses the native round-193 bank-closure census. No closure through 44 edges is assumed. No claim of historical novelty is made; related simultaneous-dependency ideas are present in earlier project work.

## Endpoint24 and complete window coverage

Use the normalized bank123 seed from round223, ending at88. Its other selected neighbours of24 are p7=28 and p143=56. Both must disappear when24 is appended. Two equal-length replacements of blocks of at most33 edges must place these indices in separate open interiors. Every such choice can be padded with unchanged vertices into one of

\[
[a,a+33],\ [c,c+33],\qquad 0\le a\le6,\quad111\le c\le142.
\]

There are224 maximal contexts. Padding preserves all shorter successful replacements, the four anchors, and the unchanged outside positions. The first block contains no bit8 crossing and the second exactly one, leaving three crossings outside. For a four-crossing final snake, the first replacement must stay in the lower face and the second must cross once. The second block's anchors are in opposite faces, so it cannot contribute zero crossings.

The analogous44-edge family has301 maximal contexts, with c ranging from100 to142. Its first block can cross the original crossing at46. Its models correctly constrain only the combined number of replacement crossings to four minus the unchanged outside crossings. No individual crossing allocation or first-face restriction is imposed in this broader family.

## Domains, joint path selection and outcomes

For each replacement, exclude retained vertices and neighbours of retained vertices other than its own anchors. Also exclude24 and all its neighbours; restore the prescribed anchors. Repeatedly delete non-anchor vertices with fewer than two available neighbours. Restrict to the component containing the first anchor. Disconnection from the other anchor, insufficient vertices and insufficient parity counts each exclude a region.

The joint selected-vertex model requires each anchor to have one selected neighbour and every selected interior vertex to have two. Each replacement has exactly its required number of vertices and parity counts. Every equality or cube adjacency between the two replacement paths is forbidden. These far-separated index intervals have no intended inter-path edge. A disconnected degree solution can contain cycles; any observed cycle is cut. A candidate is accepted only after complete reconstruction of the 193-vertex path, all unordered adjacency pairs, and exactly four crossings. No degree-feasible assignment or dynamic cycle cut occurred in the recorded runs.

| Query | Contexts | Geometric exclusions | Native infeasible | Unresolved |
|---|---:|---:|---:|---:|
|33-edge blocks, interaction restriction|224|171|53|0|
|33-edge blocks, no interaction restriction|224|171|53|0|
|44-edge blocks, initial run|301|107|102|92|
|16 selected open44 cases with connectivity flow|16|0|0|16|

The two33-edge runs took4.453 and4.234 seconds respectively. The second removes every contact constraint and contact-based rejection. Therefore the final numerical33-edge exclusion does not depend on the round193 closure premise. It remains a native finite result; its solver contradictions have no Lean replay. A successful192-edge construction in this fixed endpoint24, four-crossing, two-block arrangement must have at least one block longer than33 edges, if it exists.

The44-edge initial run completed all301 contexts in77.828 seconds, using a0.5-second limit for each solver call. All92 unknown rows remain open. The term COMPLETE_COVERAGE means every requested context was visited, not every context was excluded.

## Connectivity refinement and its limitation

Applying the existing anchor-to-anchor biconnected-block reduction to all92 open contexts removed zero vertices and rejected zero cases. No unchanged numerical retry was run. This observation rules out that reduction as an immediate improvement for these domains.

Sixteen contexts were selected by distinct first-window starts and larger combined allowed domains. The added single-source flow supplies44 units at the first anchor and demands one net unit at every other selected vertex. Directed flows are between0 and44 and require both endpoint vertices to be selected. Every actual44-edge path satisfies these conditions by sending44,43,...,1 along its consecutive forward edges. Thus they preserve every valid replacement and require connectivity. All16 selected cases remained UNKNOWN, with six seconds allowed per query,98.438 seconds total. The remaining76 open contexts were untouched. The combined unresolved set still contains92 distinct context IDs.

## Evidence, scope and continuation

Independent reviews reconstructed all224 short contexts,448 domains and5815 peeling steps, and all301 expanded contexts,602 domains and5713 peeling steps. They also checked the contact-free model, selected flow cases, and equality of the unreduced and refined domains. These are exact finite geometry/source audits, not solver contradiction certificates. Two Lean modules provide two checked public results, with the numerical closure census remaining a premise only in the general theorem's bank application.

All raw serialized models remain locally in data/. Their exact bytes are also stored in solver-models.zip, containing316 models; model-archive.json records the hashes. Extracting that archive into data/ restores the recorded paths. Result files retain all native statuses and any cycle cuts. Search summaries merge distinct context IDs and never convert a timeout into an exclusion.

No global optimum or improvement above191 is established. The earlier lower-dimensional example already demonstrates that strong local barriers can occur at a suboptimal snake, so these exclusions do not support an optimality claim for191. The current hypothesis survives beyond the excluded two-short-block arrangement.

Next, locate the smallest unresolved widths between34 and43, and construct candidate replacement paths before comparing their compatibility. Enumerating one connected replacement and solving the other in its remaining allowed graph can avoid the disconnected degree relaxation. Any finite enumeration must retain its uncovered states. Do not repeat unchanged44-edge degree or flow timeouts. The fixed-parent one-crossing result from222 and the frozen parent-history searches remain unchanged. Full manuscript review remains scheduled for230.

No software tests were created or run. Both papers are revised in place, preserving the three authors and hyperlink settings; compilation and final source-review records accompany publication.

For a width34 continuation, use the combined crossing constraint from the expanded model. In particular, the second interval [130,164] contains both old crossing edges130 and163, so the33-edge allocation of zero crossings in the first replacement and one in the second cannot be carried over. Candidate paths may redistribute the two available crossings between the replacements.

The publication fetch observed contributor revision e3c7bfcd37d4a0c54a348533fa696addefebbbd5, with further stageB/C work-in-progress snapshots toward231. These changes were inspected without merging or rebuilding. No completed new bound is asserted here; the maintained233 result retains its independent-full-rebuild qualification.
