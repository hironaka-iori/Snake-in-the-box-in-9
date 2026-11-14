# Full-paper review: construction, histories, witnesses and references

Reviewed source: milestones/210-paper-review/data/research-before.tex.

SHA-256: 4e902994337c8ef30d3d308e6915d7d43a80cb357570926fa23ab5fb42b8f73a.

Coverage: every line **6301–10200**, through the end of the document. Lines 6270–6300 were additionally read to recover the beginning of the numerical-model discussion. Reads used bounded numbered chunks; the truncated output around the older construction experiments was repaired by rereading lines 9048–9158. No paper, proof source or accepted record was changed. No search, compiler, solver or software test was run. Witness claims were reviewed as statements and against their stated verification scope; this review did not recompute their vertex pairs.

## Assessment and coverage

No algebraic or geometric defect was found in the reviewed principal written arguments. The useful changes concern organization, references and the distinction between finite calculations and their remaining geometric interpretation.

| Lines | Coverage and assessment |
|---|---|
| 6301–6310, plus 6270–6300 | Competing numerical extrapolation. The 195 model agrees with the same first eight terms; neither recurrence supplies evidence for later values of the extremal function. |
| 6312–6420 | Prefix exclusion, endpoint blocking, cycle deletion and one-crossing joining. Edge and vertex counts agree. Universal blocking is separated from blocking the recorded bank. |
| 6422–6688 | Coordinate cuts, three-component joins, dimensional examples and fixed-middle replacements. A disconnected face is not bounded by a single-snake maximum. Fixed-endpoint parity and contiguous-block limitations are correct. |
| 6690–7155 | Component, attachment and colour balance; moving endpoints; square substitutions; repeated-move closure. Written deductions and checked finite counting premises are distinguished. |
| 7158–7827 | Region pruning, lower-dimensional obstruction, quotient lifts, involution classification, clique/orbit restrictions, relative placements and trimming. General isometries, involutions and fixed-parent families are distinguished. |
| 7830–8007 | Two-parent identities, overlap, one-deletion criterion and the 196-edge cases. Positive parent lengths, the entire induced final graph, singleton final paths and addition counts are handled explicitly. |
| 8010–8431 | Controlled reflections, larger blocks and arbitrary slice isometries. Selected nonedges are retained. The maps need not be automorphisms of the entire cube or of the original selected set. |
| 8433–8846 | History classification, literal slice certificates, native four-/five-coordinate rigidity and resumable six-coordinate coverage. Target and orbit counts have consistent stabilizer accounting. Conclusions retain fixed length, index matching and source restrictions. |
| 8849–8920 | Square-base capacity, saturation and round-209 status. Equal-word conflicts prove the capacity bound; saturation forces nine shared words without prescribing their partners. |
| 8922–9450 | All older construction experiments and local diagnostics. Timeouts remain unresolved. Fixed-region exact-length exclusions are distinguished from longer-path exclusions. Disconnected constructions are not counted as snakes. |
| 9451–9613 | Every displayed transition string, blocker list, return witness and verification procedure. The procedure distinguishes a witness check from a global upper-bound proof. Numerical values were not rerun. |
| 9615–9763 | All 55 history-share rows and remaining sharp/odd witnesses. Charged positions and count conditions are specified; global concatenation is not asserted. |
| 9765–10200 | Entire bibliography. The missing round-201 reference is identified below. External metadata and links were not refreshed. |

## Anchored corrections

### 1. Add the missing round-201 reference

Lines 7830–8007 contain substantial results, including the two-parent identities and the one-addition restriction. The bibliography includes records 200 and 202 but contains no entry for 201. The subsection also ends without citing its underlying record.

Add \cite{research201} to the scope paragraph at 7995–8007 and a reference to milestones/201-crossing-deletion, with title “Fundamental restrictions on two-parent constructions.”

Its README confirms six accepted Lean modules with 24 dependency reports and identifies the geometric count interpretation, one-deletion classification and saturated-overlap conclusion as written proofs. Retain the distinction at 7996–8006; do not relabel the whole subsection as Lean-checked.

### 2. Date historical numerical restrictions

Lines 6867–6877 call the eight-omission restriction “current” inside the round-191 account. Lines 7206–7209 call the single-replacement cutoff “current.” Their mathematical restrictions remain valid, but the time reference is unclear.

Replace the opening of 6867–6869 with:

> In round 191, the cases \(r=6\) and \(r=7\) were reported infeasible in 13.203 and 30.344 seconds, respectively, before any additional cycle exclusion. The resulting computational restriction for this particular 95-edge path was

Replace the heading at 7206 with “The 44-edge single-replacement cutoff.” Replace “are now computationally excluded” at 7208–7209 with “were computationally excluded in round 194.” Preserve the distinction at 7218–7220 between one replacement followed by growth and repeated-move closure.

### 3. Convert superseded next-step prose into historical connections

Several passages propose work that the following subsection already performs. No mathematical statement needs removal.

- **6554–6559:** replace “A useful first restricted target is” with “The next restricted target was”.
- **7151–7154:** replace “The next construction search can impose” with “The subsequent construction search imposed”; round 194 supplies the result.
- **7362–7365:** replace “The next attempt uses” with “The round-196 continuation used”.
- **7542–7546:** describe the proposed subdivision as a possibility at that cutoff, rather than a current research instruction.
- **8429–8431:** replace with “The following section records partial certification of this comparison. Further construction requires different parents or changes outside the covered slice-isometry family.” Round 205 has already completed literal finite-model coverage, although the geometric links remain pending.

### 4. Clarify the round-205 verification boundary

Lines 8625–8634 are accurate. The record confirms 254 explicit models and 625 data, elimination and cover modules. The adjacent prose should distinguish literal coverage from the geometric result.

Suggested replacement for 8625:

> Lean checks complete coverage of all 254 explicit finite models in 625 data, elimination and cover modules. The result quantifies over assignments to the stored domains and compatibility tables.

Retain all three outstanding connections at 8627–8633. The whole round has 659 accepted modules and 1543 reports; 625 counts the coverage batch. The inspected round-205 README confirms this distinction.

### 5. State the comparison behind “changed histories”

The restrictions at 8697–8703 and 8762–8767 are already qualified. A direct sentence after 8764 would clarify the strongest general source-specific result:

> This means that no target in a different cube-isometry class can agree with this source at every index in any three selected coordinates.

Retain “same length” and “fixed index matching.” Do not shorten this to a claim that every new 98-edge snake changes six coordinates. Round 208 concerns only retained pair \((1,4)\), so it does not raise the general six-history requirement to seven.

The round-207 completion record confirms that all 56 five-coordinate models exhaust natively. Two Lean modules check the general lexicographic reduction and the concrete reversal obstruction; they do not certify the complete finite exclusion.

### 6. Replace the unexplained “clique domain” phrase

At 8900, “selected clique domain” introduces unnecessary graph terminology. The preceding paragraph already identifies the 32 relevant variables.

Replace 8899–8905 with:

> The same saturation restricts every unfinished branch. Each even word must remain available to at least one of the 32 selected interval variables. If exactly one of their domains contains that word, that variable is forced to take it. A remaining singleton variable may use only words still available to its opposite-corner partners. Each deduction preserves every completion of the original model.

This does not prescribe partners or assert that capacity alone suffices for construction.

### 7. Tie the round-209 status to its cutoff

Lines 8916–8920 agree with the round-209 completion record:

- Retained pairs \((0,4),(3,4),(0,5)\) are open, with respectively 8, 3 and 7 unfinished regions.
- Exactly one of 28 pairs, \((1,4)\), is exhausted. Twenty-seven remain unresolved; the other 24 have only their initial limited searches.
- Three Lean modules have thirteen reports. There is no new global bound or witness.

For the round-210 paper, begin 8916 with “At the round-209 cutoff” and place any subsequently verified round-210 status separately. Preserve the historical statement under its own citation.

### 8. Clarify historical bibliography status

Entries 9986–10009 describe partial historical certificate stages. Where later work changes status, replace “remain unfinished” or “remain pending” by “were unfinished at this archived cutoff.” Preserve the historical meaning of each reference.

Several references use moving tree/main links. Immutable revision links are preferable for a fixed release when the parent has the verified publication revision. This review did not resolve or replace those links.

### 9. Repair run-together prose

- 7247: “Round194” and “shorter189-edge” → “Round 194” and “shorter 189-edge”.
- 7337: “nonadjacent42-edge” → “nonadjacent 42-edge”.
- 7341: “involutions:20” → “involutions: 20”.
- 7354: “original96-vertex” → “original 96-vertex”.
- 7376: “quotient,16” → “quotient, 16”.
- 10109: “record195” and “November2026” → “record 195” and “November 2026”.

## Mathematical boundaries to preserve

- The two-parent identity counts additions outside the original layered union and each new within-face edge once. The hypothesis concerns the entire induced final graph, not merely a chosen traversal.
- The \(196\)-edge one-addition case has \(D=2\), \(k=4\), and \(b=e=H=0\). The added vertex is a global endpoint. The \(C=5\) attachment argument and sharper deletion-index deduction retain their written-proof scope.
- Controlled maps act on entire ordered embeddings while potentially changing other ambient pair relations. The explicit nonisometric images correctly demonstrate this distinction.
- The exact two-coordinate count permits unrestricted initial word and endpoints. Its orbit count uses only block-coordinate isometries; larger cube symmetries may identify further targets.
- The three-coordinate extension uses four antipodal labels and parity preservation. The four-coordinate counterexample correctly identifies a limit of that argument.
- Square-base capacity is exact only for same-parity equal-word conflicts. Saturation does not satisfy opposite-parity constraints automatically.
- The numerical conjecture 196 remains an extrapolation. Preserve the competing 195 model, the next-length equivalence and the separate construction/exclusion requirements.
- Short or disconnected witnesses establish only their stated local facts. Repeated recovery of the saved bank does not establish the extremal value.

## Additional records read

- milestones/201-crossing-deletion/README.md.
- milestones/205-slice-certification/README.md and the identifying/completion portion of data/completion.json.
- milestones/207-five-history/README.md and the identifying, proof and model-summary portion of data/completion.json.
- milestones/209-slice-capacity/README.md, complete MATHEMATICAL_NOTE.md and complete data/completion.json.

These reads corroborate the manuscript's evidence boundaries. They are not a rebuild of the accepted proof or native enumeration records.
