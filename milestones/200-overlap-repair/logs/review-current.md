# Round 200 review: current upper-bound material

Reviewed scope: every line 1–3034 of `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`, as assigned. The file has 8,964 lines; this report does not claim a complete reading of lines 3035–8964. No manuscript changes were made.

## Conclusion

No substantive mathematical defect or claim-status contradiction was found in the assigned range. The opening qualification of the archived 235 bound agrees with `CURRENT_STATUS.md`; 233 and 234 remain conditional. The square census, boundary constants, displayed direct six-count deductions, share/loss algebra and potential comparisons inspected in this range are internally consistent.

Two minor presentation changes are worthwhile. Neither changes a theorem or discharges an outstanding certificate.

## Findings in priority order

### 1. Explicitly qualify the older floor-eighteen target

Location: `sec:least-floors`, lines 2853–2918, particularly lines 2910–2911. Related current statements: abstract lines 55–75 and lines 2032–2049.

The proposition correctly concerns the earlier boundary-21 criterion. Its concluding sentence nevertheless calls share eighteen “the useful local target” without repeating that restriction. The front matter correctly identifies the current boundary-24 target as fifteen. A reader entering this subsection directly could therefore mistake eighteen for the current unresolved minimum. The older numerical result remains valid.

Replace lines 2910–2911 with:

```tex
For this earlier boundary-twenty-one comparison, the sufficient local
target for $012034$ is share at least 18, requiring exclusion of share
at most 17. That local theorem remains open. The current
boundary-twenty-four profile in Section~\ref{sec:floor14-loss} requires
only share at least 15 for this shape, together with its other stated
premises.
```

### 2. Define the total loss where the earlier small-loss reduction first uses it

Location: `sec:empty-packing`, paragraph “The small-loss reduction with the earlier boundary,” lines 875–892; related notation at lines 859–860 and the later explicit definition at lines 2255–2260.

The exact sum of remainders is defined and used earlier, but the abbreviation `L` is used in this paragraph before being explicitly equated to that sum in the body. The deductions at lines 887–888 require its integrality and nonnegativity. `W` also first appears here ahead of its later window-sum definition. State these meanings locally so that the three-premise reduction is self-contained.

Replace the opening of the paragraph at lines 876–878 with:

```tex
Write $G=24T+\sum_{x\in S}\sigma_{12}(x)$ and
$L=\sum_qr_{12}(q)\in\mathbb Z_{\ge0}$, and let $W$ denote the
window-weight total. The following reduction uses the three premises
```

For complete consistency at its preceding first abbreviated use, replace
`$L\le95$ to domination` at line 860 with
`$\sum_qr_{12}(q)\le95$ to domination`.

## Status and ordering observations requiring no mathematical change

- The archived 235 theorem is explicitly qualified at lines 134–142, 339 and 360–376. Its stronger empty-square consequence remains tied to that archived dependency. The current status record is consistent with this presentation.
- The unresolved 1358 reference entries at lines 2512–2520 concern the separate exact-reference package; the manuscript explicitly explains why this does not contradict the archived contributor catalogue.
- Native potential scans and unfinished full Lean potential certificates are distinguished at lines 2791–2800. A numerical scan is not represented there as completion of the actual-snake proof.
- The boundary-21 statements following the stronger boundary-24 proposition are valid historical comparisons. Lines 2283–2285 already provide a useful qualification. Updating all historical constants is unnecessary and would erase the intended comparison.
- The old original-target table at lines 2033–2048 is expressly labelled historical by the preceding paragraph; it does not incorrectly state the current four-floor target.

## Sources actually read

1. `D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex`, all lines 1–3034. A targeted text search of the same file additionally located the later current-profile labels and matching summary lines; those later sections were not read in full for this report.
2. `E:/Snake-in-a-box/handoff/CURRENT_STATUS.md`, complete record headed “Current state after round 199.”

## Limitations

This is a source review of the assigned front matter and proof sections. Finite certificates, witness arrays, contributor dependency closures and Lean artifacts were not rebuilt or replayed. No tests, heavy research processes, external searches, memory changes or nested delegation were performed. The review does not certify an unconditional bound of 233 or 234, and does not independently rebuild the archived 235 proof.
