# Manuscript review, sections 1–20

The review covers the preamble, abstract and sections 1–20 of the Round 249 manuscript, through the last paragraph before “Two-coordinate history classification” (lines 1–6273). The Round 249 input SHA-256 was 1c35412fedf13e91e941a046878a02a95113b229eeaa76eda4e1ad8916a550e7.

## Coverage and method

A line-by-line comparison against the [Round 240 review copy](../../240-five-count-recovery/data/snake9_research-before.tex) matched 6,252 lines of this range. The two changed regions were the date and the abstract, where four prior lines became twenty. The unchanged text had already been read in contiguous batches. This review used those records for the unchanged lines, read the changed text, and revisited proof statements and passages affected by later results. [Earlier review of lines 1–4400](../../240-five-count-recovery/logs/full-review-part1.md) · [Earlier review from line 4401](../../240-five-count-recovery/logs/full-review-part2.md)

Sections 1–8 cover the square census, the 235 bound and bounds on local counts. Sections 9–16 cover overlapping windows, the allocation of local contributions and restricted graph comparisons. Sections 17–19 distinguish the contributor results from alternative conditional arguments. Section 20 covers the path constructions, including joins, replacements and symmetries. Two proof samples were rederived directly. The bijection between three-vertex squares and internal path vertices gives \(s_3=v-2\), hence \(T+2s_0+35v=9214\). In a one-crossing join, projected arms may share only the joining endpoint, and the joined length is the sum of their lengths plus one. A separate two-crossing model with a fixed middle path has different hypotheses. [Manuscript](../../../paper/snake9_research.tex)

## Corrections and evidence

- Removed an obsolete 191-edge ceiling from the abstract and corrected the reading guide and the two-layer construction discussion. The earlier 93-edge partner exclusion remains valid. At both endpoints of the archived 98-edge parent, the recorded bounds on the partner are 80 through 88, giving joined bounds of 179 through 187. Among the original fifteen long parent shapes, the only ones attaining 191 are donors 30, 49, 59, 69 and 73. Each uses a 96-edge parent and a 94-edge partner. [Thirty rooted cases](../../249-long-parent-joins/audit.json) · [Two endpoints of the 98-edge parent](../../249-long-parent-joins/audit98.json)
- Added a source for the scope of the contributor's 230 theorem. Its conditional audit assumes the table of local exclusions and the share inequalities. The contributor recorded a completed audit of the unconditional bound 231. An independent full rebuild remains pending. [Contributor assembly record at the reviewed revision](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/e0ddaefcd2cc520c9fa81ef2df37f49952e6656d/milestones/37-230-feasibility/ASSEMBLY.md)

The Round 241–249 summaries were consulted for the other abstract additions. This was a written-source and evidence review. The archived solver proofs and the contributor's Lean build were not rerun.
