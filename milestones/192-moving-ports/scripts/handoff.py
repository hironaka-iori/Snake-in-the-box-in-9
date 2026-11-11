from pathlib import Path
import json,hashlib,re
R=Path('E:/Snake-in-a-box');H=R/'milestones/192-moving-ports'
handoff='''# Round 192 complete; goal active

The user explicitly resumed after the completed round191 pause. Leave the goal active; do not carry the earlier pause forward.

Read milestones/192-moving-ports/MATHEMATICAL_NOTE.md and data/completion.json. The current direction is constructive dimension lifting, with middle/outer components and crossing vertices allowed to vary.

For positive-length induced paths P,Q, let D,A,C be deleted, added and common sets; let d count deleted old endpoints and a count added new endpoints. Endpoint-corrected identities are e(A)+a=e(D)+gain+d and boundary(A,C)+d=boundary(D,C)+a. Component counts have the same correction. Finite arithmetic/counting implications pass Lean under explicit degree premises; the generic path bridge remains written.

The full Q9 model on normalized bank25 excludes a192-edge path omitting at most4 original vertices, even with endpoint and crossing changes unrestricted (30.907s). This gives minimum5 omissions/6 additions computationally, without a Lean contradiction certificate. The exactly-two-crossing, at-most6-omission query is UNKNOWN at120.078s. This concerns the whole191-edge witness; keep it distinct from the fixed95-to97 middle problem, whose minimum omission restriction remains8.

The main new geometric Lean result excludes any fixed alternate-square substitutions at the190 internal positions of normalized bank25, followed by one endpoint extension. Both original endpoint positions stay unchanged before extension. All18 endpoint candidates and the combined theorem SquareExtension192 pass. The proof checks actual cube coordinates and requires only necessary nonconsecutive and extension-separation conditions. It is a restricted geometric exclusion, not a global bound.

The corresponding native search excludes all2358 extension candidates over131 saved witnesses. Its147 distinct valid rooted implication closures comprise142 single,4 double and1 triple substitution. Each of these147 results belongs to an existing bank class, and none changes two-crossing ports. The147 rooted closures do not enumerate all valid simultaneous substitution sets. The endpoint-extension exclusion is complete for arbitrary subsets because each extension has a separate forced-closure query. Successive batches with recomputed corners and larger reroutings remain outside scope.

All23 new Lean modules pass,30 dependency reports. One failed aggregate proof snapshot is preserved. A startup guard stopped before case12 below1GiB free memory; remaining cases and aggregate succeeded after memory recovered. Do not weaken resource limits:1GiB startup,768MiB reserve,256MiB per process,60s per check, one heavy worker at a time. All research worker sessions are terminal.

Next constructive step: enumerate three- or four-transition block reorderings in the bank, preserving each block's endpoints, and inspect whole-path inducedness, rare-coordinate crossing positions and endpoint growth. These replacements may use vertices outside the fixed alternate-square choices. This is a proposal, without a success claim. Avoid repeating unchanged UNKNOWN models.

Round191 showed the displayed optimal26-edge Q6 middle supports only a48-edge two-crossing lift, while a shorter24-edge middle supports50. The fixed50-edge Q7 middle has a89-edge witness and inherited restricted upper97. The fixed98-edge Q8 middle targeting192 remains unresolved. These are specified-seed results.

Inherited upper-bound work remains qualified: archived235 independent rebuild pending; conditional233/234; round187 has93/98 clause batches and11904/12424 clauses checked; critical contradiction and actual-snake transfer pending. The direct Q8 all-pairs Lean recheck from188 is pending. Whole-source consistency review completed190; next200.

Contributor branch research/unconditional-241 advanced to b2f85574241bd8d9aca499440b9bc0f3b4c0def0 with36 production records; diff saved, no merge or independent rebuild. Preserve unrelated .gitignore and milestones/50-three-count-return/excess-screen/data/critical-family.json changes. Existing D: editor manuscripts are mirrored in E:/Snake-in-a-box/paper; authors and hypersetup are preserved.
'''
# Keep prose readable while retaining conventional Q8/Q9 and exact identifiers.
handoff=re.sub(r'(?<=[A-Za-z])(?=\d)', ' ', handoff)
handoff=handoff.replace('Q 8','Q8').replace('Q 9','Q9').replace('Q 6','Q6').replace('Q 7','Q7')
handoff=handoff.replace('bank 25','bank25').replace('SquareExtension 192','SquareExtension192').replace('unconditional-241','unconditional-241')
# Restore identifiers which must remain exact after prose spacing.
handoff=handoff.replace('b 2f 85574241bd 8d 9aca 499440b 9bc 0f 3b 4c 0def 0','b2f85574241bd8d9aca499440b9bc0f3b4c0def0')
(R/'handoff/CURRENT_STATUS.md').write_text(handoff,encoding='utf-8',newline='\n');(R/'handoff/NEXT_AGENT_PROMPT.md').write_text('Continue the active goal from the round192 checkpoint. The earlier requested pause was fulfilled and has been superseded by explicit resumption.\n\n'+handoff,encoding='utf-8',newline='\n')
p=R/'README.md';old=p.read_text();assert not old.startswith('# Current result after round 192')
p.write_text('''# Current result after round 192

The goal is active. Lean now excludes every simultaneous fixed-square substitution followed by an endpoint extension for the selected 191-edge witness. All 18 geometric cases and their combined statement pass. The broader native census excludes 2358 candidates across all 131 saved witnesses.

Endpoint corrections extend the replacement accounting to moving endpoints. A joint solver model excludes a 192-edge path omitting at most four vertices of the selected witness, with endpoints and crossings unrestricted; that numerical exclusion has no Lean contradiction certificate. No longer Q9 snake or improved global bound was obtained.

Read [round 192](milestones/192-moving-ports/README.md), [the argument](milestones/192-moving-ports/MATHEMATICAL_NOTE.md), [handoff](handoff/CURRENT_STATUS.md), [paper](paper/snake9_research.tex), and [frontier explanation](paper/snake9_frontier_explanation.tex).

## Earlier checkpoints

'''+old,encoding='utf-8',newline='\n')
(H/'scripts/handoff.py').write_bytes(Path(__file__).read_bytes())
print('SAVED active handoff and README')
