"""Final prose clarification and collaborator-facing status synchronization."""
from pathlib import Path
import hashlib, json
ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]
editor = Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
paper = ROOT/'paper/snake9_research.tex'
s = editor.read_text(encoding='utf-8')
assert s == paper.read_text(encoding='utf-8')
s = s.replace(r'Its next transition appends $b_{i+7}$.',r'For $i\le m-8$, its next transition appends $b_{i+7}$.')
s = s.replace('A separate enumeration made for this revision verifies the same inequality','A separate enumeration of the archived table verifies the same inequality')
editor.write_text(s,encoding='utf-8')
paper.write_text(s,encoding='utf-8')
audit = json.loads((HERE/'data/rewrite-audit.json').read_text())
audit['after_sha256'] = hashlib.sha256(s.encode()).hexdigest()
(HERE/'data/rewrite-audit.json').write_text(json.dumps(audit,indent=2)+'\n')

status = '''The current paper revision is [milestone 43](milestones/43-full-paper-rewrite/README.md). It presents the complete argument for 236 directly, moves the earlier 238 proof to an appendix, and integrates the latest common-budget result with explicit verification limits. All 90 previous statement blocks and all printed witnesses are retained, with two accounting statements added. The existing editor source and repository paper are synchronized; authors and PDF settings are unchanged. The exact editor source compiles successfully.

[Milestone 42](milestones/42-six-count-state-model/README.md) completes a six-count finite model with exact normalized minimum cycle mean 42/11. An eleven-edge cycle and an integer potential checked on all 4,561,226 retained edges establish the finite-model result. Three Lean audits prove the common seven-window excess budget and combined charge arithmetic. All eleven critical windows are solver-UNSAT in a stronger local model, with no replayed refutations yet. There is no new global bound: the paper remains at 191 <= a(9) <= 236. The complete graph-to-snake Lean bridge is also pending.

'''
for name in ['README.md','COLLABORATION.md']:
    path = ROOT/name
    text = path.read_text(encoding='utf-8')
    marker = 'The latest theorem is [milestone 41]'
    assert marker in text
    text = text.replace(marker,status+'The preceding local theorem is [milestone 41]',1)
    old = 'Next: use the new sum theorem in a state model that retains the required count history and shares one excess budget across overlapping patterns. This must establish a bound for every allowed sequence, rather than only remove the saved critical cycle.'
    new = 'Next: extract and replay a useful exclusion from the eleven seven-centre windows on the milestone 42 cycle, then rebuild the graph and verify every remaining transition. The common-budget model is implemented, but its current minimum is unchanged; the numerical window exclusions still need checked geometric refutations.'
    text = text.replace(old,new)
    path.write_text(text,encoding='utf-8')
path = ROOT/'paper/README.md'
text = path.read_text(encoding='utf-8')
text += '\nCurrent logical revision: milestone 43. The main text proves the interval 191 <= a(9) <= 236 directly, then develops local refinements, empty-square shares, the common excess budget, and the finite-model limitation. Earlier bounds and restricted searches are retained in appendices. All previous mathematical statements and printed witnesses are preserved. The exact open editor source compiles successfully; full rendered-page inspection is not claimed.\n'
path.write_text(text,encoding='utf-8')
