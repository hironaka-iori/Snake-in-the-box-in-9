from pathlib import Path
import hashlib,json,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
checkpoint='''Current mathematical checkpoint: [milestone 57](milestones/57-replacement-share-family/README.md). The full replacement critical family has 37 states, 48 edges and 17 patterns. Nine individual patterns cover every cycle. Screening these gives three numerical share-96 candidates with verified ordinary local forests. One candidate raises the exact exploratory mean from 102/25 to 49/12; all three together give the same value. The conditional edge estimate still rounds down to 235. Four Lean audits verify the selected pattern's finite-graph cycle coverage; the share bounds themselves remain numerical. The contributor-checked interval remains **191 <= a(9) <= 235**.'''
next_step='''Next research priority: Extract the replacement family of mean 49/12 and seek further empty-square share restrictions with sufficient combined effect to reach 234. Replaying the two additional candidates would not improve the present mean. The catalogue's numerical premises and complete graph-to-snake assembly remain unresolved. This is research round 1 of 10 after manuscript revision 56; the next scheduled paper revision is milestone 66.'''
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;s=p.read_text(encoding='utf-8')
    a=s.index('Current mathematical checkpoint:');b=s.index('\n\nCurrent manuscript revision:',a)
    s=s[:a]+checkpoint+s[b:]
    a=s.index('Next research priority:');b=s.index('\n\nThe preceding paper revision',a)
    s=s[:a]+next_step+s[b:]
    p.write_text(s,encoding='utf-8',newline='\n')
paper=ROOT/'paper/snake9_research.tex';mirror=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert paper.read_bytes()==mirror.read_bytes()
digest=hashlib.sha256(paper.read_bytes()).hexdigest()
assert digest==json.loads((ROOT/'milestones/56-packing-limit-and-revision/data/verification.json').read_text())['paper_sha256']
refs=subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse','HEAD','origin/main','origin/research/unconditional-241'],cwd=ROOT).decode().splitlines()
(HERE/'data/repository-state.json').write_text(json.dumps(dict(before_commit=dict(zip(['HEAD','origin/main','contributor'],refs)),paper_sha256=digest,paper_unchanged=True),indent=2)+'\n')
