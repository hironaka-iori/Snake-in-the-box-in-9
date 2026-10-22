"""Record milestone provenance and update only the current research summaries."""
import hashlib,json,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
def git(*args):return subprocess.check_output(['git','-c','safe.directory=E:/Snake-in-a-box',*args],cwd=ROOT,text=True).strip()
def digest(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
def replace(path,old,new):
    p=ROOT/path;s=p.read_text(encoding='utf-8');assert old in s,(path,old[:80]);p.write_text(s.replace(old,new,1),encoding='utf-8')

status=('The current checkpoint is [milestone 30](milestones/30-coarse-count-correction/README.md), completed on 23 October. '
        'Nineteen Lean audits passed: two interval exclusions, two exact-six exclusions, their snake interpretations, '
        'and the excess/overlap consequences. For the two surviving seven-centre shapes, the three high counts sum to at least 19. '
        'Each qualifying window therefore contributes eight additional integer charge units after accounting for overlap multiplicity three. '
        'The refined diagnostic has 44,336 states; its witness-table cycle changes from 859/180 to 287/60, '
        'while the lower-table cycle remains 119/29. No global bound improves. '
        'Independent experiments suggest stronger high-count minima: exactly 28 for case 3 in the local model, '
        'and between 29 and 31 for case 2. The lower sides of those experimental intervals remain solver-only. '
        'The next task is a reusable joint-counter soundness argument and proof certificates for those stronger sums.')

def main():
    p=ROOT/'README.md';s=p.read_text(encoding='utf-8')
    start=s.index('Research checkpoint:');end=s.index('\n\n| Claim',start)
    s=s[:start]+status+' This checkout integrates 191 <= a(9) <= 238. The separate collaborator 237 audit has not been imported or independently rebuilt here.'+s[end:]
    p.write_text(s,encoding='utf-8')
    p=ROOT/'COLLABORATION.md';s=p.read_text(encoding='utf-8').replace('Checkpoint: 22 October 2026.','Checkpoint: 23 October 2026.',1)
    start=s.index('The current checkpoint is');end=s.index('\n\nLatest GitHub refresh:',start)
    s=s[:start]+status+s[end:];s=s.replace('Latest GitHub refresh:', 'Latest GitHub refresh (23 October; no new commits):',1);p.write_text(s,encoding='utf-8')
    p=ROOT/'milestones/README.md';s=p.read_text(encoding='utf-8');start=s.index('Active direction as of');end=s.index('\n\n',start)
    s=s[:start]+'Active direction as of 23 October: retain empty-square shares and singleton excess lost by coarse count symbols. Milestone 30 proves two interval exclusions, two exact-six exclusions, and an overlap correction contributing eight integer charge units per qualifying window. Nineteen Lean audits passed. Stronger sum-cap results remain solver-only; the global bound is unchanged.'+s[end:]
    s+='\n- [Coarse singleton-count correction](30-coarse-count-correction/README.md)\n';p.write_text(s,encoding='utf-8')
    p=ROOT/'WORKSPACE.md';s=p.read_text(encoding='utf-8');start=s.index('The current checkpoint is');end=s.index('\n\nConstruction work',start)
    s=s[:start]+status+' See milestone30/data/verification.json and the final logs. Main integrates 238; collaborator 237 is not independently rebuilt here.'+s[end:];p.write_text(s,encoding='utf-8')
    refs=['HEAD','origin/main','origin/research/unconditional-241','origin/claude/relaxed-keller-60ks7i','origin/research/unconditional-231-230']
    (HERE/'data/github-refresh.json').write_text(json.dumps(dict(date='2026-10-23',refs={r:git('rev-parse',r) for r in refs},new_commits_since_previous_checkpoint=False),indent=2)+'\n')
    compilation=dict(path='D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex',status='compile-failed',phase='before TeX execution',
        message='exec failed: unsupported operation: windows unelevated restricted-token sandbox cannot enforce split writable root sets directly; refusing to run unsandboxed',paper_sha256_lf=digest(ROOT/'paper/snake9_research.tex'))
    (HERE/'data/paper-compilation.json').write_text(json.dumps(compilation,indent=2)+'\n')
    files=[]
    for folder in ['lean','scripts']:
        for p in sorted((HERE/folder).rglob('*')):
            if p.is_file() and '__pycache__' not in p.parts:files.append(dict(path=str(p.relative_to(ROOT)).replace('\\','/'),sha256_lf=digest(p)))
    (HERE/'data/source-manifest.json').write_text(json.dumps(dict(dependency_checkpoint=git('rev-parse','HEAD'),lean='4.19.0',mathlib_commit='c44e0c8ee63ca166450922a373c7409c5d26b00b',files=files),indent=2)+'\n')
    # Protect metadata and hyperlink settings against accidental paper changes.
    old=subprocess.check_output(['git','-c','safe.directory=E:/Snake-in-a-box','show','HEAD:paper/snake9_research.tex'],cwd=ROOT).decode('utf-8')
    new=(ROOT/'paper/snake9_research.tex').read_text(encoding='utf-8')
    for pattern in [r'\\author\{[^\n]*\}',r'\\hypersetup\{.*?\n\}']:
        assert re.search(pattern,old,re.S).group()==re.search(pattern,new,re.S).group()
    assert (ROOT/'paper/snake9_research.tex').read_bytes()==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
    print('Checkpoint summaries and provenance recorded; paper metadata preserved.')
if __name__=='__main__':main()
