"""Publish the verified joint-sum checkpoint and separately label the new screen."""
import hashlib,json,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
SCREEN=ROOT/'milestones/32-seven-count-four-screen'
def git(*args):return subprocess.check_output(['git','-c','safe.directory=E:/Snake-in-a-box',*args],cwd=ROOT,text=True).strip()
def digest(p):return hashlib.sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
def main():
    assert json.loads((HERE/'data/verification.json').read_text())['audited_theorems']==20
    assert json.loads((SCREEN/'data/verification.json').read_text())['lean_coverage_audits']==3
    summary=('The current completed proof checkpoint is [milestone 31](milestones/31-joint-counter-soundness/README.md), dated 23 October. '
      'Twenty Lean audits establish joint high-count lower bounds 29 and 28 for the two surviving seven-centre shapes, '
      'using a reusable counter argument that retains repeated corner occurrences. '
      'After overlap accounting, the qualifying windows contribute 88 or 80 additional integer charge units. '
      'The recorded cycles of means 119/29 and 287/60 avoid these windows, so the global bound is unchanged. '
      '[Milestone 32](milestones/32-seven-count-four-screen/README.md) proposes that six consecutive internal singleton counts cannot all equal four. '
      'All 34 normalized six-centre cases are solver-UNSAT; their finite coverage has three Lean audits, while numerical refutations and the full arbitrary-snake reduction remain pending. '
      'A five-centre local positive control passed independent checks. The 131-path bank has maximum observed run two, which is not a universal bound.')
    p=ROOT/'README.md';s=p.read_text(encoding='utf-8');start=s.index('The current checkpoint is');end=s.index('\n\n| Claim',start)
    s=s[:start]+summary+' This checkout integrates 191 <= a(9) <= 238. The separate collaborator 237 audit has not been imported or independently rebuilt here.'+s[end:];p.write_text(s,encoding='utf-8')
    p=ROOT/'COLLABORATION.md';s=p.read_text(encoding='utf-8');start=s.index('The current checkpoint is');end=s.index('\n\nLatest GitHub refresh',start)
    s=s[:start]+summary+'\n\nNext: certify the 34 six-centre all-four exclusions and connect the checked classification to arbitrary snakes. Preserve UNKNOWN in the shorter five-centre screens. Case-2 high sum at most 29 is a separate solver-only exclusion; a local forest attains sum 30.'+s[end:];p.write_text(s,encoding='utf-8')
    p=ROOT/'milestones/README.md';s=p.read_text(encoding='utf-8');start=s.index('Active direction as of');end=s.index('\n\n',start)
    s=s[:start]+'Active direction as of 23 October: milestone 31 proves joint singleton-count excess and its weighted contribution to the empty-square charge (20 Lean audits). Milestone 32 tests a direction-independent prohibition on six consecutive count-four centres; all 34 cases are solver-excluded and finite coverage is checked, but the complete theorem is pending. The global bound is unchanged.'+s[end:]
    s+='\n- [Joint singleton-count bounds](31-joint-counter-soundness/README.md)\n- [Consecutive singleton counts equal to four](32-seven-count-four-screen/README.md)\n';p.write_text(s,encoding='utf-8')
    p=ROOT/'WORKSPACE.md';s=p.read_text(encoding='utf-8');start=s.index('The current checkpoint is');end=s.index('\n\nConstruction work',start)
    s=s[:start]+summary+'\n\nAll milestone31 replays and wrappers are complete. Build location is in milestone31/build/latest.txt. The next milestone32 task is geometric certificate replay and normalization; its FamilyCoverage module already passed in a fresh standard-library build. Milestone32 short five-centre indices0,1,6 and independent six-centre23 are UNKNOWN; do not claim those are exclusions.'+s[end:];p.write_text(s,encoding='utf-8')
    old=subprocess.check_output(['git','-c','safe.directory=E:/Snake-in-a-box','show','HEAD:paper/snake9_research.tex'],cwd=ROOT).decode('utf-8')
    new=(ROOT/'paper/snake9_research.tex').read_text(encoding='utf-8')
    for pattern in [r'\\author\{[^\n]*\}',r'\\hypersetup\{.*?\n\}']:
        assert re.search(pattern,old,re.S).group()==re.search(pattern,new,re.S).group()
    assert (ROOT/'paper/snake9_research.tex').read_bytes()==Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
    compilation=dict(status='compile-failed',phase='before TeX execution',paper_sha256_lf=digest(ROOT/'paper/snake9_research.tex'),message='exec failed: unsupported operation: windows unelevated restricted-token sandbox cannot enforce split writable root sets directly; refusing to run unsandboxed')
    (HERE/'data/paper-compilation.json').write_text(json.dumps(compilation,indent=2)+'\n')
    refs=['HEAD','origin/main','origin/research/unconditional-241','origin/claude/relaxed-keller-60ks7i','origin/research/unconditional-231-230']
    (HERE/'data/github-refresh.json').write_text(json.dumps(dict(date='2026-10-23',refs={r:git('rev-parse',r) for r in refs},new_collaborator_commits=False),indent=2)+'\n')
    for h in [HERE,SCREEN]:
        files=[]
        for folder in ['lean','scripts','upstream']:
            if not (h/folder).exists():continue
            for p in sorted((h/folder).rglob('*')):
                if p.is_file() and '__pycache__' not in p.parts:files.append(dict(path=str(p.relative_to(ROOT)).replace('\\','/'),sha256_lf=digest(p)))
        (h/'data/source-manifest.json').write_text(json.dumps(dict(dependency_checkpoint=git('rev-parse','HEAD'),lean='4.19.0',files=files),indent=2)+'\n')
    print('Verified checkpoint recorded; author and hyperlink metadata preserved.')
if __name__=='__main__':main()
