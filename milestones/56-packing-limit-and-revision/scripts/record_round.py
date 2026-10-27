from pathlib import Path
import hashlib,json,re,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
checkpoint='''Current mathematical checkpoint: [milestone 56](milestones/56-packing-limit-and-revision/README.md). A 25-step cycle with count sum 102 has zero recorded share credit at every step. Lean checks that repacking these credits alone cannot raise its normalized mean above 102/25 or exclude 235 through the present accounting. Two modules and ten dependency audits pass. The contributor-checked interval remains **191 <= a(9) <= 235**, with the complete contributor dependency closure not independently rebuilt locally.

Current manuscript revision: [milestone 56](milestones/56-packing-limit-and-revision/README.md). The paper now presents the completed 235 proof and the retained inequality 39m+2s0<=9200, then the local return and share results from rounds 47–55 and the packing limitation. The earlier 236 proof is retained in an appendix. All 95 prior statements are preserved apart from the strengthened main bound; the source has 108 statements. All thirteen printed snakes pass 118,673 pair checks. Authors and hyperlink settings are unchanged, and the existing editor source is synchronized. The built-in compiler failed before source processing because its Windows helper could not start; compilation and visual inspection of this revision remain unverified.

Next research priority: Extract the full minimum-charge family of mean 102/25 and test new empty-square share inequalities on its recurrent patterns. Optimizing the packing of the current zero credits cannot remove the saved cycle. Ordinary feasibility remains a control for share tests. This completes the ten-round revision cycle; the next scheduled paper revision is milestone 66.'''
for name in ['README.md','COLLABORATION.md']:
    p=ROOT/name;s=p.read_text(encoding='utf-8')
    a=s.index('Current mathematical checkpoint:')
    b=s.index('The preceding paper revision is',a)
    s=s[:a]+checkpoint+'\n\n'+s[b:]
    s=s.replace('The current manuscript interval is **191 <= a(9) <= 236**.', 'At milestone 39, the manuscript interval was **191 <= a(9) <= 236**.')
    p.write_text(s,encoding='utf-8',newline='\n')
paper=ROOT/'paper/snake9_research.tex'
receipt=json.loads((HERE/'data/paper-revision.json').read_text())
receipt['after_sha256']=hashlib.sha256(paper.read_bytes()).hexdigest()
receipt['new_label_count']=len(re.findall(r'\\label\{([^}]+)\}',paper.read_text(encoding='utf-8')))
(HERE/'data/paper-revision.json').write_text(json.dumps(receipt,indent=2)+'\n')
refs=subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse','HEAD','origin/main','origin/research/unconditional-241'],cwd=ROOT).decode().splitlines()
(HERE/'data/repository-state.json').write_text(json.dumps(dict(before_commit=dict(zip(['HEAD','origin/main','contributor'],refs)),contributor_dependency_audit='b20346ee15a43b96de34128bc66b05551244cf31'),indent=2)+'\n')
