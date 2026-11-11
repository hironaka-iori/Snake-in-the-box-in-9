from pathlib import Path
import json,hashlib,subprocess
R=Path('E:/Snake-in-a-box');H=R/'milestones/192-moving-ports';P=R/'milestones/191-coloured-replacements';D=Path(__file__).parent
assert not H.exists()
for n in ['data','scripts','lean','build','logs']:(H/n).mkdir(parents=True,exist_ok=True)
(H/'.gitattributes').write_text('* -text\n')
for name in ['check_core.py','native_resources.py']:(H/'scripts'/name).write_bytes((P/'scripts'/name).read_bytes())
(H/'scripts/joint_replacement.py').write_bytes((D/'round192_joint.py').read_bytes());(H/'scripts/prepare.py').write_bytes(Path(__file__).read_bytes())
source=R/'milestones/189-middle-replacements/data/replacement-contexts.json';row=json.loads(source.read_text())['rows'][0];p=row['left']+[v+256 for v in row['middle']]+row['right']
assert len(p)==192 and len(set(p))==192
assert all(((p[i]^p[j]).bit_count()==1)==(j==i+1) for i in range(192) for j in range(i+1,192))
(H/'data/seed.json').write_text(json.dumps({'path':p,'bank_index':row['bank_index'],'original_cross_coordinate':row['coordinate'],'normalized_cross_coordinate':8,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()},indent=2)+'\n')
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
diff=subprocess.check_output(git+['diff','f393c48e..origin/research/unconditional-241','--','milestones/33-233-lean/certify/data/replay6SB233.jsonl'],cwd=R)
(H/'data/contributor-update.diff').write_bytes(diff)
records=[json.loads(line[1:]) for line in diff.decode().splitlines() if line.startswith('+{')]
(H/'data/start.json').write_text(json.dumps({'round':192,'previous_turn':'PROGRESS: published round191 with new counting results, omission restrictions and dimensional comparisons.','parent_commit':'d3557064e26e9806cb3dcfb03f3ed2fb0d5c60da','start_utc':'2026-11-11 04:57:37 UTC','goal_status':'active; explicitly resumed','contributor_head':'b2f85574241bd8d9aca499440b9bc0f3b4c0def0','contributor_records_added':len(records),'contributor_record_kinds':{k:sum(r['kind']==k for r in records) for k in {r['kind'] for r in records}},'contributor_scope':'Production records only; no independent proof rebuild or changed global claim.'},indent=2)+'\n')
print('PREPARED',H,'contributor records',len(records))
