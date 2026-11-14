from pathlib import Path
import datetime,hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
G=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
def git(*args):return subprocess.check_output(G+list(args),cwd=R)
ref=git('rev-parse','origin/research/unconditional-241').decode().strip()
base='e4b85bb1f447e19a6533fbabe18244b1473c846c'
progress=git('show',ref+':milestones/33-233-lean/CERT-PROGRESS.md')
diff=git('diff',base,ref,'--','milestones/33-233-lean')
(H/'logs/contributor-progress.md').write_bytes(progress)
(H/'logs/contributor-changes.patch').write_bytes(diff)
data=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base=base,ref=ref,progress_sha256=hashlib.sha256(progress).hexdigest(),diff_sha256=hashlib.sha256(diff).hexdigest(),last_report=progress.decode('utf-8').splitlines()[-1],scope='Contributor-reported progress only. No merge, independent rebuild, or numerical-bound upgrade.')
(H/'data/contributor.json').write_text(json.dumps(data,indent=2)+'\n')
print(ref);print(data['last_report'])
