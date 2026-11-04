"""Reuse the accepted bounded-composition and publication procedures."""
from pathlib import Path
import ast,hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
P=R/'milestones/162-share18-composition-plan'

def write(p,b):
    b=b.encode() if isinstance(b,str) else b
    p.parent.mkdir(parents=True,exist_ok=True)
    if p.exists():assert p.read_bytes()==b,str(p)
    else:p.write_bytes(b)

def main():
    write(H/'.gitattributes','* -text\n')
    copies=[]
    for name in ['prepare_prefix.py','audit_prefix.py','record_completion.py','publication.py']:
        source=P/'scripts'/name;raw=source.read_bytes();text=raw.decode('utf-8')
        if name in ['prepare_prefix.py','audit_prefix.py']:
            text=text.replace('Prefix162','Prefix163')
        elif name=='record_completion.py':
            text=text.replace('Milestones 161 and 162','Milestones 161 and 163')
            text=text.replace('milestones/162-share18-composition-plan','milestones/163-share18-replay-continuation')
            text=text.replace('# Milestone162','# Milestone163')
            text=text.replace('review/remaining-composition.md','../162-share18-composition-plan/review/remaining-composition.md')
        else:
            text=text.replace('162 files','163 files')
            text=text.replace('161/162','161/163')
        ast.parse(text,filename=name)
        out=H/'scripts'/name;write(out,text)
        copies.append(dict(source=source.relative_to(R).as_posix(),source_sha256=hashlib.sha256(raw).hexdigest(),
            output=out.relative_to(H).as_posix(),output_sha256=hashlib.sha256(out.read_bytes()).hexdigest()))
    write(H/'data/helper-preparation.json',json.dumps(dict(status='REUSED_HELPERS_PREPARED',copies=copies,
        mathematical_sources_generated=False,Lean_invoked=False,new_global_bound=False),indent=2)+'\n')
    print('PREPARED_FOUR_REUSED_HELPERS')

if __name__=='__main__':main()
