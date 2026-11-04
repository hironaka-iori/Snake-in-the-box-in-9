"""Pin the separate retained-loss arithmetic check after the replay batch."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]

def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def write(p,b):
    b=b.encode() if isinstance(b,str) else b
    if p.exists():assert p.read_bytes()==b,str(p)
    else:p.write_bytes(b)

def main():
    previous=H/'data/prefix-execution.json';plan=json.loads(previous.read_text())
    assert (H/'data/completion.json').exists()
    assert json.loads((H/'data/completion.json').read_text())['status']=='PASS_BOUNDED_PREFIX_COMPOSITION'
    checker=(H/'scripts/check_prefix.py').read_text().replace('data/prefix-execution.json','data/remainder-execution.json')
    checker_path=H/'scripts/check_remainder.py';write(checker_path,checker)
    src=H/'lean/RemainderComparison163.lean'
    plan['status']='PREPARED_RETAINED_LOSS_ARITHMETIC'
    plan['module_order']=plan['new_module_order']=['RemainderComparison163']
    plan['source_sha256']={'RemainderComparison163':sha(src)}
    plan['checker_sha256']=sha(checker_path)
    for p in [previous,H/'data/completion.json',Path(__file__),checker_path,
              H/'ROUNDING_LOSS.md',H/'review/local-lemma-explanation.md']:
        plan['input_pins'][str(p)]=sha(p)
    plan['scope']='Arithmetic with explicit packing, exact-budget, potential and positive-loss hypotheses; no proof of those additional geometric or potential hypotheses.'
    plan['positive_loss_bound_proved']=False
    plan['new_full_graph_potential_proved']=False
    write(H/'data/remainder-execution.json',json.dumps(plan,indent=2)+'\n')
    print('PREPARED_SEVEN_ARITHMETIC_STATEMENTS')

if __name__=='__main__':main()
