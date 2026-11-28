"""Find the maximum after actually taking the newly available step at the left tip."""
from pathlib import Path
import json
from tempfile import TemporaryDirectory
from interval import BANK, HERE, N, check, rebuild, solve
from spectrum import Spectrum


def main():
    donor = json.loads(BANK.read_bytes())[0]['vertex_sequence']
    prefix = donor[:128]
    choices = [v for v in N[prefix[0]] if v not in prefix and
               sum((v^w).bit_count()==1 for w in prefix)==1]
    assert choices == [32]
    core = [choices[0]] + prefix
    output = HERE/'forced-step.json'
    result = json.loads(output.read_bytes()) if output.exists() else dict(core=core,cases={})
    with TemporaryDirectory() as tmp:
        scratch=Path(tmp)
        if 'enumeration' not in result:
            result['enumeration']=Spectrum(scratch).query(core,5000000,192)
        search=result['enumeration']
        low=search['maximum_seen']
        high=low if search['closed'] else 191
        best=search['maximum_path']
        verifier,_=rebuild.masks.compilers(scratch)
        while low<high:
            target=(low+high+1)//2
            cases=result['cases'].setdefault(str(target),{})
            for maj in ((0,1) if target%2==0 else (0,)):
                if cases.get(str(maj),{}).get('status') not in ('excluded','witness'):
                    cases[str(maj)]=solve(core,target,maj,HERE,scratch,verifier,18)
                row=cases[str(maj)]
                if row['status']=='witness':
                    low=target
                    best=row['path']
                    break
            else:
                if all(row['status']=='excluded' for row in cases.values()):
                    high=target-1
                else:
                    break
        check(best)
        result.update(lower=low,upper=high,best=best)
        output.write_text(json.dumps(result,separators=(',',':'))+'\n')
        print('Forced left step',choices,'length range',low,high,'exhaustive enumeration',search['closed'])


if __name__=='__main__':
    main()
