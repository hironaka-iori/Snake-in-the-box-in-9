from run import *
def run(forms):
 line='points '+' '.join(map(str,forms))+'\n'
 s=subprocess.run([str(R/'q9_change_basis/augment'),'192','90000','0','augment'],input=line,text=True,capture_output=True,check=True).stdout
 return {int(z[2]):(z[3],int(z[5])) for l in s.splitlines() if (z:=l.split()) and z[0]=='FORM'}
def main():
 cs=[json.loads(l) for l in (D/'controls.jobs').read_text().splitlines()]; ps=[json.loads(l) for l in (D/'primary.jobs').read_text().splitlines()]
 ans=[]
 for i,c in enumerate(cs):
    sel=ps[i*8];src=sel['points'];a=c['basis'];sh=c['shift'];tab=[0]
    for x in a:tab += [x^q for q in tab]
    assert len(set(tab))==512
    dual={sum((((g&m).bit_count()&1)<<j) for j,g in enumerate(a)):m for m in range(512)}
    before=run(src);after=run([tab[x]^sh for x in src]);assert len(before)==len(after) and all(after[dual[m]]==val for m,val in before.items())
    line='points '+' '.join(map(str,c['points']))+'\n'; raw=subprocess.run([str(D/'unmasked'),'191','1700000'],text=True,input=line,capture_output=True,check=True).stdout
    witness=verify(next(l for l in raw.splitlines() if l.startswith('FOUND ')),c['points'],191)
    ans.append(dict(primary_case=i*8,dual_parity_checks=len(before),basis_closures=sum(n for _,n in before.values()),control=i,control_witness=witness))
 (D/'symmetry.json').write_text(json.dumps(ans))
if __name__=='__main__':main()
