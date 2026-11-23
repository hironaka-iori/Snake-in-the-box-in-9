from pathlib import Path
r=Path(__file__).resolve().parent;s=(r/'verify.py').read_text().replace("'geo3','geo0'","'geo3','geo0','full0','realctrl','fg0','fg1','fg2','fg3'").replace("('ctrl','geocontrol')","('ctrl','geocontrol','realctrl')")
s=s.replace('print(data)','''import gzip
known={key(q) for s in gzip.open(Path.cwd()/'q9_free_bridge_join_inputs.txt.gz','rt') if len(q:=list(map(int,s.split())))==192}
assert len(known)==131
z=list(map(int,(r/'realctrl.out').read_text().split()));out=z[2:];precursor=list(map(int,(r/'realctrl.pts').read_text().splitlines()[z[0]].split()))
assert len(precursor)==len(out)==192 and check(precursor[:-1]) and not check(precursor) and check(out)
data['natural_control']={'verified_original_190':True,'input_chords':sum((precursor[i]^precursor[j]).bit_count()==1 for i,j in combinations(range(192),2) if j>i+1),'output_is_among_131':key(out) in known}
print(data)''')
(r/'verify.py').write_text(s)

