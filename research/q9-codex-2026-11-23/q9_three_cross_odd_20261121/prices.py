from check import *
from collections import defaultdict
def main():
    ap=argparse.ArgumentParser();ap.add_argument('out');ap.add_argument('--prior',nargs='*',default=[]);args=ap.parse_args()
    closed={(r['i'],r['x']) for r in loadrows(args.prior) if r['bound']<194*r['scale']}
    menu=defaultdict(list);certs=[]
    for path in sorted((R/'q9_catalogue_three_cross/cases').glob('*.json')):
        try:r=json.loads(path.read_text());c=r['cert']
        except ValueError:continue
        donor=int(path.stem.split('_')[0][1:]);menu[donor].append(len(certs));certs.append(c)
    for t in sorted((D/'certs').glob('*_a8.json.gz')):
        donor=int(t.stem.split('_')[0][1:]);menu[donor].append(len(certs));certs.append(json.load(gzip.open(t,'rt')))
    todo=[(i,x,j) for i,x in jobs if (i,x) not in closed for j in menu[i]]
    with tempfile.TemporaryFile('w+') as f:
        for j,c in enumerate(certs):writecert(f,j,c)
        for i,x,j in todo:print('T',j,i,x,file=f)
        f.seek(0);pr=subprocess.Popen([str(D/'refine'),str(R/'q8_catalogue_96_98.words')],stdin=f,stdout=subprocess.PIPE,text=True)
        best={}
        for row,l in zip(todo,pr.stdout,strict=True):
            j,i,x,val,fee,bal=map(int,l.split());assert (i,x,j)==row
            if (i,x) not in best or val<best[i,x][0]:best[i,x]=(val,j,fee,bal)
        assert pr.wait()==0
    with (D/args.out).open('w') as out:
        for (i,x),(val,j,fee,bal) in best.items():
            c=dict(certs[j],end_weights=[0,0],balance_weight=bal);c['end_weights'][1-x.bit_count()%2]=fee
            path=D/'certs'/f'd{i}_x{x}_opt_{args.out.split(".")[0]}.json.gz'
            with gzip.open(path,'wt') as f:json.dump(c,f,separators=(',',':'))
            print(json.dumps(dict(rank=jobs.index((i,x)),i=i,x=x,cert=str(path.relative_to(D)),bound=val,scale=c['scale'])),file=out)
    print('jobs',len(best),'close193',sum(v[0]<194*certs[v[1]]['scale'] for v in best.values()),'close195',sum(v[0]<196*certs[v[1]]['scale'] for v in best.values()))
if __name__=='__main__':main()
