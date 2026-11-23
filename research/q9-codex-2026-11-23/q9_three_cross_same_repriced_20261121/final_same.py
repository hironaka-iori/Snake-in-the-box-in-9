from trees import *
import re,hashlib
def main():
    manifest=loadrows(['manifest.jsonl']);root={ (r['i'],r['x']):r for l in (D/'native_checked.jsonl').read_text().splitlines() if(r:=json.loads(l))}
    branches={r['rank']:r for f in ('trees.jsonl','deep_trees.jsonl') for l in (D/f).read_text().splitlines() if (r:=json.loads(l))}
    assert len(manifest)==len(jobs)==len(root)==1496
    assert set(branches)=={r['rank'] for r in manifest if r['bound']>=193*r['scale']}
    out=[];direct=0;nodes=0;source=Counter()
    with tempfile.TemporaryDirectory() as tmp:
        tmp=Path(tmp)
        for r in manifest:
            q=rec(r);i,x=r['i'],r['x'];source[r['source']]+=1;c=q['cert'];b=integer_bound(c,set(q['lower_vertices']),set(q['ports']),q['upper_endpoint_counts'],q['upper_delta'])+len(q['lower_vertices'])*c['scale']
            assert b==r['bound']==root[i,x]['bound']
            if b<193*c['scale']:direct+=1;continue
            z=branches[r['rank']];assert (z['i'],z['x'])==(i,x)
            with (tmp/'input').open('w') as f:writecert(f,0,c)
            with (tmp/'input').open() as f,(tmp/'table').open('w') as o:
                subprocess.run([str(D/'emit_tables'),str(R/'q8_catalogue_96_98.words'),str(i),str(x)],stdin=f,stdout=o,check=True)
            (tmp/'tree').write_bytes(gzip.open(D/z['tree'],'rb').read())
            text=subprocess.check_output([str(R/'q9_facet_priced_tree_20261121/replay'),str(tmp/'table'),str(tmp/'tree'),'193'],text=True).strip()
            assert text==z['replay'] and ' open 0 witnesses 0 ' in text and ' invalid_full 0 ' in text
            cnt=int(text.split()[2]);nodes+=cnt;out.append(dict(rank=r['rank'],i=i,x=x,tree=z['tree'],replay=text))
    (D/'tree_manifest.jsonl').write_text(''.join(json.dumps(v,separators=(',',':'))+'\n' for v in out))
    summary=dict(bank_sha256=hashlib.sha256((R/'q8_catalogue_96_98.words').read_bytes()).hexdigest(),cases=len(manifest),direct_roots=direct,closed_trees=len(out),total_tree_nodes=nodes,selected_sources=source,target_vertices=193,even_edge_max=190,remaining=0,independent_root_replays=len(manifest),independently_rebuilt_tree_tables=len(out))
    (D/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary)
if __name__=='__main__':main()
