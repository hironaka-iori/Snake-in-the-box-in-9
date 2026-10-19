"""Enumerate local degree-compatible states in the two 18-vertex cell types.

Internal cycles are allowed. This is a candidate table for a constructive model,
not an enumeration of complete snakes or an upper-bound certificate.
"""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parents[1]


def main():
    source=HERE/'data/base5-size14.json'
    bases=json.loads(source.read_text())['base_sets']
    holes=sorted(set(range(32))-set(bases[0])-set(bases[1]))
    assert len(holes)==4 and all((v^w).bit_count()!=1 for i,v in enumerate(holes)for w in holes[:i])
    records=[];tables=[]
    for base in bases:
        vertices=base+holes
        neighbors=[sum(1<<j for j,w in enumerate(vertices)if(v^w).bit_count()==1)for v in vertices]
        rows=[];max_by_ports={};counts={}
        for selected in range(1<<18):
            ends=0;valid=True
            for i in range(14):
                if selected>>i&1:
                    degree=(neighbors[i]&selected).bit_count()
                    if degree not in (1,2):valid=False;break
                    ends+=degree==1
                    if ends>2:valid=False;break
            if not valid:continue
            degrees=[(neighbors[i]&selected).bit_count()if selected>>i&1 else 0 for i in range(14,18)]
            if any(degree>2 for degree in degrees):continue
            ports=selected>>14;count=selected.bit_count()
            rows.append([selected,ports,*degrees,ends,count])
            counts[ports]=counts.get(ports,0)+1
            max_by_ports[ports]=max(max_by_ports.get(ports,0),count)
        # Empty ports with the entire base cycle selected must occur.
        assert [16383,0,0,0,0,0,0,14]in rows
        tables.append({'vertices':vertices,'rows':rows})
        records.append({'states':len(rows),'states_by_port_mask':counts,'max_vertices_by_port_mask':max_by_ports})
    payload={'base_source_sha256_lf':hashlib.sha256(source.read_bytes().replace(b'\r\n',b'\n')).hexdigest(),
        'port_vertices':holes,'columns':['selected_mask','port_mask','degree0','degree1','degree2','degree3','internal_endpoints','vertex_count'],
        'scope':'All local degree-compatible subsets; global port degrees, total endpoints, and connectivity remain to impose.',
        'tables':tables}
    (HERE/'data/cell-states.json').write_text(json.dumps(payload,separators=(',',':'))+'\n',encoding='utf-8',newline='\n')
    summary={'status':'ENUMERATED','port_vertices':holes,
        'port_degree_pairs':[[sum((v^w).bit_count()==1 for w in base)for base in bases]for v in holes],
        'subsets_examined_per_type':1<<18,'types':records,
        'table_sha256_lf':hashlib.sha256((HERE/'data/cell-states.json').read_bytes()).hexdigest(),
        'script_sha256_lf':hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()}
    (HERE/'data/cell-census.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'port_vertices':holes,'state_counts':[r['states']for r in records]}))


if __name__=='__main__':main()
