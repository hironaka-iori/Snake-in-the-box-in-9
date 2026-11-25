"""Exhaust both opposite-face Q7 partner searches for the specified optimal Q7 primer."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import gzip
import json
import subprocess

HERE=Path(__file__).resolve().parent
CSC=Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")


def read(path):
    return json.loads(path.read_bytes())


def write(path,data):
    tmp=path.with_suffix(".tmp")
    tmp.write_text(json.dumps(data,separators=(",",":"))+"\n",encoding="utf8",newline="\n")
    tmp.replace(path)


def physically(word):
    p=[0]
    for axis in word:
        p.append(p[-1]^(1<<axis))
    return p


def valid(path,d):
    assert len(set(path))==len(path) and all(0<=v<2**d for v in path)
    selected=set(path)
    for i,v in enumerate(path):
        neighbours={v^(1<<j) for j in range(d)}&selected
        assert neighbours==set(path[max(0,i-1):i]+path[i+1:i+2])


def canonical(path):
    word=bytes((u^v).bit_length()-1 for u,v in zip(path,path[1:]))
    def rename(s):
        old=bytes(dict.fromkeys(s))
        return s.translate(bytes.maketrans(old,bytes(range(len(old)))))
    return min(rename(word),rename(word[::-1])).hex()


def prefixes(parent,depth):
    layer=[[0]]
    blocked=set(parent[1:])
    for _ in range(depth):
        children=[]
        for p in layer:
            for j in range(7):
                w=p[-1]^(1<<j)
                if w not in p and w not in blocked and not any((w^u).bit_count()==1 for u in p[:-1]):
                    children.append(p+[w])
        layer=children
    return layer


def parse_parent(data,key,field):
    if key:
        word=data["paths"][key]["word"][:50]
        assert set(word)==set("0123456")
        return physically(map(int,word))
    return data[field] if isinstance(data,dict) else data


def main():
    args=ArgumentParser()
    args.add_argument("source",type=Path)
    args.add_argument("--field",default="q7_parent")
    args.add_argument("--word-key",help="Read the named Q8 transition sequence in paths and take its first 50 digits in axes 0 to 6.")
    args.add_argument("--minimum",type=int,default=45)
    args.add_argument("--depth",type=int,default=1)
    args.add_argument("--seconds",type=int,default=90)
    args.add_argument("--nodes",type=int,default=900000000)
    args.add_argument("--batch",type=int,default=0)
    args.add_argument("--audit",action="store_true")
    opt=args.parse_args()
    assert 30<=opt.minimum<=49 and 0<=opt.depth<opt.minimum and opt.nodes>0 and opt.seconds>0
    src=opt.source if opt.source.is_absolute() else HERE/opt.source
    parent=list(parse_parent(read(src),opt.word_key,opt.field))
    valid(parent,7)
    assert len(parent)==51
    parent_id=sha256(bytes(parent)).hexdigest()
    source_hash=sha256(src.read_bytes()).hexdigest()
    folder=HERE/("primer-%s-m%d-d%d"%(parent_id[:10],opt.minimum,opt.depth))
    folder.mkdir(exist_ok=True)
    idx=folder/"census.json"
    audit_path=folder/"replay.json"
    cs=HERE/"PrimerPartners.cs"
    cshash=sha256(cs.read_bytes()).hexdigest()
    meta=dict(source=src.name,source_sha256=source_hash,word_key=opt.word_key,parent=parent,dimension=7,
              minimum_partner_edges=opt.minimum,shard_depth=opt.depth,program_sha256=cshash)
    pending=[]
    for end,order in enumerate((parent,parent[::-1])):
        p=[x^order[0] for x in order]
        for seq in prefixes(p,opt.depth):
            tag=str(end)+"-"+bytes(seq).hex()
            pending.append((tag,end,p,seq))
    census=read(idx) if idx.exists() else dict(meta=meta,shards={})
    assert census['meta']==meta
    data=(read(audit_path) if audit_path.exists() else dict(meta=meta,shards={})) if opt.audit else census
    assert data['meta']==meta
    made=0
    with TemporaryDirectory(prefix="q7-primer-") as work:
        root=Path(work)
        exe=root/"PrimerPartners.exe"; paths=root/"paths.txt"
        subprocess.run([str(CSC),"/nologo","/optimize+","/platform:x64","/out:"+str(exe),str(cs)],check=True,capture_output=True)
        for tag,end,p,pre in pending:
            if data['shards'].get(tag,{}).get('status')=='complete':continue
            if opt.audit and census['shards'].get(tag,{}).get('status')!='complete':continue
            task=subprocess.run([str(exe),"array" if opt.audit else "mask",str(opt.minimum),str(opt.nodes),str(opt.seconds),str(paths)],
                         input=",".join(map(str,p))+"\n"+",".join(map(str,pre))+"\n",
                         text=True,capture_output=True,check=True)
            status,nodes,total,parity,reach=task.stdout.split()
            row=dict(status=status,end=end,prefix=pre,nodes=int(nodes),emitted=int(total),
                     parity_cuts=int(parity),component_cuts=int(reach))
            if status=="complete":
                ordered=[]
                shapes=Counter()
                counts=Counter()
                blocked=set(p[1:])
                for line in paths.read_text(encoding="ascii").splitlines():
                    q=list(map(int,line.split(",")))
                    assert q[:len(pre)]==pre and not blocked.intersection(q) and len(q)>opt.minimum
                    valid(q,7)
                    lifted=p[::-1]+[v+128 for v in q]
                    valid(lifted,8)
                    shapes[canonical(lifted)]+=1
                    ordered.append(bytes(q).hex());counts[len(q)-1]+=1
                assert len(ordered)==len(set(ordered))==int(total)
                raw=("".join(q+"\n" for q in sorted(ordered))).encode("ascii")
                dest=folder/(tag+".hex.gz")
                row.update(partner_edges=dict(sorted(counts.items())),shape_multiplicities=shapes,
                       paths=dest.name,plaintext_sha256=sha256(raw).hexdigest())
                if opt.audit:
                    expected=census['shards'][tag]
                    assert expected['plaintext_sha256']==row['plaintext_sha256'] and gzip.decompress(dest.read_bytes())==raw
                    assert expected['shape_multiplicities']==shapes
                else:
                    dest.write_bytes(gzip.compress(raw,mtime=0))
            data['shards'][tag]=row
            write(audit_path if opt.audit else idx,data)
            made+=1
            print(tag,status,nodes,total,flush=True)
            if opt.batch and made>=opt.batch:break
    combined=Counter()
    lengths={0:Counter(),1:Counter()}
    for row in data['shards'].values():
        if row['status']!="complete":continue
        combined.update(row['shape_multiplicities'])
        lengths[row['end']].update({int(k):v for k,v in row['partner_edges'].items()})
    complete=all(data['shards'].get(tag,{}).get('status')=='complete' for tag,_,_,_ in pending)
    result=dict(complete=complete,total_shards=len(pending),closed_shards=sum(row['status']=="complete" for row in data['shards'].values()),
                labelled_by_end_and_partner_edges=lengths,shapes_by_q8_edges=Counter(len(bytes.fromhex(w)) for w in combined),
                shape_words=sorted(combined),total_labelled=sum(combined.values()))
    data['summary']=result
    write(audit_path if opt.audit else idx,data)
    print("complete",complete,"counts",lengths,"shape lengths",result['shapes_by_q8_edges'])


if __name__=="__main__":
    main()

