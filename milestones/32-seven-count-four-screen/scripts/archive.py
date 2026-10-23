"""Lossless certificate storage. Use --pack once, --unpack before regeneration."""
import argparse, gzip, hashlib, json
from pathlib import Path
HERE=Path(__file__).resolve().parents[1]
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--pack',action='store_true');ap.add_argument('--unpack',action='store_true');args=ap.parse_args()
    assert args.pack != args.unpack
    manifest=HERE/'data/archives.json'
    if args.pack:
        records=[]
        for p in sorted((HERE/'certificates').iterdir()):
            if p.suffix not in ('.cnf','.drat','.lrat') or p.name.split('.')[0] not in {'four0','four1','four14','four22'}: continue
            raw=p.read_bytes();out=p.with_name(p.name+'.gz');out.write_bytes(gzip.compress(raw,mtime=0))
            records.append(dict(file=p.name,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),archive_sha256=hashlib.sha256(out.read_bytes()).hexdigest()))
        manifest.write_text(json.dumps(records,indent=2)+'\n')
    else:
        for r in json.loads(manifest.read_text()):
            p=HERE/'certificates'/r['file'];compressed=p.with_name(p.name+'.gz').read_bytes()
            assert hashlib.sha256(compressed).hexdigest()==r['archive_sha256']
            raw=gzip.decompress(compressed);assert hashlib.sha256(raw).hexdigest()==r['sha256']
            if p.exists(): assert p.read_bytes()==raw
            else:p.write_bytes(raw)
    print('Certificate archives checked.')
if __name__=='__main__':main()
