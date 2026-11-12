from pathlib import Path
H=Path(__file__).resolve().parents[1]
source=(H/'scripts/target.py').read_text()
source=source.replace('from native_resources import snapshot','from native_resources import snapshot\nfrom block_bounds import terminal_blocks')
marker='                route=[u];local_nodes=0'
assert source.count(marker)==1
source=source.replace(marker,'''                blocks=terminal_blocks(comp,u,v,NM)
                if blocks['upper_edges']<length:
                    current['rejections']['BLOCK_BOUND']+=1
                    if 'BLOCK_BOUND' not in static_examples:static_examples['BLOCK_BOUND']=dict(query=info,block_bound=blocks['upper_edges'],blocks=blocks['blocks'])
                    continue
                comp=blocks['mask']
                route=[u];local_nodes=0''')
source=source.replace("bank_sha256=hashlib.sha256(raw).hexdigest(),script_sha256=", "block_bounds_sha256=hashlib.sha256((H/'scripts/block_bounds.py').read_bytes()).hexdigest(),bank_sha256=hashlib.sha256(raw).hexdigest(),script_sha256=")
source=source.replace("Per-query node limits give UNKNOWN, never exclusions.","Terminal block restriction and sum of block colour bounds, including the adjacent-anchor bound1, are also necessary. Per-query node limits give UNKNOWN, never exclusions.")
target=H/'scripts/target_blocks.py';assert not target.exists();target.write_text(source,encoding='utf-8',newline='\n')
print('PREPARED_TARGET_BLOCKS')
