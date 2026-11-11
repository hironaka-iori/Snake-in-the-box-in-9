from pathlib import Path
H=Path('E:/Snake-in-a-box/milestones/190-exchange-constraints');s=(H/'scripts/edit_neighbourhood.py').read_text()
(H/'sources/five-baseline.py').write_text(s,encoding='utf-8',newline='\n')
s=s.replace("ap.add_argument('--seconds',type=float,default=90);args=ap.parse_args();tag=f'exact-edits{args.edits}'", "ap.add_argument('--seconds',type=float,default=90);ap.add_argument('--deleted-edges',type=int);args=ap.parse_args();tag=f'exact-edits{args.edits}'+(f'-deletededges{args.deleted_edges}' if args.deleted_edges is not None else '')")
s=s.replace('model.add(sum(added_edges)==sum(deleted_pair)+2)', 'model.add(sum(added_edges)==sum(deleted_pair)+2)\nif args.deleted_edges is not None:model.add(sum(deleted_pair)==args.deleted_edges)')
s=s.replace("'exchange_edge_identity_imposed':True", "'exchange_edge_identity_imposed':True,'deleted_internal_edges':args.deleted_edges")
(H/'scripts/edit_neighbourhood.py').write_text(s,encoding='utf-8',newline='\n');(H/'scripts/branch.py').write_bytes(Path(__file__).read_bytes())
