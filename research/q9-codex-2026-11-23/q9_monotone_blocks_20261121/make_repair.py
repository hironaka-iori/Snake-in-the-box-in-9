from pathlib import Path
D=Path(__file__).resolve().parent
s=(D/'partition.cpp').read_text()
s=s.replace('struct Whole:Fit{','''struct Whole:Fit{
 int holes=1,retired=0;long long filltries=0;
 bool fill(bitset<512> ss,int remain,vector<int>&p,vector<int>&inserted){
    ++filltries;array<int,512> deg{};int ep=0,root=-1;bitset<512>opts;
    for(int v=0;v<512;v++)if(ss[v]){for(int k=0;k<9;k++)deg[v]+=ss[v^(1<<k)];if(deg[v]>2)return false;ep+=2-deg[v];if(deg[v]==1)root=v;if(deg[v]<2)for(int k=0;k<9;k++)opts.set(v^(1<<k));}
    if(ep>2+2*remain||ep<2)return false;
    if(!remain){if(ep!=2||root<0)return false;p={root};int prev=-1;while(true){int dest=-1;for(int k=0;k<9;k++){int t=p.back()^(1<<k);if(t!=prev&&ss[t]){dest=t;break;}}if(dest<0)break;prev=p.back();p.push_back(dest);}return p.size()==ss.count();}
    opts&=~ss;for(int v=0;v<512;v++)if(opts[v]){int nn=0;bool ok=true;for(int k=0;k<9;k++){int u=v^(1<<k);if(ss[u]){nn++;if(deg[u]>=2)ok=false;}}if(!ok||nn>2||nn<1)continue;ss.set(v);inserted.push_back(v);if(fill(ss,remain-1,p,inserted))return true;inserted.pop_back();ss.reset(v);}return false;
 }
 void buildLoose(int a,int c){auto&A=b[a],&C=b[c];for(int k=0;k<5040;k++){const auto&f=lut[k];for(int t=0;t<128;t++){++mapChecks;Mask ma,mc;bool ok=true;for(int v:C.vs){int u=f[v]^t;if(!A.points[u])continue;if(A.two[u]||C.two[v]){ok=false;break;}ma.set(u);mc.set(v);}if(!ok||(A.zero&~ma).count()+(C.zero&~mc).count()>2+2*holes)continue;Map chart{k,t};edge[a][c].push_back({chart,ma,mc});++pairOK;}}}
''')
s=s.replace('int sum=L.demand+R.demand-2;if(sum%2)return false;','for(int deficit=2;deficit<=2+2*holes;deficit+=2){int sum=L.demand+R.demand-deficit;if(sum%2)continue;')
s=s.replace('if(m<=0||eL<0','if(m<0||eL<0').replace('eR<(int)R.iso.size())return false;','eR<(int)R.iso.size())continue;')
s=s.replace('vector<int>anch=L.iso;if(anch.empty())anch=L.ports;anch.resize(L.iso.empty()?missL+1:1);','vector<int>anch=L.ports;if(m)anch.resize(missL+1);')
s=s.replace('bitset<256>tried;for(int u:anch)for(int v:R.ports){int t=u^img[v];if(tried[t])continue;tried.set(t);++candidates;', 'bitset<256>tried;if(!m)tried.set();else for(int u:anch)for(int v:R.ports)tried.set(u^img[v]);for(int t=0;t<256;t++)if(tried[t]){++candidates;')
s=s.replace('if(deg<0&&(R.deg[x]==0||++missed>missR))','if(deg<0&&++missed>missR)')
s=s.replace('if(!ok)continue;for(int x:L.iso)if(!right[x]){ok=false;break;}if(!ok)continue;', 'if(!ok)continue;')
start=s.index(' int start=-1,tips=0;');end=s.index(' cout<<"HIT "',start)
s=s[:start]+''' vector<int>p,inserted;if(!fill(sel,holes,p,inserted)){++disconnected;continue;}++succeeded;
'''+s[end:]
s=s.replace("<<pi<<' '<<t;for(int x:p)","<<pi<<' '<<t<<' '<<holes;for(int q:inserted)cout<<' '<<q;for(int x:p)")
s=s.replace('}}return false;\n }','}}}return false;\n }',1)
s=s.replace('build(0,j);build(c,d);','buildLoose(0,j);buildLoose(c,d);')
s=s.replace('if(argc!=3)return 2;array<int,7>p;','if(argc!=4)return 2;array<int,7>p;').replace('Whole s;ifstream f(argv[1]);','Whole s;s.holes=stoi(argv[3]);ifstream f(argv[1]);').replace('if(s.run(seq)&&seq.size()>=193)','if(s.run(seq)&&seq.size()+s.holes>=193)').replace('<<" hits "<<s.succeeded','<<" fill_nodes "<<s.filltries<<" hits "<<s.succeeded')
(D/'repairfaces.cpp').write_text(s)
