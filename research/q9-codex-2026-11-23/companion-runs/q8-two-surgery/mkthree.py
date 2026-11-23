from pathlib import Path
r=Path(__file__).resolve().parent;s=(r/'mix.cpp').read_text()
i=s.index('  map<int, vector<Pit>> bank;');e=s.index('  auto begin =',i)
s=s[:i]+'''  map<int,vector<Pit>> bank;
  set<M> seen;
  int best=0;long long checks=0,accepted=0,trials=0;
  auto save=[&](){
    if(p.cc!=3||p.nv<100)return;auto m=mask(p);if(seen.count(m))return;
    int ct=0;array<Path,3> a;bool vis[256]{};
    for(int x=0;x<256;x++)if(p.live[x]&&!vis[x]&&popcount(unsigned(p.nb[x]))<=1){a[ct++]=p.chain(x);for(int v:a[ct-1])vis[v]=true;}
    if(ct!=3)abort();int small=min({a[0].size(),a[1].size(),a[2].size()});int key=p.nv*100+small;auto&list=bank[key];
    if(list.size()>=60)return;list.push_back(p);seen.insert(m);best=max(best,p.nv);
    int off=a[0][0];for(auto&w:a){cout<<w.size();for(int x:w)cout<<" "<<(x^off);cout<<" ";}cout<<endl;};
  save();
'''+s[e:]
s=s.replace('abs(p.cc - 2) - abs(oldcc - 2)','abs(p.cc - 3) - abs(oldcc - 3)').replace('p.cc == 2','p.cc == 3').replace('p.nv >= 100','p.nv >= 100')
i=s.index('  cerr << "proposals');s=s[:i]+'''  cerr<<"proposals "<<trials<<" accepted "<<accepted<<" saved "<<seen.size()<<" best "<<best<<endl;
}
'''
(r/'three.cpp').write_text(s)

