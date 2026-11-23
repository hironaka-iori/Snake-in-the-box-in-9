from pathlib import Path
r=Path(__file__).resolve().parent
s=(r/'mix.cpp').read_text()
start=s.index('    if (trials % reset == 0 && !bank.empty())')
end=s.index('    Trial t{p};',start)
s=s[:start]+'''    if (trials % reset == 0) {
       if (pick(4)==0 || front.empty()) p=initial;
       else {auto k=front.begin();advance(k,pick(front.size()));p=k->second[pick(k->second.size())];}
       auto now=getArms(p);shortOld=min(now[0].size(),now[1].size());
    }
    int old = p.nv, oldcc = p.cc;
'''+s[end:]
start=s.index('    double advantage = p.nv - old')
end=s.index('    if (ok && advantage < 0)',start)
s=s[:start]+'''    int cand=shortOld;
    bool ok=p.cc==2 && p.nv>=88;
    if(ok){
      int root=-1;
      for(int x=0;x<256;x++) if(p.live[x]&&popcount(unsigned(p.nb[x]))<2){root=x;break;}
      int now=root,prev=-1,n=0;
      while(now>=0){++n;int v=other(now,prev,p.nb[now]);prev=now;now=v;}
      cand=min(n,p.nv-n);
    }
    double advantage = p.nv-old-weight*(abs(cand-aim)-abs(shortOld-aim));
'''+s[end:]
s=s.replace('  save();\n  auto begin', '''  int aim=policy;
  double weight=.43;
  auto orig=getArms(initial); int shortOld=min(orig[0].size(),orig[1].size());
  map<int,vector<Pit>> front;map<int,int> heights;
  save();
  auto begin''')
s=s.replace('      ++accepted;','''      ++accepted;shortOld=cand;
      if(p.nv>=96 && p.nv>=heights[cand] && (trials%157==0 || heights[cand]<p.nv)){
         if(heights[cand]<p.nv){front[cand].clear();heights[cand]=p.nv;}
         auto &f=front[cand];if(f.size()<14)f.push_back(p);else f[pick(f.size())]=p;
      }''')
s=s.replace('  cerr << endl;\n}', '''  cerr << " heights";for(auto [x,n]:heights)if(n>=98)cerr<<" "<<x<<":"<<n;cerr<<endl;
}''')
(r/'target.cpp').write_text(s)

