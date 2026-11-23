from pathlib import Path
r=Path(__file__).resolve().parent;s=(r/'tripleiso.cpp').read_text().replace('void emit(){','void finalEmit(){',1);i=s.index('void dfs(')
s=s[:i]+'''P otherArm,csteps;int mapping[8],freeAxes;long long built=0,packedNodes=0;using CacheKey=pair<M,P>;set<CacheKey> tried;
void pack(int v,int ix){++packedNodes;
 if(ix==csteps.size()){swap(c,otherArm);finalEmit();swap(c,otherArm);return;}
 int d=csteps[ix],opts=mapping[d]<0?freeAxes:1<<mapping[d];
 while(opts){int w=opts&-opts;opts^=w;int y=v^w;if(occ[y]||deg[y])continue;bool fresh=mapping[d]<0;if(fresh){mapping[d]=countr_zero((unsigned)w);freeAxes^=w;}otherArm.push_back(y);pack(y,ix+1);otherArm.pop_back();if(fresh){freeAxes^=w;mapping[d]=-1;}}
}
void emit(){++built;M m{};for(auto*p:{&a,&append})for(int x:*p)m[x/64]|=1ull<<(x%64);if(tried.size()>2000000)tried.clear();if(!tried.insert({m,csteps}).second)return;
 for(int x:append)mark(x,1);fill(mapping,mapping+8,-1);freeAxes=255;for(int src=0;src<256;src++)if(!occ[src]&&!deg[src]){otherArm={src};pack(src,0);}for(int x:append)mark(x,-1);
}
'''+s[i:]
s=s.replace('if(n<target)continue;','if(n<target||a.size()+b.size()-k<50||c.size()<2)continue;csteps.clear();for(int h=1;h<c.size();h++)csteps.push_back(countr_zero(unsigned(c[h]^c[h-1])));')
s=s.replace('for(auto*p:{&a,&c})for(int x:*p)mark(x,1);','for(int x:a)mark(x,1);').replace('for(auto*p:{&a,&c})for(int x:*p)mark(x,-1);','for(int x:a)mark(x,-1);')
s=s.replace('<<" saved "<<answers','<<" formed joined arms "<<built<<" third arm nodes "<<packedNodes<<" saved "<<answers')
(r/'independent.cpp').write_text(s)

