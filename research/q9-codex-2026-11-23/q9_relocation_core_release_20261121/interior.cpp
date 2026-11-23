#define main original_cross_driver
#include "crossover.cpp"
#undef main
struct SetRange{
 vector<Mask> include,conflict;
 SetRange(const P&p,int cut,bool rev):include(193),conflict(193){for(int t=1;t<=192;t++){
  include[t]=include[t-1];conflict[t]=conflict[t-1];if(t<=cut)continue;int v=p[rev?192-t:t-1];put(include[t],v);put(conflict[t],v);
  for(int d=0;d<9;d++)put(conflict[t],v^(1<<d));
 }}
};
int main(){ifstream f("placements.txt");string line;array<vector<P>,120>paths;while(getline(f,line)){istringstream in(line);int rank,t,s,u,j,k,v;in>>rank>>t>>s>>u>>j>>k;P p;while(in>>v)p.push_back(v);paths[rank].push_back(p);}
 ifstream info("branches.txt");int rank,ep,y,nb,nf;
 while(info>>rank>>ep>>y>>nb>>nf){Search e;e.id=rank;Mask fixed{};int v;while(nb--){info>>v;e.ban[v]=1;}while(nf--){info>>v;put(fixed,v);}
  vector<Slice> slices;for(auto p:paths[rank])slices.emplace_back(p);set <pair<P,P>> seen;uint64_t fits=0,accepted=0,unique=0;
  for(int sa=0;sa<(int)slices.size()&&!e.found;sa++){
   const auto&A=slices[sa];vector<SetRange>left,right;const vector<int> trims={0,4,9,15};
   for(int cut:trims){left.emplace_back(A.p,cut,false);right.emplace_back(A.p,cut,true);}
   for(int sb=0;sb<(int)slices.size()&&!e.found;sb++)if(sa!=sb){auto&B=slices[sb];array<int,512>pos;pos.fill(-1);for(int k=0;k<192;k++)pos[B.p[k]]=k;
    Mask hard;for(int t=0;t<8;t++)hard[t]=fixed[t]&A.s[192][t]&B.s[192][t];put(hard,ep);put(hard,y);
    e.sa=sa;e.sb=sb;e.host1=A.s.back();e.host2=B.s.back();
    for(int i=1;i<190&&!e.found;i++)if(pos[A.p[i]]>=0)for(int j=i+2;j<191&&!e.found;j++)if(pos[A.p[j]]>=0){
     int k=pos[A.p[i]],l=pos[A.p[j]],lo=min(k,l),hi=max(k,l);if(hi-lo<2)continue;
     Mask middle;bool different=false;for(int t=0;t<8;t++){middle[t]=B.s[hi][t]^B.s[lo+1][t];different|=middle[t]!=(A.s[j][t]^A.s[i+1][t]);}if(!different)continue;
     for(int it=0;it<4;it++)for(int jt=0;jt<4;jt++){
      int lt=trims[it],rt=trims[jt];if(lt>=i||rt>=191-j||lt+rt>22)continue;
      int n=192-lt-rt+hi-lo-j+i;if(n<170||n>200)continue;fits++;
      if(intersects(middle,left[it].conflict[i])||intersects(middle,right[jt].conflict[191-j]))continue;
      Mask old;for(int t=0;t<8;t++)old[t]=left[it].include[i+1][t]|right[jt].include[192-j][t];if(!covers(old,middle,hard))continue;
      accepted++;P p(A.p.begin()+lt,A.p.begin()+i+1);for(int s=k+(l>k?1:-1);s!=l;s+=(l>k?1:-1))p.push_back(B.p[s]);
      p.insert(p.end(),A.p.begin()+j,A.p.end()-rt);if((int)p.size()!=n)abort();
      P needs;for(int u=0;u<512;u++)if(hard[u/64]>>(u%64)&1)needs.push_back(u);
      if(!seen.emplace(p,needs).second)continue;unique++;e.orient1=i;e.orient2=j;e.a=p;e.b.clear();e.mid.clear();for(int u:p)e.setv(u,1);e.extend(p.front(),p.back(),n-1,true);for(int u:p)e.setv(u,-1);
     }
    }
   }
  }cout<<"SEARCH "<<rank<<" "<<fits<<" "<<accepted<<" "<<unique<<" "<<e.tips<<" "<<e.maxlen<<endl;if(e.found)return 0;
 }
}
