#define main anneal_main
#include "coupled.cpp"
#undef main
#include <sstream>
struct Entry{State s;string order;};struct D{U mask;int n;};using Dom=array<vector<D>,16>;
int goal,limit,used,choice[16];uint64_t cutLength=0,cutEmpty=0,cutAC=0,check=0,branches=0;
State fixedS,found;uint64_t treeCuts=0;
U required(int i,int j){return j==i+1?1u<<fixedS.p[j]:j==i-1?1u<<fixedS.p[i]:0;}
int treeUB(const Dom&dom,int type){
 array<vector<int>,16> val;int parent[16],order[16],len=1;fill(parent,parent+16,-1);order[0]=type==0?0:(3*type)%16;parent[order[0]]=order[0];
 if(type==0){for(int i=1;i<16;i++)parent[i]=i-1,order[i]=i;len=16;}
 else for(int pos=0;pos<len;pos++){int i=order[pos];for(int z=0;z<4;z++){int j=adj[i][(z+type)%4];if(parent[j]<0)parent[j]=i,order[len++]=j;}}
 for(int i=0;i<16;i++)for(auto c:dom[i])val[i].push_back(c.n);
 for(int pos=15;pos>0;pos--){int j=order[pos],i=parent[j];vector<int> idx(dom[j].size());for(int n=0;n<idx.size();n++)idx[n]=n;
  sort(idx.begin(),idx.end(),[&](int a,int b){return val[j][a]>val[j][b];});U is=required(i,j);
  for(int a=0;a<dom[i].size();a++){int best=-9999;for(int b:idx){if((dom[i][a].mask&dom[j][b].mask)==is){best=val[j][b];break;}}val[i][a]+=best;}
 }return *max_element(val[order[0]].begin(),val[order[0]].end());
}
int dfs(Dom dom){
 if(++used>limit)return -1;branches++;bool change=true;
 while(change){change=false;int tops[16],sum=0;for(int i=0;i<16;i++){
   if(dom[i].empty()){cutEmpty++;return 0;}tops[i]=dom[i][0].n;sum+=tops[i];}
  if(sum<goal){cutLength++;return 0;}
  for(int i=0;i<16;i++){auto&v=dom[i];while(v.back().n<tops[i]-(sum-goal)){v.pop_back();change=true;}}
  for(int i=0;i<16;i++){for(int d=0;d<4;d++){int j=adj[i][d];U isec=required(i,j);auto&v=dom[i];auto e=remove_if(v.begin(),v.end(),[&](D p){for(auto q:dom[j]){check++;if((p.mask&q.mask)==isec)return false;}return true;});
   if(e!=v.end()){v.erase(e,v.end());change=true;if(v.empty()){cutAC++;return 0;}}}}
 }
 for(int mode=0;mode<(used==1?5:2);mode++)if(treeUB(dom,mode)<goal){treeCuts++;return 0;}
 int ix=-1;for(int i=0;i<16;i++)if(dom[i].size()>1&&(ix<0||dom[i].size()<dom[ix].size()))ix=i;
 if(ix<0){found=fixedS;for(int i=0;i<16;i++)found.m[i]=dom[i][0].mask;return 1;}
 auto choices=dom[ix];auto prior=find_if(choices.begin(),choices.end(),[&](D c){return c.mask==fixedS.m[ix];});if(prior!=choices.end())iter_swap(choices.begin(),prior);for(auto c:choices){auto tmp=dom;tmp[ix]={c};int r=dfs(move(tmp));if(r)return r;}return 0;
}
int solve(State s){
 fixedS=s;Dom dom;for(int i=0;i<16;i++){U forbidden=0;for(int d=0;d<4;d++){int j=adj[i][d];forbidden|=((1u<<s.p[j])|(1u<<s.p[j+1]))&~required(i,j);}
 int rt=s.p[i],end=s.p[i+1];for(int id:cat[rt^end]){U m=shifted[rt][id];if(!(m&forbidden))dom[i].push_back({m,rows[id].n});}
 stable_sort(dom[i].begin(),dom[i].end(),[](auto&a,auto&b){return a.n>b.n;});}
 used=0;return dfs(move(dom));
}
int main(int argc,char**argv){if(argc!=6)return 2;goal=stoi(argv[2]);limit=stoi(argv[3]);int changes=stoi(argv[4]),cap=stoi(argv[5]);ifstream f(argv[1]);vector<Entry>bank;string line;
 while(getline(f,line)){istringstream is(line);string tag;Entry e;int c,n;is>>tag;if(tag!="STATE")continue;is>>e.order>>c>>n;for(int i=0;i<16;i++)is>>e.s.m[i]>>e.s.p[i];is>>e.s.p[16];bank.push_back(e);}
 for(int x=0;x<32;x++)for(int d=0;d<5;d++)nbs[x]|=1u<<(x^(1<<d));gen(0,1,0);for(int x=0;x<32;x++)for(auto r:rows)shifted[x].push_back(shift(r.m,x));
 int exact=0,bounded=0,global=0;for(int ei=0;ei<bank.size();ei++){auto z=bank[ei];auto w=z.order;gray[0]=0;int ix[16];for(int k=0;k<15;k++)gray[k+1]=gray[k]^(1<<(w[k]-'0'));for(int k=0;k<16;k++)ix[gray[k]]=k;for(int k=0;k<16;k++)for(int d=0;d<4;d++)adj[k][d]=ix[gray[k]^(1<<d)];
  int cnt=changes==0?1:(changes==1?528:cap);for(int t=0;t<cnt;t++){auto s=z.s;if(changes==1&&t){int u=(t-1)/31,delta=1+(t-1)%31;s.p[u]^=delta;}if(changes>1){int a=rnd()%17,b=rnd()%16;if(b>=a)++b;s.p[a]^=1+rnd()%31;s.p[b]^=1+rnd()%31;}
   int ans=solve(s);if(ans==1){writeBest(found,w,ei,t);return 0;}if(ans<0)bounded++;else exact++;}
  cout<<"BANK "<<ei<<" "<<exact<<" "<<bounded<<" "<<branches<<" "<<check<<endl;
 }cout<<"DONE target "<<goal<<" change "<<changes<<" exact "<<exact<<" bounded "<<bounded<<" nodes "<<branches<<" pairchecks "<<check<<" length "<<cutLength<<" empty "<<cutEmpty<<" ac "<<cutAC<<" tree "<<treeCuts<<endl;
}
