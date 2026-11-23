// Each successful hinge re-embedding has at most one global chord.
#define Q9_FIXED_BRIDGE_NO_DRIVER
#include "search_q9_fixed_bridge.cpp"
#include <deque>
struct Bank{
 unordered_set<string>seen;deque<vector<int>>front;ofstream out;long long leaves=0,nodes=0;
 Bank(const char*path):out(path){}
 bool observe(const vector<int>&w,int c){
  if(c==0){Walk t(9,w);t.verify();if(t.E!=0)abort();cout<<"FOUND";for(int x:w)cout<<" "<<x;cout<<endl;return true;}
  if(seen.insert(key(w)).second){Walk t(9,w);t.verify();if(t.E!=1)abort();front.push_back(w);for(int i=0;i<(int)w.size();i++)out<<(i?" ":"")<<w[i];out<<endl;}
  return false;
 }
};
struct Permute{
 const vector<int>&p;int cut,anchor,fixed_axes=0,num=0,internal;
 Bank&bank;
 array<int,512>cost{},mapped{};
 array<int,9>axis{},prior{};
 array<vector<int>,9>ready;
 Permute(const vector<int>&p_,int k,int inherited,Bank&b):p(p_),cut(k),anchor(p[k]),internal(inherited),bank(b){
  int moving_axes=0;
  for(int i=0;i<=cut;++i){int v=p[i]^anchor;fixed_axes|=v;if(i<cut)for(int d=0;d<9;d++)cost[v^(1<<d)]++;}
  for(int i=0;i<=cut;++i)cost[p[i]^anchor]=9;
  vector<int>suffix;for(int i=cut+1;i<(int)p.size();i++){suffix.push_back(p[i]^anchor);moving_axes|=suffix.back();}
  int assigned=0;
  while(assigned!=moving_axes){
   int choice=-1,score=-1;
   for(int d=0;d<9;d++)if((moving_axes&~assigned)&(1<<d)){
    int next=assigned|(1<<d),rating=0;for(int x:suffix)rating+=(x&~next)==0;
    if(rating>score){choice=1<<d;score=rating;}
   }
   prior[num]=assigned;axis[num]=choice;assigned|=choice;
   for(int x:suffix)if((x&choice)&&!(x&~assigned))ready[num].push_back(x);
   num++;
  }
 }
 bool visit(int depth,int free,int bad){
  bank.nodes++;
  if(depth==num){
   bank.leaves++;vector<int>w=p;for(int i=cut+1;i<(int)p.size();i++)w[i]=anchor^mapped[p[i]^anchor];return bank.observe(w,bad);
  }
  bool tried_unseen=false;
  for(int f=free;f;f&=f-1){
   int target=f&-f;
   if(!(target&fixed_axes)){if(tried_unseen)continue;tried_unseen=true;}
   for(int t=prior[depth];;t=(t-1)&prior[depth]){mapped[t|axis[depth]]=target|mapped[t];if(!t)break;}
   int b=bad;for(int v:ready[depth]){b+=cost[mapped[v]];if(b>1)break;}
   if(b<=1&&visit(depth+1,free^target,b))return true;
  }
  return false;
 }
};
#ifndef Q9_PERM_CLOSURE_NO_MAIN
int main(int argc,char**argv){
 if(argc!=3 && argc!=4)return 2;int limit=stoi(argv[1]);Bank bank(argv[2]);if(!bank.out)return 3;
 string line;if(argc==4){ifstream prior(argv[3]);if(!prior)return 5;
    while(getline(prior,line)){istringstream in(line);vector<int>p;int x;while(in>>x)p.push_back(x);if(!p.empty())bank.seen.insert(key(p));}}
 while(getline(cin,line)){istringstream in(line);vector<int>p;int v;while(in>>v)p.push_back(v);if(p.empty())continue;Walk t(9,p);t.verify();if(t.E!=1)return 4;bank.observe(p,1);}
 int expanded=0;long long cuts=0;
 while(!bank.front.empty()&&expanded<limit){
  auto p=move(bank.front.front());bank.front.pop_front();int n=p.size();
  int x=-1,y=-1;for(int i=0;i<n;i++)for(int j=i+2;j<n;j++)if(popcount(unsigned(p[i]^p[j]))==1){x=i;y=j;}
  for(int orientation=0;orientation<2;orientation++){
   for(int i=(n-1)/2;i<n-1;i++){
    if(orientation==1&&2*i==n-1)continue;
    int inherited=(y<=i||x>=i);
    Permute res(p,i,inherited,bank);cuts++;if(res.visit(0,511,inherited))return 0;
   }
   reverse(p.begin(),p.end());int z=n-1-y;y=n-1-x;x=z;
  }
  if(++expanded%20==0)cout<<"CHECK "<<expanded<<" bank "<<bank.seen.size()<<" pending "<<bank.front.size()<<" cuts "<<cuts<<" nodes "<<bank.nodes<<" leaves "<<bank.leaves<<endl;
 }
 cout<<"DONE "<<expanded<<" bank "<<bank.seen.size()<<" pending "<<bank.front.size()<<" cuts "<<cuts<<" nodes "<<bank.nodes<<" leaves "<<bank.leaves<<endl;
}

#endif
