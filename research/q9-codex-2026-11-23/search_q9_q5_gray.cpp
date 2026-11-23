// Construct in Q4 x Q5 by visiting every Q5 fibre once along a Q4 Hamilton path.
#define main chain_relax_cli
#include "search_q9_q5_chain.cpp"
#undef main
#include <random>
#include <unordered_map>
#include <unordered_set>
struct Runner{
 struct State{array<U,16> masks{};array<int,16> record{};int end=0,total=0,lastShape=-1;};
 mt19937 rng;int goal,width,best=0;
 array<int,16> gray{},index{};vector<vector<int>> future;
 vector<vector<int>> lengths;vector<int> bySize;
 array<vector<Row>,32> placed;
 Runner(int g,int w,int seed):rng(seed),goal(g),width(w){}
 void init(){
  for(int x=0;x<32;x++)for(int d=0;d<5;d++)nb[x]|=U(1)<<(x^(1<<d));
  array<int,5>p{0,1,2,3,4};do{array<int,32>img{};
   for(int x=1;x<32;x++)img[x]=img[x&(x-1)]|(1<<p[countr_zero(unsigned(x))]);group.push_back(img);
  }while(next_permutation(p.begin(),p.end()));
  collect(0,1,0);
  for(int x=0;x<32;x++)for(auto &r:rows)placed[x].push_back({translate(r.mask,x),r.end^x,r.n,r.shape});
  bySize.resize(rows.size());iota(bySize.begin(),bySize.end(),0);
  stable_sort(bySize.begin(),bySize.end(),[](int a,int b){return rows[a].n>rows[b].n;});
  future.assign(16,vector<int>(rep.size()));
  for(int i=0;i<rep.size();i++){
   auto &r=rows[rep[i]];U blocked=translate(r.mask,r.end)&~U(1);vector<char>used(rep.size());vector<int> choices;
   for(auto& b:rows)if(!(b.mask&blocked)&&!used[b.shape]){choices.push_back(b.shape);used[b.shape]=1;}
   lengths.push_back(choices);
  }
  for(int n=1;n<16;n++)for(int a=0;a<rep.size();a++){
   int b=0;for(int j:lengths[a])b=max(b,rows[rep[j]].n+future[n-1][j]);future[n][a]=b;
  }
 }
 bool grayOrder(int depth,unsigned used){
  if(depth==16)return true;
  array<int,4> ds{0,1,2,3};shuffle(ds.begin(),ds.end(),rng);
  for(int d:ds){int v=gray[depth-1]^(1<<d);if((used>>v)&1)continue;gray[depth]=v;
   if(grayOrder(depth+1,used|(1<<v)))return true;
  }return false;
 }
 int openCapacity(U allowed){
  // Bound by the bipartite colour split of each connected component.
  int best=0;U todo=allowed;
  while(todo){U reach=todo&-todo,front=reach;todo&=~reach;
   while(front){U nx=0;for(U s=front;s;s&=s-1)nx|=nb[countr_zero(s)];front=nx&todo;todo&=~front;reach|=front;}
   int b=0,w=0;for(U s=reach;s;s&=s-1)(popcount(unsigned(countr_zero(s)))%2?b:w)++;
   best=max(best,min({14,b+w,2*min(b,w)+1}));
  }return best;
 }
 void emit(const State&s,int k){
  vector<int>out;int start=0;
  for(int l=0;l<=k;l++){auto &r=placed[start][s.record[l]];int cur=start,prev=-1;
   for(int j=0;j<r.n;j++){out.push_back(gray[l]*32+cur);int next=-1;
    for(int d=0;d<5;d++){int y=cur^(1<<d);if(y!=prev&&(r.mask&(1u<<y))){next=y;break;}}
    prev=cur;cur=next;
   }start=r.end;
  }
  for(int i=0;i<out.size();i++)for(int j=0;j<i;j++)if(out[i]==out[j]||has_single_bit(unsigned(out[i]^out[j]))!=(i==j+1))abort();
  cout<<(out.size()>=193?"FOUND ":"BEST ")<<out.size()-1;for(int v:out)cout<<" "<<v;cout<<endl;
 }
 bool run(int attempt){
  gray[0]=0;if(!grayOrder(1,1))abort();for(int j=0;j<16;j++)index[gray[j]]=j;
  vector<State> beam(1);
  int floor=goal;
  for(int k=0;k<16;k++){
   struct Pick{double score;State s;};
   vector<Pick> candidates;unordered_set<uint64_t> keys;
   vector<int> sizes;
   for(const auto&st:beam){
    U blocked=0;for(int d=0;d<4;d++){
     int j=index[gray[k]^(1<<d)];if(j<k)blocked|=j==k-1?(st.masks[j]&~(U(1)<<st.end)):st.masks[j];
    }
    if(blocked&(U(1)<<st.end))continue;
    vector<int> options;
    if(k==0)options=rep;else{
      // Generate directly inside the allowed column component.
      auto gen=[&](auto&&self,int x,U mask,U denied)->void{
        if(popcount(mask)>=3){int shape=label.at({translate(mask,st.end),x^st.end});
         if(st.total+popcount(mask)+future[15-k][shape]>=floor){
            auto pos=rowId.find({translate(mask,st.end),x^st.end});options.push_back(pos->second);
         }}
        for(U nx=nb[x]&~(denied|mask|blocked);nx;nx&=nx-1){int y=countr_zero(nx);self(self,y,mask|(U(1)<<y),denied|nb[x]);}
      };gen(gen,st.end,U(1)<<st.end,0);
    }
    for(int id:options){
     auto &r=placed[st.end][id];int total=st.total+r.n,ub=total+future[15-k][r.shape];
     if(ub<floor)continue;
     State n=st;n.masks[k]=r.mask;n.record[k]=id;n.total=total;n.end=r.end;n.lastShape=r.shape;
     if(k>=12&&total-1>best){best=total-1;emit(n,k);if(best>=192)return true;}
     int cap=total;
     for(int j=k+1;j<16;j++){
        U no=0;for(int d=0;d<4;d++){
           int a=index[gray[j]^(1<<d)];if(a<=k)no|=a+1==j?n.masks[a]&~(U(1)<<n.end):n.masks[a];
        }
        cap+=openCapacity(~no);
     }
     if(cap<floor)continue;
     uint64_t hash=1469598103934665603ull;for(int j=0;j<=k;j++)hash=(hash^n.masks[j])*1099511628211ull;
     hash^=n.end;if(!keys.insert(hash).second)continue;
     double jitter=double(rng())/rng.max()*5;
     candidates.push_back({total+0.9*min(ub,cap)+0.2*cap+jitter,n});
    }
   }
   if(candidates.empty())break;
   auto cmp=[](const Pick& a,const Pick& b){return a.score>b.score;};
   if(candidates.size()>width){nth_element(candidates.begin(),candidates.begin()+width,candidates.end(),cmp);candidates.resize(width);}
   beam.clear();for(auto &c:candidates)beam.push_back(c.s);
  }return false;
 }
 map<pair<U,int>,int> rowId;
};
#ifndef Q9_GRAY_LIBRARY
int main(int argc,char**argv){
 if(argc!=5)return 2;Runner x(stoi(argv[1]),stoi(argv[2]),stoi(argv[4]));x.init();
 for(int i=0;i<rows.size();i++)x.rowId[{rows[i].mask,rows[i].end}]=i;
 for(int k=0;k<stoi(argv[3]);k++){
  if(x.run(k))return 0;if(k%25==0)cout<<"AT "<<k+1<<" best_edges "<<x.best<<endl;
 }cout<<"DONE best_edges "<<x.best<<endl;
}
#endif
