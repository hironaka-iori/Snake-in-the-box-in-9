// Use the shape trie for the body, then grow both tips in either direction.
#define main rigid_main
#include "search_q9_free_bridge_join.cpp"
#undef main
#include <bitset>
int requested,cap,tipBest,bodyLimit;long long tipNodes=0,capped=0,pairsSeen=0;
set<string> seen,nearShapes;
string key(const Path&q){string best;for(int dir:{1,-1}){array<int,9>lab{};int n=0;string cur;
 for(int i=1;i<(int)q.size();i++){int j=dir==1?i:q.size()-i;int d=__builtin_ctz(q[j]^q[j-1]);
 if(!lab[d])lab[d]=++n;cur+=char('0'+lab[d]-1);}if(best.empty()||cur<best)best=cur;}return best;}
struct Grow{Path q;bitset<512> used;array<int,512> nb{};int spent=0;bool limited=false;
 void toggle(int v,int n){used[v]=n>0;for(int d=0;d<9;d++)nb[v^(1<<d)]+=n;}
 void visit(bool reversed){
 if(++spent>cap){limited=true;return;}int e=int(q.size())-1;tipBest=max(tipBest,e);
 if(e>=requested){if(!valid(q))abort();cout<<"FOUND";for(int v:q)cout<<" "<<v;cout<<endl;exit(0);}
 if(e==191 && nearShapes.insert(key(q)).second){ if(!valid(q))abort();cout<<"PATH191";for(int v:q)cout<<" "<<v;cout<<"\n";}
 for(int d=0;d<9;d++){int v=q.back()^(1<<d);if(used[v]||nb[v]!=1)continue;
 toggle(v,1);q.push_back(v);visit(reversed);q.pop_back();toggle(v,-1);if(limited)return;}
 if(!reversed){reverse(q.begin(),q.end());visit(true);reverse(q.begin(),q.end());}
 }};
void totals(){cout<<"TIP_RESULTS pairs "<<pairsSeen<<" distinct "<<seen.size()<<" capped "<<capped<<" nodes "<<tipNodes<<" best "<<tipBest<<" classes191 "<<nearShapes.size()<<endl;}
void both(){pairsSeen++;if(!seen.insert(key(p)).second)return;Grow g;g.q=p;for(int v:p)g.toggle(v,1);
 g.visit(false);capped+=g.limited;tipNodes+=g.spent;if(int(seen.size())>=bodyLimit){totals();exit(0);}}
int main(int argc,char**argv){if(argc!=10)return 2;requested=stoi(argv[7]);cap=stoi(argv[8]);bodyLimit=stoi(argv[9]);
 onPair=both;int result=rigid_main(7,argv);totals();return result;}
