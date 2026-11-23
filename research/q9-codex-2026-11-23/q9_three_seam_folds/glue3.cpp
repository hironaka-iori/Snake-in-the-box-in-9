#include "fold_common.hpp"
using Mask=array<unsigned long long,8>;
void mark(Mask&m,int v){m[v>>6]|=1ULL<<(v&63);}
bool overlaps(const Mask&a,const Mask&b){for(int k=0;k<8;k++)if(a[k]&b[k])return true;return false;}
struct Placement{Mask pts{},near{};string w;};
struct All{
 const string& wing;array<int,9> map;array<bool,512> ban{};int used=0;uint64_t nodes=0;vector<Placement> list;string word;int offset;int cap;bool cut=false;
 All(const string& mid,const string&r,int origin,int limit):wing(r),offset(origin),cap(limit){map.fill(-1);word.resize(r.size());auto p=vertices(mid);for(int j=1;j<p.size();j++){int x=p[j];ban[x]=true;for(int b=1;b<512;b*=2)ban[x^b]=true;}}
 void visit(int i,int v){
  if(cut)return;if(i==wing.size()){Placement p;p.w=word;int x=offset;for(char c:word){x^=1<<(c-'A');mark(p.pts,x);mark(p.near,x);for(int b=1;b<512;b*=2)mark(p.near,x^b);}list.push_back(move(p));if(list.size()>=cap)cut=true;return;}
  int id=wing[i]-'A';int old=map[id];if(old>=0){int x=v^(1<<old);if(ban[x])return;word[i]='A'+old;visit(i+1,x);return;}
  nodes++;for(int d=0;d<9&&!cut;d++)if(!(used&(1<<d))){int x=v^(1<<d);if(ban[x])continue;word[i]='A'+d;map[id]=d;used^=1<<d;visit(i+1,x);used^=1<<d;map[id]=-1;}
 }
};
struct Stats{uint64_t wins=0,unique=0,folds=0,mid=0,solves=0,cuts=0,nodes=0,placements=0,both=0,pairs=0,hits=0;} st;
Bank bank;int cap,goal;vector<string>raw;unordered_set<string>handled;
bool join(int row,int start,int n1,int n2,bool ctl){
 const string&w=raw[row];string l=w.substr(start,n1),mid=w.substr(start+n1,n2),r=w.substr(start+n1+n2,goal-n1-n2);reverse(l.begin(),l.end());
 auto ls=bank.alternatives(l),ms=bank.alternatives(mid),rs=bank.alternatives(r);
 st.wins++;if(ls.empty()||ms.empty()||rs.empty())return false;string identity=canonical(l)+" "+canonical(mid)+" "+canonical(r);
 if(!ctl&&!handled.insert(identity).second)return false;st.unique++;st.folds+=ls.size()*ms.size()*rs.size();
 for(auto &m:ms){st.mid++;string rev(m.rbegin(),m.rend());int end=vertices(m).back();
 vector<Placement>a,b;auto collect=[&](const vector<string>&ws,const string&center,int offset,vector<Placement>&out){for(auto&s:ws){All g(center,s,offset,cap);g.visit(0,0);st.solves++;st.cuts+=g.cut;st.nodes+=g.nodes;st.placements+=g.list.size();out.insert(out.end(),make_move_iterator(g.list.begin()),make_move_iterator(g.list.end()));}};
 if(n1>=r.size()){collect(ls,m,0,a);if(a.empty())continue;collect(rs,rev,end,b);}else{collect(rs,rev,end,b);if(b.empty())continue;collect(ls,m,0,a);}
 if(a.empty()||b.empty())continue;st.both++;
 for(auto&A:a)for(auto&B:b){st.pairs++;if(overlaps(A.near,B.pts))continue;string result(A.w.rbegin(),A.w.rend());result+=m;result+=B.w;Path p=vertices(result);assert(valid(p)&&p.size()==goal+1);st.hits++;
 cout<<"HIT "<<row<<" "<<start<<" "<<n1<<" "<<n2<<" "<<goal<<" "<<result;for(int x:p)cout<<" "<<x;cout<<endl;return true;}
 }return false;
}
int main(int argc,char**argv){assert(argc==9);ifstream f(argv[1]);goal=stoi(argv[2]);int lo=stoi(argv[3]),hi=stoi(argv[4]),grid=stoi(argv[5]),stride=stoi(argv[6]);cap=stoi(argv[7]);bool ctl=stoi(argv[8]);string line;while(getline(f,line)){istringstream in(line);int dimension;in>>dimension;if(dimension!=10)continue;Path p;int x;while(in>>x)p.push_back(x);assert(valid(p));string w;for(int i=1;i<p.size();i++)w+='A'+countr_zero(unsigned(p[i]^p[i-1]));raw.push_back(w);}
 for(int row=0;row<raw.size();row++){
  for(int start=0;start+goal<=raw[row].size();start+=stride){for(int a=lo;a<=hi;a+=grid){for(int b=lo;b<=hi;b+=grid){int c=goal-a-b;if(c<lo||c>hi||c<=0)continue;if(join(row,start,a,b,ctl)&&!ctl)goto done;}}}
  cout<<"ROW "<<row<<" "<<st.wins<<" "<<st.unique<<" "<<st.nodes<<" "<<st.placements<<" "<<st.pairs<<" "<<st.cuts<<" "<<st.hits<<endl;
 }done:cout<<"DONE windows "<<st.wins<<" distinct_nonempty "<<st.unique<<" fold_triples "<<st.folds<<" middles "<<st.mid<<" placement_enums "<<st.solves<<" assignment_nodes "<<st.nodes<<" accepted_placements "<<st.placements<<" two_wings "<<st.both<<" cross_tests "<<st.pairs<<" capped "<<st.cuts<<" hits "<<st.hits<<endl;}
