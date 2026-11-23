// Insert coordinate d after interior path vertex i, retaining prefix [0,i]
// and translating the suffix [i,n) by 1<<d. Sweep occupation counts across i.
#define Q9_FIXED_BRIDGE_NO_DRIVER
#include "../search_q9_fixed_bridge.cpp"
#include <map>
#include <set>
string word(const vector<int>& p){string w=key(p);for(char& c:w)c+='0';return w;}
vector<int> decode(const string&w){vector<int>p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));return p;}
template<class F> void insertions(const vector<int>&p,int limit,F emit){
 int n=p.size();
 for(int d=0;d<9;d++){
   int mask=1<<d;vector<int>base{p.front()};
   for(int v:p)base.push_back(v^mask);
   Walk w(9,base);
   for(int i=1;i<n-1;i++){
     w.edit(p[i-1]^mask,-1);w.edit(p[i],1);
     if(w.E>limit) continue;
     vector<int>q(p.begin(),p.begin()+i+1);
     for(int j=i;j<n;j++)q.push_back(p[j]^mask);
     emit(q,w.E);
   }
 }
}
int main(int argc,char**argv){
 if(argc!=3)return 2;
 int target=stoi(argv[1]),cap=stoi(argv[2]);
 map<int,set<string>> banks;map<string,int> input;
 string s;
 while(cin>>s){auto p=decode(s);Walk w(9,p);w.verify();if(w.E)abort();input[word(p)]=0;}
 if(input.empty())return 3;
 int n=input.begin()->first.size();
 mt19937 gen(828812);
 for(int len=n+1;len<=target;len++){
   map<int,set<string>> found;
   const int limit=len==target?5:7;
   long long proposals=0;
   for(auto&[w,e]:input){
     auto p=decode(w);proposals+=9*(int(p.size())-2);
     insertions(p,limit,[&](const vector<int>&q,int cost){
       found[cost].insert(word(q));
     });
   }
   input.clear();int total=0;for(auto&[k,ws]:found)total+=ws.size();
   cout<<"LEVEL "<<len<<" evaluated "<<proposals<<" distinct "<<total;
   for(auto&[k,ws]:found)cout<<" "<<k<<"="<<ws.size();
   cout<<endl;
   for(auto&[cost,ws]:found){
     vector<string> rows(ws.begin(),ws.end());shuffle(rows.begin(),rows.end(),gen);
     for(auto&w:rows){
       if(cost<=3||(len==target&&cost==4))cout<<"PATH "<<len<<" "<<cost<<" "<<w<<"\n";
       if(int(input.size())<cap)input.emplace(w,cost);
     }
   }
   cout<<"RETAIN "<<len<<" "<<input.size()<<endl;
 }
}
