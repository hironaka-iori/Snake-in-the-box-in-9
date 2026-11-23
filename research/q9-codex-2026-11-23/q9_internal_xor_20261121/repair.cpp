#define Q9_FIXED_BRIDGE_NO_DRIVER
#include "../search_q9_fixed_bridge.cpp"
#include <map>
#include <set>
string word(const vector<int>& p){string w=key(p);for(char& c:w)c+='0';return w;}
int main(int argc,char**argv){
 if(argc!=5)return 2;
 int epochs=stoi(argv[1]),steps=stoi(argv[2]),goal=stoi(argv[3]);Search s{mt19937_64(stoul(argv[4]))};
 vector<vector<int>>starts;map<int,set<string>> saved;string t;
 while(cin>>t){
    if(t!="PATH"){getline(cin,t);continue;}int n,e;cin>>n>>e>>t;
    if(n!=goal||e>4)continue;
    vector<int>p{0};for(char c:t)p.push_back(p.back()^(1<<(c-'0')));
    Walk w(9,p);w.verify();if(w.E!=e)abort();starts.push_back(p);
 }
 if(starts.empty())return 3;
 long long bridges=0,accepted=0;int best=999;
 for(int a=0;a<epochs;a++){
    auto p=starts[a%starts.size()];Walk w(9,p);
    for(int j=0;j<steps;j++){
      if(w.E<best){best=w.E;cout<<"BEST "<<a<<" "<<j<<" "<<best<<endl;}
      if(w.E<=3){
        string k=word(w.p);
        if(saved[w.E].insert(k).second){w.verify();cout<<"NEAR "<<w.E<<" "<<k<<"\n";}
        if(!w.E){cout<<"FOUND "<<k<<endl;return 0;}
      }
      if(j%45==0){Bridge b{s,w};bridges+=b.run(min(w.E+int(s.pick(5)==0),6),800);}
      else accepted+=s.move(w,.07+.29*(1.-(j%700)/700.));
    }
    if(a%64==63)cout<<"AT "<<a+1<<" "<<best<<" "<<accepted<<" "<<bridges<<endl;
 }
 cout<<"DONE "<<epochs<<" "<<steps<<" "<<best<<" "<<accepted<<" "<<bridges<<endl;
}
