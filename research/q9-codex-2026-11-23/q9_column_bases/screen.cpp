#include <algorithm>
#include <array>
#include <bitset>
#include <iostream>
#include <sstream>
#include <vector>
#include <random>
#include <cassert>
#include <set>
using namespace std;
using B=bitset<256>;
struct State{B one,two,three; State add(const B&h)const{return {one|h,two|(one&h),three|(two&h)};}};
struct Screen{
    B support;B near[256];vector<int> points,chosen,missing;
    vector<vector<int>> samples;mt19937 gen;int goal,k,quota;long long complete=0,passed=0;
    Screen(B s,int n,int cap,int seed):support(s),gen(seed),goal(n),k(n+1-(int)s.count()),quota(cap){
        for(int v=0;v<256;v++)if(s[v])points.push_back(v);
        for(int a=1;a<256;a++)for(int v:points)if(s[v^a])near[a].set(v);
    }
    bool eligible(const State& st){
        if((support&~st.three).count()<(size_t)k ||st.one!=support || (support&~st.two).count()>2)return false;
        int form=0;for(int f=1;f<256&&!form;f++){bool ok=true;for(int g:chosen)if(!__builtin_parity((unsigned)(g&f))){ok=false;break;}if(ok)form=f;}
        assert(form);int parity=0;for(int x:points)parity+=__builtin_parity((unsigned)(form&x));
        if(abs(2*parity-(int)points.size())>1)return false;
        // Low-degree sites induce a linear forest or even cycles, whose independence number is componentwise.
        B free=support&~st.three,seen;int alpha=0;
        for(int v:points)if(free[v]&&!seen[v]){vector<int>b{v};seen.set(v);bool end=false;
            for(size_t i=0;i<b.size();i++){int deg=0;for(int g:chosen)if(free[b[i]^g]){deg++;if(!seen[b[i]^g]){seen.set(b[i]^g);b.push_back(b[i]^g);}}if(deg<2)end=true;}
            alpha+=((int)b.size()+(end?1:0))/2;
        }
        if(alpha<k)return false;
        return true;
    }
    void add(int start,int need,int span,const State&s){
        if((support&~s.three).count()<(size_t)k)return;
        if(!need){complete++;if(!eligible(s))return;
            passed++;if(quota==0||(int)samples.size()<quota)samples.push_back(chosen);else{
                uniform_int_distribution<long long> dst(0,passed-1);long long idx=dst(gen);if(idx<quota)samples[(int)idx]=chosen;
            }return;
        }
        for(int g=start;g<256;g++){if(!(g&(g-1)))continue;int q=0;for(int j=0;j<(int)missing.size();j++)q|=((g>>missing[j])&1)<<j;
            if(span&(1<<q))continue;
            int expand=span;for(int j=0;j<(1<<(int)missing.size());j++)if(span&(1<<j))expand|=1<<(j^q);
            chosen.push_back(g);add(g+1,need-1,expand,s.add(near[g]));chosen.pop_back();
        }
    }
    void run(int repl){
        assert(repl<=3);
        if(k<0||k>(int)points.size())return;
        for(int mask=0;mask<256;mask++)if(__builtin_popcount((unsigned)mask)==8-repl){
            State st{};chosen.clear();missing.clear();for(int i=0;i<8;i++)if(mask&(1<<i)){chosen.push_back(1<<i);st=st.add(near[1<<i]);}else missing.push_back(i);
            add(1,repl,1,st);
        }
    }
};
int main(int argc,char**argv){if(argc!=4)return 2;int n=atoi(argv[1]),r=atoi(argv[2]),cap=atoi(argv[3]);string line;int row=0;
    while(getline(cin,line)){istringstream in(line);int v;B s;while(in>>v){assert(v>=0&&v<256);s.set(v);}
        Screen solver(s,n,cap,281+row);solver.run(r);
        for(auto &basis:solver.samples){cout<<"CASE "<<row;for(int a:basis)cout<<" "<<a;cout<<" support";for(int x:solver.points)cout<<" "<<x;cout<<"\n";}
        cout<<"END "<<row++<<" candidates "<<solver.complete<<" eligible "<<solver.passed<<" retained "<<solver.samples.size()<<endl;
    }}
