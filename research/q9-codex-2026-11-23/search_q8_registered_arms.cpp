#define main old_q8_join_cli
#include "search_q8_bank_join.cpp"
#undef main
#include <map>
#include <sstream>
#include <cassert>
using namespace std;
using P=vector<int>;
string canonicalWord(string w){
 array<int,8> m;m.fill(-1);int next=0;for(char&c:w){int d=c-'0';if(m[d]<0)m[d]=next++;c='0'+m[d];}return w;
}
string shape(const P& p){
 string w;for(int i=1;i<p.size();i++)w+='0'+countr_zero(unsigned(p[i]^p[i-1]));
 auto normalize=[](string s){array<int,9> m;m.fill(-1);int k=0;for(auto &c:s){int d=c-'0';if(m[d]<0)m[d]=k++;c='0'+m[d];}return s;};
 string a=normalize(w);reverse(w.begin(),w.end());return min(a,normalize(w));
}
struct Library{
 vector<P> arms;array<vector<uint64_t>,256> banned;int chunks=0;
 void prepare(){
    chunks=(arms.size()+63)/64;for(auto& b:banned)b.assign(chunks,0);
    for(int id=0;id<arms.size();id++)for(int x:arms[id])if(x)banned[x][id/64]|=uint64_t(1)<<(id%64);
 }
};
P decode(string w){
 P p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));
 for(int i=0;i<p.size();i++)for(int j=0;j<i;j++){
    int d=popcount(unsigned(p[i]^p[j]));assert(p[i]<256 && d>0&&((d==1)==(i==j+1)));
 }return p;
}
int main(int argc,char**argv){
 if(argc!=5)return 2;ifstream old(argv[1]),fresh(argv[2]),reference(argv[3]);ofstream out(argv[4]);if(!old||!fresh||!reference||!out)return 2;
 string w;map<int,Library> libs;set<string> registered,known;vector<P> frontier;
 while(reference>>w){P p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));known.insert(shape(p));}
 while(old>>w){w=canonicalWord(w);if(registered.insert(w).second)libs[w.size()].arms.push_back(decode(w));}
 while(fresh>>w){w=canonicalWord(w);if(registered.insert(w).second){auto p=decode(w);libs[w.size()].arms.push_back(p);frontier.push_back(p);}}
 for(auto &[len,lib]:libs)lib.prepare();
 map<int,uint64_t> tested,hits;int rows=0,novel=0;
 for(auto& b:frontier){
    array<int,8> perm{0,1,2,3,4,5,6,7};
    do{
        array<int,256> image{};for(int v=1;v<256;v++)image[v]=image[v&(v-1)]|(1<<perm[countr_zero(unsigned(v))]);
        P loc;for(int x:b)if(x)loc.push_back(image[x]);
        for(auto &[len,a]:libs){
            int edges=len+b.size();if(edges<191||a.arms.empty())continue;
            tested[edges]+=a.arms.size();
            for(int j=0;j<a.chunks;j++){
                int n=min<int>(64,a.arms.size()-64*j);
                uint64_t live=n==64?~uint64_t(0):(uint64_t(1)<<n)-1;
                for(int x:loc){live&=~a.banned[x][j];if(!live)break;}
                while(live){
                    int id=64*j+countr_zero(live);live&=live-1;hits[edges]++;
                    P p(a.arms[id].rbegin(),a.arms[id].rend());p.push_back(256);for(int x:loc)p.push_back(256+x);
                    for(int i=0;i<p.size();i++)for(int k=0;k<i;k++){int d=popcount(unsigned(p[i]^p[k]));assert(d>0&&((d==1)==(i==k+1)));}
                    if(edges>=192){cout<<"FOUND "<<edges;for(int x:p)cout<<" "<<x;cout<<endl;return 0;}
                    string s=shape(p);if(known.insert(s).second){out<<s<<endl;novel++;}
                }
            }
        }
    }while(next_permutation(perm.begin(),perm.end()));
    if(++rows%10==0)cout<<"AT "<<rows<<" "<<novel<<endl;
 }
 for(auto [e,n]:tested)cout<<"LENGTH "<<e<<" "<<n<<" "<<hits[e]<<endl;
 cout<<"DONE "<<rows<<" "<<novel<<endl;
}
