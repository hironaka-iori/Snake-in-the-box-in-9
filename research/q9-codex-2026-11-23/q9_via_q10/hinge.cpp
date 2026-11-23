// Fold two contiguous pieces independently, then enumerate relative coordinate
// permutations about their common endpoint without changing either piece.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using namespace std;using Path=vector<int>;
string canonical(string w){array<int,16> map;map.fill(-1);int n=0;for(char& z:w){int d=z-'A';if(map[d]<0)map[d]=n++;z='A'+map[d];}return w;}
Path vertices(const string& w){Path p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'A')));return p;}
bool valid(const Path& p){for(int j=0;j<int(p.size());j++)for(int i=0;i<j;i++){
    int d=popcount(unsigned(p[i]^p[j]));if(d==0||((d==1)!=(i+1==j)))return false;}return true;}
struct Glue{
    array<bool,512> forbidden{};array<int,9> map{};const string& right;int used=0;uint64_t branches=0;string word;
    Glue(const string& a,const string& b):right(b){Path p=vertices(a);for(size_t i=1;i<p.size();i++){
        int x=p[i];forbidden[x]=true;for(int k=1;k<512;k*=2)forbidden[x^k]=true;}map.fill(-1);}
    bool search(int i,int x){
        while(i<int(right.size())){
            int a=right[i]-'A',dest=map[a];if(dest<0){++branches;
                for(int d=0;d<9;d++)if(!(used>>d&1)){int y=x^(1<<d);if(forbidden[y])continue;
                    map[a]=d;used^=1<<d;if(search(i+1,y))return true;used^=1<<d;map[a]=-1;}
                return false;
            }
            x^=1<<dest;if(forbidden[x])return false;i++;
        }
        for(char c:right)word.push_back('A'+map[c-'A']);return true;
    }
};
struct Bank{
    unordered_map<string,vector<string>> pieces;
    vector<string> alternatives(const string& raw){
        string key=canonical(raw);auto it=pieces.find(key);if(it!=pieces.end())return it->second;
        int dims=1+(*max_element(key.begin(),key.end())-'A');set<string> distinct;
        // A short piece can omit some input axes. Enumerate all induced
        // identifications attainable by a global surjection from ten axes.
        if(dims<10&&valid(vertices(key)))distinct.insert(key);
        for(int a=0;a<dims;a++)for(int b=0;b<a;b++){
            string w=key;for(char& c:w)if(c=='A'+a)c='A'+b;w=canonical(w);
            if(valid(vertices(w)))distinct.insert(w);
        }
        vector<string> out(distinct.begin(),distinct.end());pieces.emplace(key,out);return out;
    }
};
int main(int argc,char**argv){
    if(argc!=7)return 2;int goal=stoi(argv[1]),cut=stoi(argv[2]),stride=stoi(argv[3]),mode=stoi(argv[4]);ifstream in(argv[5]);mt19937 rng(stoul(argv[6]));
    string line;int row=-1;Bank bank;unordered_set<string> done;uint64_t windows=0,pairs=0,branches=0,success=0;
    while(getline(in,line)){istringstream s(line);int dim;s>>dim;if(dim!=(mode==1?9:10))continue;row++;
        Path p;for(int x;s>>x;)p.push_back(x);assert(valid(p));string w;
        for(size_t i=1;i<p.size();i++)w.push_back('A'+countr_zero(unsigned(p[i]^p[i-1])));
        for(int start=0;start+goal<=int(w.size());start+=stride){
            int split=cut?cut:1+rng()%(goal-1);
            string a=w.substr(start,split),b=w.substr(start+split,goal-split);reverse(a.begin(),a.end());
            vector<string> left,right;
            if(mode==1){left={canonical(a)};right={canonical(b)};}else{left=bank.alternatives(a);right=bank.alternatives(b);}
            windows++;
            for(const auto& l:left)for(const auto& r:right){pairs++;
                string key=l<r?l+" "+r:r+" "+l;if(!done.insert(key).second)continue;
                Glue g(l,r);bool hit=g.search(0,0);branches+=g.branches;if(!hit)continue;
                string result=l;reverse(result.begin(),result.end());result+=g.word;
                Path path=vertices(result);assert(int(result.size())==goal&&valid(path));success++;
                cout<<"FOUND "<<row<<" "<<start<<" "<<split<<" "<<goal;for(int x:path)cout<<" "<<x;cout<<endl;
                if(mode==0)return 0;
            }
        }cout<<"ROW "<<row<<" "<<windows<<" "<<pairs<<" "<<done.size()<<" "<<branches<<" "<<success<<endl;
    }
    cout<<"DONE "<<windows<<" "<<pairs<<" "<<done.size()<<" "<<branches<<" "<<success<<endl;
}
