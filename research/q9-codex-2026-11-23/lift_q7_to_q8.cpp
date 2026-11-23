// Build both orientations of distinct long Q8 snakes by joining two Q7 arms.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <set>
#include <string>
#include <vector>
using namespace std;
struct Arm {string steps; vector<int> vertices; array<uint64_t,2> mask{};};
string canonical(string word){
    array<int,8> labels; labels.fill(-1);int n=0;
    for(char &c:word){
        int d=c-'0';if(labels[d]<0)labels[d]=n++;c='0'+labels[d];
    }
    return word;
}
bool valid(const vector<int>& p){
    for(unsigned i=0;i<p.size();i++)for(unsigned j=0;j<i;j++){
        int d=popcount(unsigned(p[i]^p[j]));if(!d || (d==1)!=(i==j+1))return false;
    }
    return true;
}
int main(){
    vector<Arm> arms;
    string s;
    while(cin>>s){
        Arm a;a.steps=s;a.vertices.push_back(0);
        for(char c:s){
            if(c<'0'||c>'6')return 2;
            int v=a.vertices.back()^(1<<(c-'0'));a.vertices.push_back(v);
            a.mask[v/64]|=uint64_t(1)<<(v%64);
        }
        if(!valid(a.vertices))return 3;
        arms.push_back(a);
    }
    sort(arms.begin(),arms.end(),[](const Arm&a,const Arm&b){return a.steps.size()<b.steps.size();});
    set<string> result;
    array<int,7> perm{0,1,2,3,4,5,6};
    do{
        array<int,128> m{};
        for(int v=1;v<128;v++)m[v]=m[v&(v-1)]|(1<<perm[countr_zero(unsigned(v))]);
        for(int j=0;j<int(arms.size());j++){
            const auto &b=arms[j];array<uint64_t,2> mask{};
            for(size_t h=1;h<b.vertices.size();h++){
                int v=m[b.vertices[h]];mask[v/64]|=uint64_t(1)<<(v%64);
            }
            for(int i=j;i>=0;i--){
                const auto &a=arms[i];if(a.steps.size()+b.steps.size()+1<93)break;
                if((a.mask[0]&mask[0])||(a.mask[1]&mask[1]))continue;
                string q(a.steps.rbegin(),a.steps.rend());q+='7';
                for(char c:b.steps)q+=char('0'+perm[c-'0']);
                if(result.insert(canonical(q)).second){
                    vector<int> p{0};for(char c:q)p.push_back(p.back()^(1<<(c-'0')));
                    if(!valid(p))return 4;
                    result.insert(canonical(string(q.rbegin(),q.rend())));
                }
            }
        }
    }while(next_permutation(perm.begin(),perm.end()));
    for(const auto &q:result)cout<<q<<'\n';
}
