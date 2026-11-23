// Search all moves translating one interval by two bits, then retain a bounded beam.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
struct State {string s;int cost;uint32_t tie;};
bool before(const State&a,const State&b){return a.cost!=b.cost?a.cost<b.cost:a.tie<b.tie;}
int penalty(int x){return x==0?2:(x&(x-1))==0;}
vector<int> vertices(const string&s){vector<int> p{0};for(char c:s)p.push_back(p.back()^(1<<(c-'0')));return p;}
int score(const string&s){auto p=vertices(s);int z=0;for(int j=0;j<p.size();j++)for(int i=0;i<j-1;i++)z+=penalty(p[i]^p[j]);return z;}
struct Move{int i,j,a,b,cost;uint32_t tie;};
void moves(const State&s,int width,mt19937& rng,vector<State>& next){
    auto p=vertices(s.s);int n=p.size();vector<vector<int>> positions(512);
    for(int i=0;i<n;i++)positions[p[i]].push_back(i);
    vector<Move> found;
    for(int a=0;a<9;a++)for(int b=a+1;b<9;b++){
        int m=(1<<a)^(1<<b);vector<int> bounds{-1},block(n);
        for(int i=0;i<n;i++){
            block[i]=int(bounds.size())-1;
            if(i+1<n&&(s.s[i]=='0'+a||s.s[i]=='0'+b))bounds.push_back(i);
        }
        if(bounds.size()<2)continue;
        bounds.push_back(n-1);int nb=int(bounds.size())-1;
        vector<int> matrix(nb*nb),degree(nb);
        for(int j=0;j<n;j++)for(int flip:{0,m})for(int d=-1;d<9;d++){
            int x=p[j]^flip^(d<0?0:(1<<d));
            for(int i:positions[x])if(i<j&&block[i]!=block[j]){
                int diff=(flip?1:-1)*(d<0?2:1);
                int l=block[i],r=block[j];
                matrix[l*nb+r]+=diff;degree[l]+=diff;degree[r]+=diff;
            }
        }
        for(int r=0;r<nb;r++)for(int l=1;l<r;l++)matrix[l*nb+r]+=matrix[(l-1)*nb+r];
        // Starting at block 1 eliminates the globally translated duplicate of a suffix.
        for(int l=1;l<nb;l++){int delta=0;for(int r=l;r<nb;r++){
            int interior=r==l?0:(matrix[(r-1)*nb+r]-matrix[(l-1)*nb+r]);
            delta+=degree[r]-2*interior;
            int cost=s.cost+delta;if(cost>s.cost+5)continue;
            found.push_back({bounds[l],bounds[r+1],a,b,cost,static_cast<uint32_t>(rng())});
        }}
    }
    auto cmp=[](const Move&a,const Move&b){return a.cost!=b.cost?a.cost<b.cost:a.tie<b.tie;};
    int take=min(int(found.size()),width*3);
    partial_sort(found.begin(),found.begin()+take,found.end(),cmp);
    for(int idx=0;idx<take;idx++){
        auto z=found[idx];string q=s.s;
        for(int k:{z.i,z.j})if(k<q.size())q[k]=char('0'+z.a+z.b-(q[k]-'0'));
        next.push_back({move(q),z.cost,z.tie});
    }
}
int main(int argc,char**argv){
    if(argc!=6)return 2;int width=stoi(argv[1]),depth=stoi(argv[2]),target=stoi(argv[3]),limit=stoi(argv[4]),seed=stoi(argv[5]);
    string line;int handled=0;while(getline(cin,line)&&handled<limit){
        istringstream in(line);int id,t,j,x,last;in>>id>>t>>j>>last;if(t!=target)continue;handled++;
        string s;while(in>>x){int flip=x^last;assert(__builtin_popcount(unsigned(flip))==1);s.push_back(char('0'+__builtin_ctz(unsigned(flip))));last=x;}
        mt19937 rng(seed+id);int rec=score(s);cout<<id<<" "<<t<<" "<<rec<<" "<<s<<endl;
        vector<State> beam{{s,rec,0}};set<string> seen{s};
        for(int iter=0;iter<depth&&!beam.empty();iter++){
            vector<State> next;for(auto&v:beam)moves(v,width,rng,next);
            sort(next.begin(),next.end(),before);beam.clear();
            for(auto&v:next)if(seen.insert(v.s).second){
                assert(score(v.s)==v.cost);
                if(v.cost<rec){rec=v.cost;cout<<id<<" "<<t<<" "<<rec<<" "<<v.s<<endl;if(!rec)return 0;}
                beam.push_back(move(v));if(beam.size()==width)break;
            }
        }
    }
}
