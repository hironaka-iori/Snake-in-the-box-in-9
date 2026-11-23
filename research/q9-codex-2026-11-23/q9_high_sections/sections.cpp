#include <array>
#include <algorithm>
#include <cassert>
#include <bitset>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
using Bits=bitset<512>;
#include "../q9_change_basis/forest_focus.hpp"
struct Run{int begin,end;int size() const{return end-begin;}};
struct Candidate{int from,to;};
int main(int argc,char**argv){
    if(argc!=6)return 1;
    int goal=stoi(argv[1]),maxholes=stoi(argv[2]),maxruns=stoi(argv[3]),save=stoi(argv[4]);ofstream bank(argv[5]);
    string line;int rid=0;
    while(getline(cin,line)){
        istringstream in(line);int dim,x;in>>dim;vector<int> source;
        while(in>>x)source.push_back(x);
        vector<int> order(1<<dim,-1);
        for(int i=0;i<(int)source.size();i++){x=source[i];assert(x<(1<<dim)&&order[x]==-1);order[x]=i;}
        for(int i=0;i<(int)source.size();i++){int d=0;for(int a=0;a<dim;a++){int j=order[source[i]^(1<<a)];if(j>=0){assert(abs(j-i)==1);d++;}}assert(d==2-(i==0)-(i+1==(int)source.size()));}
        int longest=0,saved=0;long long tested=0,raw=0;unordered_set<Bits> seen;
        for(int mask=1;mask<(1<<dim);mask++){
            if(__builtin_popcount((unsigned)mask)!=dim-9)continue;
            vector<vector<Run>> faces(1<<(dim-9));vector<int> faceid(1<<dim),base(1<<dim);
            for(int i=1;i<(1<<dim);i++){int bit=i&-i,other=i^bit;if(mask&bit){faceid[i]=faceid[other]|1<<__builtin_popcount((unsigned)(mask&(bit-1)));base[i]=base[other];}
                else {faceid[i]=faceid[other];base[i]=base[other]|1<<__builtin_popcount((unsigned)(~mask&(bit-1)));}}
            for(int i=0;i<(int)source.size();){int j=i+1;int f=faceid[source[i]];while(j<(int)source.size()&&faceid[source[j]]==f)j++;faces[f].push_back({i,j});longest=max(longest,j-i-1);i=j;}
            for(int f=0;f<(int)faces.size();f++){
                auto runs=faces[f];sort(runs.begin(),runs.end(),[](Run a,Run b){return a.size()>b.size()||(a.size()==b.size()&&a.begin<b.begin);});
                if(runs.empty())continue;
                if(runs[0].size()>goal){cout<<"FOUND contiguous "<<rid<<" mask "<<mask<<" face "<<f<<" path";for(int j=runs[0].begin;j<=runs[0].begin+goal;j++)cout<<" "<<base[source[j]];cout<<endl;return 0;}
                int top=min((int)runs.size(),10);vector<int> chosen;
                auto rec=[&](auto&&self,int start,int count)->bool{
                    if(!chosen.empty()&&count>=goal+1-maxholes&&count<=goal+1){
                        int holes=goal+1-count;
                        if((int)chosen.size()<=holes+1){
                            raw++;Bits set;for(int ri:chosen)for(int j=runs[ri].begin;j<runs[ri].end;j++)set.set(base[source[j]]);
                            if(seen.insert(set).second){
                                tested++;if(saved<save){bank<<"points";for(int j=0;j<512;j++)if(set[j])bank<<" "<<j;bank<<endl;saved++;}
                                unordered_set<Bits> failed;vector<int> out;
                                if(grow_focus(set,holes,out,failed)){
                                    cout<<"FOUND forest "<<rid<<" mask "<<mask<<" face "<<f<<" path";for(int z:out)cout<<" "<<z;cout<<endl;return true;
                                }
                            }
                        }
                    }
                    if((int)chosen.size()>=maxruns||start>=top)return false;
                    int upper=count;
                    for(int j=start;j<top&&j-start<maxruns-(int)chosen.size();j++)upper+=runs[j].size();
                    if(upper<goal+1-maxholes)return false;
                    for(int q=start;q<top;q++){if(count+runs[q].size()>goal+1)continue;chosen.push_back(q);
                        if(self(self,q+1,count+runs[q].size()))return true;chosen.pop_back();}
                    return false;
                };
                if(rec(rec,0,0))return 0;
            }
        }
        cout<<"END "<<rid++<<" dimension "<<dim<<" edges "<<source.size()-1<<" longest "<<longest<<" candidate_groups "<<raw<<" unique "<<tested<<" saved "<<saved<<endl;
    }
}
