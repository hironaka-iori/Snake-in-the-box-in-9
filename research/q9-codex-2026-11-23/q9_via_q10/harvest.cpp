#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <fstream>
#include <iostream>
#include <sstream>
#include <vector>
#include <set>
#include <string>
using namespace std;
int main(int argc,char**argv){
    if(argc!=4)return 2;int dim=stoi(argv[1]),target=stoi(argv[2]);ifstream in(argv[3]);string line;
    set<string> words; int row=-1,global=0,bestDebt=1e9;uint64_t maps=0,windows=0;
    while(getline(in,line)){
        istringstream is(line);int d;is>>d;if(d!=dim)continue;++row;vector<int> p,steps;
        for(int x;is>>x;)p.push_back(x);
        for(size_t i=1;i<p.size();i++){int z=p[i]^p[i-1];assert(has_single_bit(unsigned(z)));steps.push_back(countr_zero(unsigned(z)));}
        array<int,16> assign{};int best=0,low=1e9;
        auto gen=[&](auto&& self,int i,int used)->void{
            if(used+dim-i<9)return;
            if(i<dim){for(int a=0;a<min(used+1,9);a++){assign[i]=a;self(self,i+1,max(used,a+1));}return;}
            ++maps;array<int,512> seen,cnt{};seen.fill(-1);vector<int> walk;int start=0,x=0,debt=0;
            for(int t=0;t<int(p.size());t++){
                if(t)x^=1<<assign[steps[t-1]];
                if(t>target){
                    int v=walk[t-target-1];cnt[v]--;
                    debt-=cnt[v];for(int b=1;b<512;b*=2)debt-=cnt[v^b];
                }
                int barred=seen[x];debt+=cnt[x];
                for(int b=1;b<512;b*=2){int y=x^b,j=seen[y];debt+=cnt[y];if(j<t-1)barred=max(barred,j);}
                // Earlier occurrences of the immediate predecessor are already excluded by the
                // duplicate at that predecessor. Its latest occurrence is allowed.
                start=max(start,barred+1);seen[x]=t;++cnt[x];walk.push_back(x);
                best=max(best,t-start);
                if(t>=target){windows++;int defects=debt-target;low=min(low,defects);
                    if(defects<=3){
                        string raw;for(int j=t-target+1;j<=t;j++)raw+=char(48+countr_zero(unsigned(walk[j]^walk[j-1])));
                        auto canon=[](string a){array<int,9> ren;ren.fill(-1);int n=0;for(char& c:a){int v=c-48;if(ren[v]<0)ren[v]=n++;c=char(48+ren[v]);}return a;};
                        auto key=canon(raw);reverse(raw.begin(),raw.end());key=min(key,canon(raw));
                        if(words.insert(key).second){cout<<"CAND "<<row<<" "<<t-target<<" "<<defects<<" "<<key<<endl;}
                    }if(defects<bestDebt){bestDebt=defects;cout<<"NEAR "<<row<<" "<<t-target<<" "<<defects;for(int v:assign)cout<<" "<<v;cout<<endl;}}
                if(t-start>global){global=t-start;
                    if(global>=100){cout<<"BEST "<<row<<" "<<start<<" "<<global;for(int k=0;k<dim;k++)cout<<" "<<assign[k];cout<<endl;}}
            }
        };gen(gen,0,0);cout<<"ROW "<<row<<" "<<best<<" "<<low<<endl;
    }
    cout<<"DONE "<<row+1<<" "<<maps<<" "<<windows<<" "<<global<<" "<<bestDebt<<endl;
}
