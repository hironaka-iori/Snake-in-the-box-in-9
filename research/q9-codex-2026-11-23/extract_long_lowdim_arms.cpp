#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;

string canon(const vector<int>& w, int left, int right) {
    string best;
    for (int direction : {1,-1}) {
        array<int,16> m; m.fill(-1);
        int next=0;
        string s;
        for (int k=0;k<right-left;k++) {
            int v=w[direction==1?left+k:right-1-k];
            if(m[v]<0) m[v]=next++;
            s+=char('a'+m[v]);
        }
        if(best.empty()||s<best) best=s;
    }
    return best;
}
void verify(const string& word, int dim) {
    set<int> used{0}; int v=0;
    for(char c:word) {
        int d=c-'a';
        if(d<0||d>=dim) throw runtime_error("bad axis");
        v^=1<<d;
        int nb=0;
        for(int k=0;k<dim;k++) nb+=used.count(v^(1<<k));
        if(nb!=1||!used.insert(v).second) throw runtime_error("invalid extracted arm");
    }
}
int main(int argc,char** argv) {
    if(argc!=3)return 2;
    ofstream out(argv[1]); if(!out)return 3;
    int min8=stoi(argv[2]);
    map<int,int> rows; map<pair<int,int>,int> maxima;
    set<pair<int,string>> seen;
    string line; int parent=-1;
    while(getline(cin,line)) {
        ++parent;
        if(line.empty()||line[0]<'0'||line[0]>'9')continue;
        auto c1=line.find(','), c2=line.find(',',c1+1), c3=line.find(',',c2+1);
        int n=stoi(line.substr(0,c1)), length=stoi(line.substr(c1+1,c2-c1-1));
        istringstream input(line.substr(c2+1,c3-c2-1)); vector<int>w; int x;
        while(input>>x)w.push_back(x);
        if(int(w.size())!=length)throw runtime_error("truncated source");
        rows[n]++;
        for(int dim:{8,9}) {
            array<int,16> counts{}; int distinct=0,left=0,threshold=dim==8?min8:189;
            for(int j=0;j<length;j++) {
                if(!counts[w[j]]++) distinct++;
                while(distinct>dim) {
                    if(!--counts[w[left++]])distinct--;
                }
                int len=j-left+1;
                maxima[{n,dim}]=max(maxima[{n,dim}],len);
                if(len<threshold)continue;
                for(int start=left;j+1-start>=threshold;start++) {
                    string s=canon(w,start,j+1);
                    if(!seen.emplace(dim,s).second)continue;
                    verify(s,dim);
                    out<<dim<<" "<<s<<" "<<n<<" "<<parent<<" "<<start<<" "<<(j+1)<<endl;
                }
            }
        }
    }
    for(auto [n,num]:rows)cout<<"source Q"<<n<<" rows "<<num<<" max Q8 "<<maxima[{n,8}]<<" max Q9 "<<maxima[{n,9}]<<endl;
    cout<<"distinct excerpts "<<seen.size()<<endl;
}
