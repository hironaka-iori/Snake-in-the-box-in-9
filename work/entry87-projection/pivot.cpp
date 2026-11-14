// Rooted isometry gluing. Reads one list of nine-cube vertices from stdin.
// Writes the attempted and successful permutation counts for each eligible pivot.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

using namespace std;

bool induced(const vector<int>& path) {
    for (size_t j=0; j<path.size(); ++j) {
        for (size_t i=0; i<j; ++i) {
            int h=popcount(unsigned(path[i]^path[j]));
            if (j==i+1 ? h!=1 : h<2) return false;
        }
    }
    return true;
}

int main() {
    vector<int> path;
    int x;
    while (cin>>x) {
        if (x<0 || x>=512) throw invalid_argument("vertex outside Q9");
        path.push_back(x);
    }
    if (path.size()!=193) throw invalid_argument("expected 193 vertices");
    cout<<"pivot,eligible,attempted,valid,first_witness\n";
    for(int k=0;k<193;++k) {
        vector<int> l(path.begin(),path.begin()+k+1), r(path.begin()+k,path.end());
        if (!induced(l) || !induced(r)) {cout<<k<<",0,0,0,\n";continue;}
        const bool move_left=l.size()<r.size();
        if(move_left) swap(l,r);
        const int v=path[k];
        array<bool,512> blocked{};
        for(int w:l) if(w!=v) {
            blocked[w^v]=true;
            for(int i=0;i<9;++i) blocked[(w^v)^(1<<i)]=true;
        }
        vector<int> offsets;
        for(int w:r) if(w!=v) offsets.push_back(w^v);
        // Short checks first; moving a long arm has the same validity criterion.
        // Sorting by the fraction of the same Hamming sphere that is blocked
        // changes only the order of failure detection.
        array<int,10> blocked_count{},sphere{};
        for(int w=0;w<512;++w) {
            int h=popcount(unsigned(w));
            sphere[h]++; blocked_count[h]+=blocked[w];
        }
        stable_sort(offsets.begin(),offsets.end(),[&](int a,int b) {
            int i=popcount(unsigned(a)),j=popcount(unsigned(b));
            return blocked_count[i]*sphere[j]>blocked_count[j]*sphere[i];
        });
        array<int,9> perm{0,1,2,3,4,5,6,7,8};
        uint64_t attempted=0,valid=0;
        vector<int> first;
        do {
            ++attempted;
            auto image=[&](int w) {
                int t=0;
                for(unsigned z=w;z;z&=z-1) t|=1<<perm[countr_zero(z)];
                return t;
            };
            bool ok=true;
            for(int w:offsets) if(blocked[image(w)]) {ok=false;break;}
            if(ok) {
                ++valid;
                if(first.empty()) {
                    first=path;
                    for(int j=0;j<193;++j) if(move_left ? j<k : j>k)
                        first[j]=v^image(first[j]^v);
                    if(!induced(first)) throw logic_error("invalid witness");
                }
            }
        } while(next_permutation(perm.begin(),perm.end()));
        cout<<k<<",1,"<<attempted<<","<<valid<<",";
        for (int w:first) cout<<w<<" ";
        cout<<"\n";
    }
}
