// Exact weight of a maximum mutually touching family of nonempty subsets of Q3.
// Classify by its zero, one, or two singleton shapes; the residual pair
// incompatibilities form a matching of size twelve.
#include <algorithm>
#include <array>
#include <bit>
#include <iostream>
#include <stdexcept>
#include <vector>
using namespace std;
using Hist=array<int,256>;
struct Scenario { vector<int> singles,unrestricted; vector<pair<int,int>> pairs; };
array<int,256> nearMask{};
vector<Scenario> scenarios;

void initialize(){
    for(int s=1;s<256;s++)for(int x=0;x<8;x++)if(s>>x&1)
        for(int y=0;y<8;y++)if(popcount(unsigned(x^y))<=1)nearMask[s]|=1<<y;
    vector<vector<int>> ss(1);
    for(int i=0;i<8;i++){
        ss.push_back({1<<i});
        for(int j=i+1;j<8;j++)if(has_single_bit(unsigned(i^j)))ss.push_back({1<<i,1<<j});
    }
    for(auto picked:ss){
        Scenario h;h.singles=picked;
        auto ok=[&](int s){return all_of(picked.begin(),picked.end(),[&](int x){return (nearMask[x]&s)!=0;});};
        for(int s=1;s<=255;s++){
            int k=popcount(unsigned(s)),t=255^nearMask[s];
            if(k>=3 || (k==2&&t==0)){if(ok(s))h.unrestricted.push_back(s);continue;}
            if(k!=2||s>=t)continue;
            if(popcount(unsigned(t))!=2||(255^nearMask[t])!=s)throw logic_error("far pair");
            h.pairs.emplace_back(ok(s)?s:0,ok(t)?t:0);
        }
        scenarios.push_back(h);
    }
    if(scenarios.size()!=21)throw logic_error("singletons");
}

int optimum(const Hist& w){
    int best=0;
    for(const auto& h:scenarios){
        int total=0;
        for(int s:h.singles)total+=w[s];
        for(int s:h.unrestricted)total+=w[s];
        for(auto [s,t]:h.pairs)total+=max(w[s],w[t]);
        best=max(best,total);
    }
    return best;
}

int main(){
    initialize();
    cout<<"entry,retained_mask,exclusions,peak,sample_position,excluded_positions\n";
    for(int seed=0;seed<131;seed++){
        array<int,192> q{};
        for(int& x:q)if(!(cin>>x))throw invalid_argument("bank input");
        for(int m=0;m<512;m++)if(popcount(unsigned(m))==3){
            array<int,3> keep{};int k=0;
            for(int b=0;b<9;b++)if(m>>b&1)keep[k++]=b;
            array<int,192> z{},id{},left{},right{};
            vector<int> tr(1,0);
            for(int j=0;j<192;j++){
                for(int b=0;b<3;b++)z[j]|=((q[j]>>keep[b])&1)<<b;
                if(j&&z[j]==z[j-1])tr.push_back(0);
                id[j]=int(tr.size())-1;
                tr.back()|=1<<z[j];
                left[j]=((j&&id[j]==id[j-1])?left[j-1]:0)|(1<<z[j]);
            }
            for(int j=191;j>=0;j--)
                right[j]=((j<191&&id[j]==id[j+1])?right[j+1]:0)|(1<<z[j]);
            array<Hist,2> hist{};
            for(int i=1;i<int(tr.size());i++)hist[(i+1)%2][tr[i]]++;
            int last=0,peak=0,pos=0;
            vector<int> excluded;
            for(int j=0;j<192;j++){
                int r=id[j],p=r%2;
                if(r!=last){
                    hist[last%2][tr[last]]++;
                    hist[(r+1)%2][tr[r]]--;
                    last=r;
                }
                hist[p][left[j]]++; hist[1-p][right[j]]++;
                int score=max(optimum(hist[0]),optimum(hist[1]));
                if(score>peak){peak=score;pos=j;}
                if(score>32)excluded.push_back(j);
                hist[p][left[j]]--;hist[1-p][right[j]]--;
            }
            cout<<seed<<','<<m<<','<<excluded.size()<<','<<peak<<','<<pos<<',';
            for(size_t i=0;i<excluded.size();i++)cout<<(i?" ":"")<<excluded[i];
            cout<<'\n';
        }
    }
}
