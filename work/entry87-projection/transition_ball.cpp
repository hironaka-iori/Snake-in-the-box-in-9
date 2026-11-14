// Exact indexed transition-substitution search. Input: an ordered 193-vertex walk.
// Arguments: substitutions, first-step range, optional --reverse, optional second-step range.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>
using namespace std;
int N,P;
using Count=uint64_t;
struct Segment{int first,last,delta;};
struct Change{int step,bit;};
vector<int> q,oldbits;
vector<uint16_t> prefix;
vector<Segment> fixedParts;
vector<Change> edits,hit;
Count calls=0,tried=0,closed=0;
int remainingFirst,remainingLast,secondFirst,secondLast;

// For a pair of segments, their relative translation determines every new
// inter-vertex distance. Only nonconsecutive index pairs are counted.
int rectangle(int delta,int a,int b,int c,int d) {
    size_t off=size_t(delta)*P*P;
    auto v=[&](int i,int j){return int(prefix[off+i*P+j]);};
    return v(b+1,d+1)-v(a,d+1)-v(b+1,c)+v(a,c);
}
bool permitted(int start,int end,int delta) {
    if(rectangle(0,start,end,start,end))return false;
    for(auto s:fixedParts)
        if(rectangle(delta^s.delta,s.first,s.last,start,end))return false;
    return true;
}
bool search(int start,int delta,int left) {
    ++calls;
    if(!left){
        ++closed;
        if(!permitted(start,N-1,delta))return false;
        hit=edits;
        return true;
    }
    // The next edited step can immediately follow the last edited one.
    // Every earlier vertex must still pass against the existing prefix.
    if(!permitted(start,start,delta))return false;
    int lo=start,hi=N-1;
    while(lo<hi){
        int mid=(lo+hi+1)/2;
        if(permitted(start,mid,delta))lo=mid;else hi=mid-1;
    }
    int first=start+1,last=min(lo+1,N-left);
    if(edits.empty()){first=max(first,remainingFirst);last=min(last,remainingLast);}
    if(edits.size()==1){first=max(first,secondFirst);last=min(last,secondLast);}
    for(int t=first;t<=last;t++){
        fixedParts.push_back({start,t-1,delta});
        for(int b=0;b<9;b++)if(b!=oldbits[t]){
            ++tried;
            edits.push_back({t,b});
            if(search(t,delta^(1<<oldbits[t])^(1<<b),left-1))return true;
            edits.pop_back();
        }
        fixedParts.pop_back();
    }
    return false;
}
int main(int argc,char**argv){
    if(argc<4)return 2;
    int radius=stoi(argv[1]);
    remainingFirst=stoi(argv[2]);remainingLast=stoi(argv[3]);
    for(int w;cin>>w;)q.push_back(w);
    if(q.size()<2||q.size()>193)return 4;
    N=int(q.size());P=N+1;
    int arg=4;bool reversed=arg<argc && string(argv[arg])=="--reverse";
    if(reversed){++arg;reverse(q.begin(),q.end());}
    secondFirst=1;secondLast=N-1;
    if(arg+2==argc){secondFirst=stoi(argv[arg]);secondLast=stoi(argv[arg+1]);}
    else if(arg!=argc)return 2;
    if(radius<0||radius>=N||remainingFirst<1||remainingLast>=N||remainingFirst>remainingLast)return 3;
    oldbits.resize(N);
    for(int i=1;i<N;i++){
        unsigned d=q[i]^q[i-1];
        if(!has_single_bit(d))throw invalid_argument("nonedge at source step");
        oldbits[i]=countr_zero(d);
    }
    prefix.resize(512*P*P);
    for(int delta=0;delta<512;delta++)if(popcount(unsigned(delta))%2==0){
        auto table=prefix.data()+size_t(delta)*P*P;
        for(int i=0;i<N;i++){
            int row=0;
            for(int j=0;j<N;j++){
                if(j>i+1 && popcount(unsigned(q[i]^q[j]^delta))<=1)++row;
                table[(i+1)*P+j+1]=row+table[i*P+j+1];
            }
        }
    }
    bool found=search(0,0,radius);
    cout<<"{\"substitutions\":"<<radius<<",\"first_range\":["<<remainingFirst<<','<<remainingLast
        <<"],\"second_range\":["<<secondFirst<<','<<secondLast<<"],\"reversed\":"
        <<(reversed?"true":"false")<<",\"calls\":"<<calls<<",\"replacements\":"<<tried<<",\"terminal_tests\":"<<closed
        <<",\"status\":\""<<(found?"SAT":"UNSAT")<<"\"";
    if(found){
        vector<int> transitions=oldbits;
        for(auto c:hit)transitions[c.step]=c.bit;
        vector<int> w={q[0]};
        for(int i=1;i<N;i++)w.push_back(w.back()^(1<<transitions[i]));
        for(int j=0;j<N;j++)for(int i=0;i<j;i++){
            int d=popcount(unsigned(w[i]^w[j]));
            if(j==i+1?d!=1:d<2)throw logic_error("invalid witness");
        }
        cout<<",\"vertices\":[";
        for(size_t i=0;i<w.size();i++)cout<<(i?",":"")<<w[i];
        cout<<"]";
    }
    cout<<"}\n";
}
