// Enumerate same-parity substitutions, with both endpoints in the prescribed set.
#define main minority_exchange_cli
#include "search_q9_parity_combinations.cpp"
#undef main
struct MajorityExchange {
    Bounds state;
    vector<int> source, outside;
    int cap, drops, gain;
    bool stream_odd=false,minor=false;
    uint64_t cores=0, tests=0, undecided=0;
    bool viable() const {
        // Existing vertices can only lose usable neighbors as further vertices enter.
        // Each endpoint may use one neighbor; no vertex may use zero.
        if(state.poor>(minor?0:(stream_odd?1:2)))return false;
        if(state.poor)for(int v:source)if(state.occupied[v] && !state.room[v])return false;
        return true;
    }
    bool fill(const vector<int>& options,int start,int need) {
        if(!need) {
            if(state.counts[2]<int(source.size())+gain-1)return false;
            if((minor && state.counts[1]<2) || (stream_odd && !state.counts[1]))return false;
            vector<int> s;for(int v=0;v<512;v++)if(state.occupied[v])s.push_back(v);
            assert(s.size()==source.size()+gain);tests++;
            if(stream_odd){
                for(int v:s)cout<<v<<" ";
                cout<<"\n";return false;
            }
            Search graph(s,cap,!minor);
            if(graph.test())return true;
            undecided+=graph.unknown;return false;
        }
        for(int j=start;j+need<=int(options.size());j++){
            int v=options[j];state.change(v,1);
            if(state.room[v] && viable() && fill(options,j+1,need-1))return true;
            state.change(v,-1);
        }return false;
    }
    bool remove(int base,int need) {
        if(!need) {
            cores++;
            if(!viable())return false;
            vector<int> options;
            if(drops+gain)for(int v:outside){
                state.change(v,1);if(state.room[v] && viable())options.push_back(v);state.change(v,-1);
            }
            return fill(options,0,drops+gain);
        }
        for(int j=base;j+need<=int(source.size());j++){
            int v=source[j];state.change(v,-1);
            if(remove(j+1,need-1))return true;
            state.change(v,1);
        }return false;
    }
};
int main(int argc,char** argv){
    if(argc<3||argc>5)return 2;int drops=stoi(argv[1]),cap=stoi(argv[2]);
    int gain=argc>=4?stoi(argv[3]):0;
    if(gain<0||gain>5)return 2;
    if(drops<0||drops>5||cap<=0)return 2;
    string line;int row=0;
    while(getline(cin,line)){
        MajorityExchange e;e.cap=cap;e.drops=drops;e.gain=gain;e.stream_odd=(argc==5 && string(argv[4])=="odd-stream");e.minor=(argc==5 && string(argv[4])=="minor");int x;istringstream input(line);
        while(input>>x){if(x<0||x>=512||e.state.occupied[x]||(!e.source.empty()&&popcount(unsigned(x^e.source[0]))%2))return 2;e.source.push_back(x);e.state.change(x,1);}
        if(e.source.size()<3||e.source.size()>128)return 2;
        for(int x=0;x<512;x++)if(!e.state.occupied[x] && popcount(unsigned(x^e.source[0]))%2==0)e.outside.push_back(x);
        if(e.remove(0,drops))return 0;
        (e.stream_odd?cerr:cout)<<"ROW "<<row++<<" "<<e.cores<<" "<<e.tests<<" "<<e.undecided<<endl;
    }
}
