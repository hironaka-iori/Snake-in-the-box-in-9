#define Q9_MIXED_CHECK
#include "q9_mixed_halves.cpp"
struct Donors{
    set<string> data;
    void load(const string& name,int length,int step){
        ifstream f(name);if(!f)throw runtime_error("input file");
        string w;
        while(f>>w){
            if(!length){data.insert(canonical(w));continue;}
            int last=int(w.size())-length;
            if(last<0)throw runtime_error("short");
            for(int i=0;i<=last;i+=step)data.insert(canonical(w.substr(i,length)));
            data.insert(canonical(w.substr(last,length)));
        }
    }
};
int main(int argc,char**argv){
    if(argc<6)return 2;
    int goal=stoi(argv[1]),len=stoi(argv[2]),step=stoi(argv[3]);
    if(len<2||step<1)return 2;
    Donors moms,bank;moms.load(argv[4],0,1);
    for(int i=5;i<argc;i++)bank.load(argv[i],len,step);
    vector<Shape> bs;for(auto &w:bank.data)bs.emplace_back(decodeWord(w),9);
    Embed search(9,goal);
    uint64_t pairs=0,parents=0;
    cout<<"START "<<goal<<" "<<len<<" "<<step<<" "<<moms.data.size()<<" "<<bank.data.size()<<endl;
    for(auto&w:moms.data){
        auto a=decodeWord(w);search.setFirst(a);
        for(size_t j=0;j<bs.size();j++){
            ++pairs;
            if(search.run(bs[j])){cout<<"DONORS "<<w<<" ";for(int i=1;i<bs[j].p.size();i++)cout<<countr_zero(unsigned(bs[j].p[i]^bs[j].p[i-1]));cout<<endl;return 0;}
        }
        if(++parents%25==0)cout<<"AT "<<parents<<" "<<pairs<<" "<<search.admitted<<" "<<search.search.extension.nodes<<endl;
    }
    cout<<"DONE "<<pairs<<" "<<search.admitted<<" "<<search.direct<<" "<<search.assignments<<" "<<search.search.bridgeNodes<<" "<<search.search.extension.nodes<<endl;
}
