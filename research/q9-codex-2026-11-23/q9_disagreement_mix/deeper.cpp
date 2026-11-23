// On one cube colour release two prescribed vertices and insert three in their place.
// Every vertex of the opposite colour is freely reconstructed by the Hamiltonian search.
#define main parity_reference_entry
#include "../search_q9_new_parity_replacements.cpp"
#undef main
#include <sstream>
struct CandidateSearch {
    Bounds state;
    vector<int> base,pool,chosen;
    uint64_t pairs=0,eligible=0,unknown=0,oneOK=0,twoOK=0;
    int cap;
    bool complete(){
        if(state.counts[1]<2 || state.counts[2]<int(base.size()))return false;
        vector<int> fixed;for(int v=0;v<512;++v)if(state.occupied[v])fixed.push_back(v);
        if(fixed.size()!=base.size()+1)abort();
        ++eligible;
        if(getenv("Q9_DUMP_MINORITY")){
            cout<<"S";for(int v:fixed)cout<<" "<<v;cout<<"\n";
        }
        Search check(fixed,cap,false);
        bool hit=check.test();unknown+=check.unknown;
        return hit;
    }
    bool run(const vector<int>& src,int forcedA,int forcedB){
        base=src;
        for(int v:base)state.change(v,1);
        for(int v=0;v<512;++v)if(!state.occupied[v] && !__builtin_parity(unsigned(v^base.front())))pool.push_back(v);
        for(int i=0;i<int(base.size());++i){
            if(forcedA>=0&&forcedA!=i)continue;
            state.change(base[i],-1);
            for(int j=i+1;j<int(base.size());++j){
                if(forcedB>=0&&forcedB!=j)continue;
                ++pairs;state.change(base[j],-1);vector<int> allowed;
                for(int v:pool){
                    // A new minority point needs two distinct available neighbours.
                    int connectors=0;for(int d=0;d<9;++d)connectors+=state.load[v^(1<<d)]<2;
                    if(connectors<2)continue;
                    state.change(v,1);if(!state.poor)allowed.push_back(v);state.change(v,-1);
                }
                oneOK+=allowed.size();
                for(int a=0;a<int(allowed.size());++a){
                    state.change(allowed[a],1);
                    for(int b=a+1;b<int(allowed.size());++b){
                        state.change(allowed[b],1);
                        if(!state.poor){
                            ++twoOK;
                            for(int c=b+1;c<int(allowed.size());++c){
                                state.change(allowed[c],1);
                                if(!state.poor&&complete())return true;
                                state.change(allowed[c],-1);
                            }
                        }
                        state.change(allowed[b],-1);
                    }
                    state.change(allowed[a],-1);
                }
                state.change(base[j],1);
            }
            state.change(base[i],1);
        }
        return false;
    }
};
int main(int argc,char**argv){
    if(argc!=4)return 2;
    int start=stoi(argv[1]),stop=stoi(argv[2]),cap=stoi(argv[3]);string line;int row=0;
    while(getline(cin,line)){
        if(row>=stop)break;
        if(row<start){++row;continue;}
        istringstream f(line);int a,b;f>>a>>b;vector<int> s;for(int v;f>>v;)s.push_back(v);
        if(s.size()<2)return 3;
        array<bool,512> seen{};
        for(int v:s){if(v<0||v>=512||seen[v]||__builtin_parity(unsigned(v^s[0])))return 3;seen[v]=true;}
        CandidateSearch q;q.cap=cap;
        bool hit=q.run(s,a,b);
        cout<<"ROW "<<row<<" "<<q.pairs<<" "<<q.oneOK<<" "<<q.twoOK<<" "<<q.eligible<<" "<<q.unknown<<" "<<hit<<endl;
        if(hit&&s.size()>=95)return 0;
        ++row;
    }
}
