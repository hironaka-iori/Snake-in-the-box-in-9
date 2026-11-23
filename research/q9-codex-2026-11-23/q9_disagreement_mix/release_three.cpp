// Remove three prescribed minority points, insert four new points outside the source.
#define main parity_bounds_entry
#include "../search_q9_new_parity_replacements.cpp"
#undef main
#include <sstream>
struct ReleaseThree{
    Bounds state;vector<int> pool,source,allowed;
    int drops=3;
    uint64_t triples=0,tested=0,unknown=0;
    bool insert(int first,int left){
        if(!left){
            if(state.counts[1]<2||state.counts[2]<int(source.size()))return false;
            vector<int> side;for(int v=0;v<512;++v)if(state.occupied[v])side.push_back(v);
            if(side.size()!=source.size()+1)abort();
            ++tested;Search s(side,200000,false);bool found=s.test();unknown+=s.unknown;return found;
        }
        for(int i=first;i+left<=int(allowed.size());++i){
            state.change(allowed[i],1);
            if(!state.poor&&insert(i+1,left-1))return true;
            state.change(allowed[i],-1);
        }
        return false;
    }
    bool remove(int first,int left){
        if(!left){
            ++triples;allowed.clear();
            for(int v:pool){
                int room=0;for(int d=0;d<9;++d)room+=state.load[v^(1<<d)]<=1;
                if(room<2)continue;
                state.change(v,1);if(!state.poor)allowed.push_back(v);
                state.change(v,-1);
            }
            return insert(0,drops+1);
        }
        for(int j=first;j+left<=int(source.size());++j){
            state.change(source[j],-1);
            if(remove(j+1,left-1))return true;
            state.change(source[j],1);
        }
        return false;
    }
    bool run(){
        for(int v:source)state.change(v,1);
        for(int x=0;x<512;++x)if(!state.occupied[x]&&!__builtin_parity(unsigned(x^source[0])))pool.push_back(x);
        return remove(0,drops);
    }
};
int main(int argc,char**argv){
    if(argc!=3 && argc!=4)return 2;int row=0;
    for(string line;getline(cin,line);++row){
        if(row<stoi(argv[1])||row>=stoi(argv[2]))continue;
        istringstream f(line);int a,b;f>>a>>b;ReleaseThree q;if(argc==4)q.drops=stoi(argv[3]);
        for(int v;f>>v;)q.source.push_back(v);
        bool found=q.run();
        cout<<"ROW "<<row<<" "<<q.triples<<" "<<q.tested<<" "<<q.unknown<<" "<<found<<endl;
        if(found&&q.source.size()==95)return 0;
    }
}
