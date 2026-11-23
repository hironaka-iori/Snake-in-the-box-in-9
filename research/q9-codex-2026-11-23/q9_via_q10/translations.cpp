#define main ports_original_main
#include "ports.cpp"
#undef main
#include <bitset>
using Bits=bitset<512>;
struct Relation{Bits ok;Path deltas;};
struct CSP{
    const vector<Path>& shape;vector<vector<Relation>> rel;uint64_t nodes=0;int budget;
    Path answer;
    CSP(const vector<Path>& input,int cap):shape(input),rel(input.size(),vector<Relation>(input.size())),budget(cap){
        int n=shape.size();for(int i=0;i<n;i++)for(int j=i+1;j<n;j++){
            array<unsigned short,512> hits{};
            for(int x:shape[i])for(int y:shape[j]){
                int m=x^y;hits[m]++;for(int b=1;b<512;b*=2)hits[m^b]++;
            }
            auto& r=rel[i][j];
            for(int v=0;v<512;v++){
                bool ok=(j==i+1)? hits[v]==1&&popcount(unsigned(shape[i].back()^v))==1 : hits[v]==0;
                if(ok){r.ok.set(v);r.deltas.push_back(v);}
            }
            rel[j][i]=r;
        }
    }
    struct Domain{Bits bits;Path opts;};
    bool filter(vector<Domain>& d,Path queue){
        int n=d.size();vector<bool> pending(n);for(int k:queue)pending[k]=true;
        for(size_t head=0;head<queue.size();head++){
            int i=queue[head];pending[i]=false;
            for(int j=0;j<n;j++)if(j!=i){
                const auto& r=rel[i][j];auto& opts=d[j].opts;auto old=opts.size();int size=0;
                for(int x:opts){
                    bool supported=false;
                    if(r.deltas.size()<d[i].opts.size()){
                        for(int z:r.deltas)if(d[i].bits[x^z]){supported=true;break;}
                    }else{
                        for(int y:d[i].opts)if(r.ok[x^y]){supported=true;break;}
                    }
                    if(supported)opts[size++]=x;else d[j].bits.reset(x);
                }
                if(!size)return false;
                if(size!=int(old)){
                    opts.resize(size);if(!pending[j]){queue.push_back(j);pending[j]=true;}
                }
            }
        }return true;
    }
    int dfs(vector<Domain>& d,Path queue){
        if(++nodes>budget)return -1;
        if(!filter(d,queue))return 0;
        int chosen=-1;for(int k=0;k<int(d.size());k++)if(d[k].opts.size()>1&&
             (chosen<0||d[k].opts.size()<d[chosen].opts.size()))chosen=k;
        if(chosen<0){
            for(int k=0;k<int(d.size());k++)for(int x:shape[k])answer.push_back(x^d[k].opts[0]);
            assert(valid(answer));return 1;
        }
        for(int v:d[chosen].opts){
            auto next=d;next[chosen].opts={v};next[chosen].bits.reset();next[chosen].bits.set(v);
            int r=dfs(next,{chosen});if(r)return r;
        }
        return 0;
    }
    int solve(){
        int c=0,n=shape.size();for(int i=1;i<n;i++)if(shape[i].size()>shape[c].size())c=i;
        vector<Domain> d(n);Path q(n),parity(n);iota(q.begin(),q.end(),0);swap(q[0],q[c]);
        for(int i=1;i<n;i++)parity[i]=parity[i-1]^(shape[i-1].size()%2);
        for(int i=0;i<n;i++)for(int v=0;v<512;v++)
            if((i!=c||!v) && int(popcount(unsigned(v))%2)==(parity[i]^parity[c])){
                d[i].opts.push_back(v);d[i].bits.set(v);}
        return dfs(d,q);
    }
};
#ifndef TRANSLATION_LIBRARY
int main(int argc,char**argv){
    if(argc!=6)return 2;int dim=stoi(argv[1]),len=stoi(argv[2]),cap=stoi(argv[3]);ifstream s(argv[4]),jobs(argv[5]);string line;vector<Path> data;
    while(getline(s,line)){istringstream in(line);int d;in>>d;if(d!=dim)continue;Path w;int last,x;in>>last;while(in>>x){w.push_back(countr_zero(unsigned(last^x)));last=x;}data.push_back(w);}
    while(getline(jobs,line)){istringstream in(line);string kind;int row,mask,off;in>>kind;if(kind!="LIMIT")continue;in>>row>>mask>>off;
        Run blocks(data.at(row),off,len,mask,1);CSP m(blocks.blocks,cap);int ans=m.solve();
        cout<<"CASE "<<row<<" "<<mask<<" "<<off<<" "<<ans<<" "<<m.nodes;
        if(ans>0)for(int x:m.answer)cout<<" "<<x;cout<<endl;
    }
}

#endif
