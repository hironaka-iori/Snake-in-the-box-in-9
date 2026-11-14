// Enumerate all edits of one even set in a rooted Q8 face and recover every
// possible order and set of odd representatives in both opposite layers.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>
using namespace std;
struct Mask{
    array<uint64_t,4> words{};
    bool operator[](size_t i)const{return (words[i/64]>>(i%64))&1;}
    void set(size_t i){words[i/64]|=uint64_t(1)<<(i%64);}
    void reset(size_t i){words[i/64]&=~(uint64_t(1)<<(i%64));}
    void flip(size_t i){words[i/64]^=uint64_t(1)<<(i%64);}
    size_t count()const{size_t k=0;for(auto w:words)k+=popcount(w);return k;}
    bool none()const{return !(words[0]|words[1]|words[2]|words[3]);}
    size_t first_from(size_t i)const{
        if(i>=256)return 256;
        size_t j=i/64;uint64_t word=words[j]&(~uint64_t(0)<<(i%64));
        while(!word && ++j<4)word=words[j];
        return j==4?256:64*j+countr_zero(word);
    }
    size_t first()const{return first_from(0);}
    size_t next(size_t i)const{return first_from(i+1);}
    Mask operator&(const Mask&b)const{
        Mask r;for(int i=0;i<4;++i)r.words[i]=words[i]&b.words[i];return r;
    }
    Mask operator~()const{Mask r;for(int i=0;i<4;++i)r.words[i]=~words[i];return r;}
};
array<Mask,256> neighbors;
using Path=vector<int>;
struct Shape{
    Mask anchor;
    array<Mask,256> adj,tip;
    Mask marked;
    bool caps;
    explicit Shape(const Mask& a,bool cap):anchor(a),caps(cap){
        for(int w=0;w<256;++w){
            Mask n=a&neighbors[w];
            if(n.count()==1){int x=int(n.first());tip[x].set(w);marked.set(x);}
            if(n.count()==2){
                int x=int(n.first()),y=int(n.next(x));adj[x].set(y);adj[y].set(x);
            }
        }
    }
    vector<Path> all_orders(const Path& active){
        vector<Path> out;Path seq{0};Mask free=anchor;free.reset(0);
        auto visit=[&](auto&& self,int end)->void{
            if(free.none()){
                if(!caps || marked[end])out.push_back(seq);
                return;
            }
            Mask next=free&adj[end];
            if(next.none())return;
            int leaves=0;
            for(int y:active){
                if(!free[y])continue;
                size_t deg=(adj[y]&free).count()+adj[y][end];
                if(deg==0)return;
                if(deg==1 && (++leaves>1 || (caps && !marked[y])))return;
            }
            for(size_t y=next.first();y<256;y=next.next(y)){
                seq.push_back(int(y));free.reset(y);self(self,int(y));free.set(y);seq.pop_back();
            }
        };
        visit(visit,0);return out;
    }
    vector<Mask> lists(const Path& p)const{
        vector<Mask> out;
        for(size_t i=1;i<p.size();++i){
            Mask candidates=neighbors[p[i-1]]&neighbors[p[i]],valid;
            for(size_t w=candidates.first();w<256;w=candidates.next(w))
                if((neighbors[w]&anchor).count()==2)valid.set(w);
            if(valid.none())throw logic_error("edge has no witness");
            out.push_back(valid);
        }
        if(caps)out.push_back(tip[p.back()]);
        return out;
    }
};

vector<int> matching(const vector<Mask>& lists){
    array<int,256> owner;owner.fill(-1);
    auto augment=[&](auto&& self,int j,Mask& seen)->bool{
        Mask allowed=lists[j]&~seen;
        for(size_t w=allowed.first();w<256;w=allowed.next(w)){
            if(seen[w])continue;
            seen.set(w);
            if(owner[w]==-1 || self(self,owner[w],seen)){owner[w]=j;return true;}
        }
        return false;
    };
    for(int j=0;j<int(lists.size());++j){
        Mask seen;
        if(!augment(augment,j,seen))return {};
    }
    vector<int> result(lists.size());
    for(int w=0;w<256;++w)if(owner[w]>=0)result[owner[w]]=w;
    return result;
}

int main(int argc,char**argv){
    if(argc!=3)return 2;
    int cap=stoi(argv[1]),changing=stoi(argv[2]);
    array<Path,2> original;
    array<Mask,2> base;
    for(int s=0;s<2;++s){
        int size;cin>>size;
        if(size!=49-s)return 2;
        for(int i=0;i<size;++i){
            int v;cin>>v;
            if(v<0 || v>=256 || __builtin_parity(unsigned(v)) || base[s][v])return 2;
            original[s].push_back(v);base[s].set(v);
        }
    }
    if((base[0]&base[1]).count()!=1 || !base[0][0] || !base[1][0])return 2;
    for(int v=0;v<256;++v)for(int b=0;b<8;++b)neighbors[v].set(v^(1<<b));
    int fixed=1-changing;
    Shape fixed_shape(base[fixed],cap==fixed);
    auto fixed_orders=fixed_shape.all_orders(original[fixed]);
    if(fixed_orders.empty()){cout<<"fixed-impossible\n";return 0;}
    struct Known{Path order;vector<Mask> lists;};
    vector<Known> known;
    for(const auto& order:fixed_orders)known.push_back({order,fixed_shape.lists(order)});
    Path rm,add;
    for(int x:original[changing])if(x)rm.push_back(x);
    for(int v=0;v<256;++v)if(!__builtin_parity(unsigned(v)) && !base[0][v] && !base[1][v])add.push_back(v);
    uint64_t count=0,initial=0,orderable=0,pairs=0;
    Mask selected=base[changing];
    array<int,256> weight{},label{},degree{},caps_available{};
    array<array<int,256>,256> multiplicity{};
    auto contribution=[&](int w,int sign){
        if(weight[w]==1){caps_available[label[w]]+=sign;return;}
        if(weight[w]!=2)return;
        int x=int((neighbors[w]&selected).first()),y=label[w]^x;
        int before=multiplicity[x][y],after=before+sign;
        multiplicity[x][y]=multiplicity[y][x]=after;
        if((before==0)!=(after==0)){degree[x]+=sign;degree[y]+=sign;}
    };
    for(int v:original[changing])
        for(int b=0;b<8;++b){int w=v^(1<<b);++weight[w];label[w]^=v;}
    for(int w=0;w<256;++w)contribution(w,1);
    auto toggle=[&](int v){
        int sign=selected[v]?-1:1;
        for(int b=0;b<8;++b)contribution(v^(1<<b),-1);
        selected.flip(v);
        for(int b=0;b<8;++b){
            int w=v^(1<<b);weight[w]+=sign;label[w]^=v;contribution(w,1);
        }
    };
    auto evaluate=[&]()->bool{
        ++count;int leaves=0;
        for(size_t v=selected.first();v<256;v=selected.next(v)){
            if(!degree[v])return false;
            if(v && degree[v]==1 && (++leaves>1 || (cap==changing && !caps_available[v])))return false;
        }
        ++initial;
        Path active;
        for(size_t v=selected.first();v<256;v=selected.next(v))active.push_back(int(v));
        Shape shape(selected,cap==changing);
        auto orders=shape.all_orders(active);
        if(orders.empty())return false;
        ++orderable;
        for(auto& p:orders){
            auto li=shape.lists(p);
            for(auto& other:known){
                ++pairs;
                vector<Mask> all=li;all.insert(all.end(),other.lists.begin(),other.lists.end());
                auto reps=matching(all);
                if(reps.empty())continue;
                array<Path,2> legs;
                auto make=[&](int s,const Path& order,int offset){
                    for(int i=0;i<int(order.size());++i){
                        legs[s].push_back(order[i]);
                        if(i+1<int(order.size()) || s==cap)legs[s].push_back(reps[offset+i]);
                    }
                };
                make(changing,p,0);make(fixed,other.order,int(li.size()));
                reverse(legs[0].begin(),legs[0].end());
                cout<<"witness";
                for(int v:legs[0])cout<<' '<<v;
                for(int v:legs[1])cout<<' '<<(v^256);
                cout<<'\n';return true;
            }
        }
        return false;
    };
    for(int i=0;i<int(rm.size());++i){toggle(rm[i]);
        for(int j=i+1;j<int(rm.size());++j){toggle(rm[j]);
            for(int h=0;h<int(add.size());++h){toggle(add[h]);
                for(int k=h+1;k<int(add.size());++k){
                    toggle(add[k]);if(evaluate())return 0;toggle(add[k]);
                }toggle(add[h]);
            }toggle(rm[j]);
        }toggle(rm[i]);
    }
    cout<<"count "<<count<<' '<<initial<<' '<<orderable<<' '<<pairs<<'\n';
}
