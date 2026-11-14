// Rotate the two outer arms about different hinges while preserving the middle
// spine. A valid image of each arm must avoid the spine; the two arms must
// additionally avoid one another's closed neighbourhoods in the nine-cube.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;
using Mask=array<uint64_t,8>;
array<Mask,512> closed;
void insert(Mask&m,int v){m[v>>6]|=1ull<<(v&63);}
bool has(const Mask&m,int v){return (m[v>>6]>>(v&63))&1;}
void unite(Mask&m,const Mask&b){for(int i=0;i<8;++i)m[i]|=b[i];}
bool separate(const Mask&a,const Mask&b){for(int i=0;i<8;++i)if(a[i]&b[i])return false;return true;}
struct Image {Mask used{},halo{};array<int,9> perm{};};
struct Catalog {int pin,dir;vector<Image> images;uint64_t nodes=0;};
struct Bisect {Mask common{};int left=-1,right=-1;vector<int> items;};
struct Index{
    vector<Bisect> tree;
    const vector<Image>& images;
    explicit Index(const vector<Image>& data):images(data){
        vector<int> order;for(int i=0;i<int(data.size());++i)order.push_back(i);
        if(!order.empty())build(order);
    }
    int build(const vector<int>& items){
        const int id=int(tree.size());tree.emplace_back();Mask common{};common.fill(~0ull);
        for(int i:items)for(int j=0;j<8;++j)common[j]&=images[i].used[j];
        tree[id].common=common;
        if(items.size()<=12){tree[id].items=items;return id;}
        array<int,512> frequency{};
        for(int i:items)for(int j=0;j<8;++j){auto word=images[i].used[j]&~common[j];while(word){
            ++frequency[64*j+countr_zero(word)];word&=word-1;}}
        int best=0,b=-1;for(int x=0;x<512;++x){int v=min(frequency[x],int(items.size())-frequency[x]);if(v>best){best=v;b=x;}}
        if(b<0){tree[id].items={items[0]};return id;}
        vector<int> yes,no;for(int i:items)(has(images[i].used,b)?yes:no).push_back(i);
        int left=build(yes),right=build(no);tree[id].left=left;tree[id].right=right;return id;
    }
    int find(int id,const Mask& blocked,uint64_t& checks)const{
        if(!separate(tree[id].common,blocked))return -1;
        if(tree[id].left<0){
            for(int i:tree[id].items){++checks;if(separate(images[i].used,blocked))return i;}
            return -1;
        }
        int hit=find(tree[id].left,blocked,checks);return hit>=0?hit:find(tree[id].right,blocked,checks);
    }
};
vector<int> reconstruct(const vector<int>&q,const Catalog& cat,const Image& img){
    vector<int> result;array<int,9> names;names.fill(-1);int next=0,v=q[cat.pin];
    for(int j=cat.pin;j+cat.dir>=0&&j+cat.dir<int(q.size());j+=cat.dir){
        int b=countr_zero(unsigned(q[j]^q[j+cat.dir]));if(names[b]<0)names[b]=next++;
        v^=1<<img.perm[names[b]];result.push_back(v);
    }
    return result;
}
Catalog catalogue(const vector<int>&q,int pin,int dir,const Mask&blocked){
    Catalog out{pin,dir};int n=int(q.size()),named=0;array<int,9> old;old.fill(-1);
    vector<int> coords;
    for(int i=pin;i+dir>=0&&i+dir<n;i+=dir){
        int b=countr_zero(unsigned(q[i]^q[i+dir]));
        if(old[b]<0)old[b]=named++;coords.push_back(old[b]);
    }
    array<int,9> perm{};
    auto run=[&](auto&& self,int i,int v,int count,int used,Mask occupied)->void{
        ++out.nodes;
        if(i==int(coords.size())){
            Image img;img.used=occupied;img.perm=perm;
            for(int j=0;j<8;++j){auto bits=occupied[j];while(bits){
                int w=64*j+countr_zero(bits);bits&=bits-1;unite(img.halo,closed[w]);}}
            out.images.push_back(img);return;
        }
        int b=coords[i];int begin=b<count?perm[b]:0,end=b<count?begin+1:9;
        for(int a=begin;a<end;++a){
            if(b==count&&(used&(1<<a)))continue;
            int w=v^(1<<a);if(has(blocked,w))continue;
            Mask next=occupied;insert(next,w);perm[b]=a;
            self(self,i+1,w,count+(b==count),used|(1<<a),next);
        }
    };
    run(run,0,q[pin],0,0,Mask{});return out;
}
int main(int argc,char**argv){
    if(argc!=3 && argc!=4)return 2;int lo=stoi(argv[1]),hi=stoi(argv[2]);
    bool use_index=argc==4;
    vector<int> q;for(int x;cin>>x;)q.push_back(x);
    int n=int(q.size()),s=-1,t=-1,chords=0;
    for(int j=0;j<n;++j)for(int i=0;i<j;++i){
        int d=popcount(unsigned(q[i]^q[j]));if(j==i+1&&d!=1)return 3;
        if(j>i+1&&d<2){++chords;s=i;t=j;}
    }
    if(chords!=1)return 4;
    for(int v=0;v<512;++v){insert(closed[v],v);for(int b=0;b<9;++b)insert(closed[v],v^(1<<b));}
    uint64_t pairs=0,rejected=0,entered=0,images=0,comparisons=0;
    for(int l=1;l<n-2;++l)for(int r=l+1;r<n-1;++r){
        int length=r-l+1;if(length<lo||length>hi)continue;
        ++pairs;
        if(t<=l||s>=r||(s>=l&&t<=r)){++rejected;continue;}
        Mask blockL{},blockR{};
        for(int j=l;j<=r;++j){if(j!=l)unite(blockL,closed[q[j]]);if(j!=r)unite(blockR,closed[q[j]]);}
        insert(blockL,q[l]);insert(blockR,q[r]);
        // An arm is verified internally by its source. It can meet the
        // neighbourhood of its own hinge in its first site only.
        auto L=catalogue(q,l,-1,blockL);entered+=L.nodes;images+=L.images.size();
        if(L.images.empty())continue;
        auto R=catalogue(q,r,1,blockR);entered+=R.nodes;images+=R.images.size();
        auto output=[&](const Image&left,const Image&right){
            auto a=reconstruct(q,L,left),b=reconstruct(q,R,right);reverse(a.begin(),a.end());
            cout<<"FOUND "<<l<<" "<<r;for(int v:a)cout<<" "<<v;
            for(int j=l;j<=r;++j)cout<<" "<<q[j];for(int v:b)cout<<" "<<v;
            cout<<"\n";
        };
        if(use_index && R.images.size()>=40 && L.images.size()>=12){
            Index index(R.images);
            for(const auto&left:L.images){
                int i=index.find(0,left.halo,comparisons);
                if(i>=0){output(left,R.images[i]);return 0;}
            }
        }else for(const auto&left:L.images)for(const auto&right:R.images){
            ++comparisons;
            if(separate(left.halo,right.used)){output(left,right);return 0;}
        }
    }
    cout<<"EXHAUSTED "<<pairs<<" "<<rejected<<" "<<entered<<" "<<images<<" "<<comparisons<<"\n";
}
