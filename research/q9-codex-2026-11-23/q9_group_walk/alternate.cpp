// Switch the partition between repair passes. Keep the best actual cube trace.
#define GROUP_WALK_LIBRARY
#include "repair.cpp"
#include <fstream>
#include <sstream>
#include <unordered_set>
using Order=array<int,9>;
vector<Order> partitions(){
    vector<Order> result;Order a;iota(a.begin(),a.end(),0);
    do{
        if(a[0]>a[3]||a[3]>a[6])continue;
        if(is_sorted(a.begin(),a.begin()+3)&&is_sorted(a.begin()+3,a.begin()+6)&&is_sorted(a.begin()+6,a.end()))result.push_back(a);
    }while(next_permutation(a.begin(),a.end()));
    assert(result.size()==280);return result;
}
string encode(const P& p,bool reversePath){
    // Sort the nine binary columns of transition masks, so even invalid triples are comparable.
    array<string,9> columns;int n=p.size();
    for(int k=0;k<9;k++)for(int i=1;i<n;i++){
        int a=reversePath?n-i:i;
        columns[k]+=char('0'+(((p[a]^p[a-1])>>k)&1));
    }
    sort(columns.begin(),columns.end());string key;for(auto& col:columns)key+=col;
    return key;
}
string key(const P&p){return min(encode(p,false),encode(p,true));}
string representation(const P&p,const Order& order){
    array<int,3> masks{};
    for(int k=0;k<9;k++)masks[k/3]|=1<<order[k];
    string w;
    for(int i=1;i<int(p.size());i++){
        int d=p[i]^p[i-1];if(popcount(unsigned(d))!=1&&popcount(unsigned(d))!=3)return "";
        if(none_of(masks.begin(),masks.end(),[&](int g){return (d&g)==d;}))return "";
        w+=char('0'+countr_zero(unsigned(d)));
    }
    return w;
}
int main(int argc,char**argv){
    if(argc!=6)return 2;
    int target=stoi(argv[1]),budget=stoi(argv[2]),jobs=stoi(argv[3]),depth=stoi(argv[4]);mt19937 rng(stoul(argv[5]));
    vector<string> parents;string word;while(cin>>word)parents.push_back(word);
    auto orders=partitions();unordered_set<string> seen;vector<P> pool;int best=10000;
    for(int j=0;j<jobs;j++){
        bool fromBank=pool.empty()||rng()%4==0;
        P input;string w;const Order* chosen=nullptr;
        if(fromBank){
            w=parents[rng()%parents.size()];if(rng()%2)reverse(w.begin(),w.end());
            while(int(w.size())<target){vector<pair<int,string>> trial;
                for(int k=0;k<96;k++){auto t=w;t.insert(rng()%(w.size()+1),1,char('0'+rng()%9));Repair c(t,orders[0],1,rng);trial.emplace_back(c.errors().size(),t);}
                sort(trial.begin(),trial.end());w=trial[rng()%5].second;
            }
            chosen=&orders[rng()%orders.size()];
        }else{
            input=pool[rng()%pool.size()];shuffle(orders.begin(),orders.end(),rng);
            for(auto& a:orders){w=representation(input,a);if(!w.empty()){chosen=&a;break;}}
            if(!chosen)continue;
        }
        Repair h(w,*chosen,budget,rng);if(!input.empty())h.p=input;h.capture=true;
        int initial=h.errors().size();bool found=h.run(depth);
        if(found){assert(valid(h.p));cout<<"FOUND "<<j<<" "<<target;for(int v:h.p)cout<<" "<<v;cout<<endl;return 0;}
        if(h.record.empty())abort();
        if(h.best<=max(3,min(10,best+3)) && seen.insert(key(h.record)).second){
            pool.push_back(h.record);best=min(best,h.best);
            cout<<"BANK "<<j<<" "<<initial<<" "<<h.best<<" "<<pool.size();for(int v:h.record)cout<<" "<<v;cout<<endl;
        }
        if(j%32==0)cout<<"PROGRESS "<<j<<" "<<pool.size()<<" "<<initial<<" "<<h.best<<" "<<h.nodes<<" "<<h.cut<<endl;
    }
}
