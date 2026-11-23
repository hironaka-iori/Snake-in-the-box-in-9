#define PORTS_LIBRARY
#include "search_q9_port_matching.cpp"
int main(){
    int target,bridge,arm,n;
    while(cin>>target>>bridge>>arm>>n){
        Path p;vector<pair<int,int>> islands;
        for(int j=0;j<n;j++){int length,x;cin>>length;int from=p.size();while(length--){cin>>x;p.push_back(x);}islands.push_back({from,int(p.size())-1});}
        Ports g;
        if(g.run(p,islands,target,bridge,arm,500000,10000)){
            cout<<"YES";for(int v:g.witness)cout<<" "<<v;cout<<endl;
        }else cout<<(g.cutoff||g.incomplete?"UNKNOWN":"NO")<<endl;
    }
}
