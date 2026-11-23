#define Q8_AUDIT_LIBRARY
#define Q8_HOST_LIBRARY
#include "verify_q8_clustered_hosts.cpp"
#include "search_q8_multicross_bank.cpp"
int main(){
 string w;while(cin>>w){
    if(w.size()!=191)return 3;
    int axis=-1;for(char c='0';c<='8';c++)if(count(w.begin(),w.end(),c)==1)axis=c-'0';
    if(axis<0)continue;
    P path{0};for(char c:w)path.push_back(path.back()^(1<<(c-'0')));
    assert(valid(path,9));for(int need=0;need<=3;need++){
        P host(path.begin()+(need+1)/2,path.end()-need/2);
        for(int extra=0;extra<=need;extra++){
            int k=int(host.size())+extra-192;
            Audit audit;bool answer=k>=0&&audit.run(host,191,k,extra);
            Refill solver;solver.goal=191;solver.vertices=host;for(int x:host)solver.used[x]=true;
            P witness;if(k>=0)witness=extra?solver.refill_external(k,extra):solver.visit(k);
            assert(answer==(extra==need) && answer==!witness.empty());
            if(answer)assert(valid(witness,9)&&witness.size()==192);
        }
        cout<<"PASS essential_external_points "<<need<<" edges 191"<<endl;
    }return 0;
 }return 4;
}
