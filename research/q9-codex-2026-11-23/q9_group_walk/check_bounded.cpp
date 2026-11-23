#define GROUP_WALK_LIBRARY
#include "repair.cpp"
int main(){
    mt19937 rng(779431);int both[2]{};
    for(int caseNo=0;caseNo<1000;caseNo++){
        int n=3+rng()%12,depth=rng()%3;string w;for(int j=0;j<n;j++)w+=char('0'+rng()%9);
        array<int,9> order;iota(order.begin(),order.end(),0);shuffle(order.begin(),order.end(),rng);
        Repair solver(w,order,1000000,rng);P seed=solver.p;
        // Independently number the visits (group, local time) along the word.
        array<int,9> group{};array<int,3> local{};
        for(int k=0;k<9;k++)group[order[k]]=k/3;
        vector<array<int,3>> states{local};
        for(char c:w){local[group[c-'0']]++;states.push_back(local);}
        vector<pair<int,int>> cells;
        for(int g=0;g<3;g++)for(int i=0;i<=local[g];i++)cells.emplace_back(g,i);
        auto test=[&](auto&& self,int start,int left,P p)->bool{
            if(valid(p))return true;if(!left)return false;
            for(int k=start;k<int(cells.size());k++){auto [g,t]=cells[k];
                for(int a=0;a<3;a++)for(int b=a+1;b<3;b++){P q=p;
                    for(int i=0;i<int(q.size());i++)if(states[i][g]==t)q[i]^=(1<<order[3*g+a])|(1<<order[3*g+b]);
                    if(self(self,k+1,left-1,q))return true;
                }
            }return false;
        };
        bool a=test(test,0,depth,seed),b=solver.run(depth);assert(!solver.cut&&a==b);both[a]++;
    }
    cout<<"tests 1000 unsat "<<both[0]<<" found "<<both[1]<<endl;
}
