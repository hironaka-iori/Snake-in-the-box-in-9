#define main q9_orders_driver
#include "search_q9_excused_orders.cpp"
#undef main
#include <random>
int main(){
 std::mt19937 rng(808);set<string> known;ostringstream output;
 uint64_t cases=0,orders=0,lifts=0,clean=0;
 for(int trial=0;trial<150;trial++){
  Path eligible;for(int v=0;v<32;v++)if(popcount(unsigned(v))%2==0)eligible.push_back(v);
  shuffle(eligible.begin(),eligible.end(),rng);eligible.resize(3+trial%4);
  int a=eligible[rng()%eligible.size()],b=a^(1<<(rng()%5));
  for(bool major:{false,true}){
   Path fixed=eligible;Search s(fixed,100000);s.axes[b]^=a^b;
   Repair solver{a,b,100000,known,output};solver.countOnly=true;solver.check(s,major);
   uint64_t wantOrders=0,wantLifts=0,wantClean=0;
   sort(fixed.begin(),fixed.end());
   do {
    if(fixed.front()>fixed.back())continue;
    vector<Path> groups(fixed.size()+(major?-1:1));
    for(int v=0;v<512;v++){
     Path incident;
     for(int i=0;i<fixed.size();i++)if(popcount(unsigned(v^fixed[i]))==1 && !(v==b&&fixed[i]==a))incident.push_back(i);
     if(incident.size()==2 && incident[1]==incident[0]+1)groups[incident[0]+!major].push_back(v);
     if(!major && incident.size()==1){
      if(incident[0]==0)groups.front().push_back(v);
      if(incident[0]==int(fixed.size())-1)groups.back().push_back(v);
     }
    }
    uint64_t ways=1,withoutB=1;for(auto &g:groups){ways*=g.size();withoutB*=g.size()-count(g.begin(),g.end(),b);}
    wantOrders+=ways>0;wantLifts+=ways;wantClean+=withoutB;
   }while(next_permutation(fixed.begin(),fixed.end()));
   assert(!solver.unknown && wantOrders==solver.positive && wantLifts==solver.lifts && wantClean==solver.clean);
   cases++;orders+=wantOrders;lifts+=wantLifts;clean+=wantClean;
  }
 }
 cout<<"verified cases "<<cases<<" orders "<<orders<<" lifts "<<lifts<<" clean "<<clean<<endl;
}
