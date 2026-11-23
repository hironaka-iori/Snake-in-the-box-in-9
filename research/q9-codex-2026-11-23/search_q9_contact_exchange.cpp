// Stochastic selection of deletions, followed by exact replacement for each tested set.
#define main unused_exchange_main
#include "search_q9_four_deletions.cpp"
#undef main
#include <cmath>
#include <random>
struct Sample:Exchange{
 std::mt19937 gen;
 vector<int> bag;
 int pick(int count){return int(gen()%count);}
 vector<int> avail(){
   vector<int> opts;
   for(int x:outside){
     if(degree[x]>2)continue;
     bool ok=true;
     for(int d=0;d<dim;d++){int u=x^(1<<d);if(active[u]&&degree[u]>=2){ok=false;break;}}
     if(ok)opts.push_back(x);
   }
   return opts;
 }
 int rate(const vector<int>& opts){
   array<int,512> cap{};
   for(int x:opts)for(int d=0;d<dim;d++)cap[x^(1<<d)]++;
   int forced=0,spare=0;
   for(int x:p)if(active[x]&&degree[x]<2){
      forced+=max(0,2-degree[x]-cap[x]);spare+=min(2-degree[x],cap[x]);
   }
   return 5*min(int(opts.size()),k+4)-9*max(0,forced-2)+min(spare,15);
 }
 bool sample(int rounds){
   n=p.size();N=1<<dim;if(!valid(p))abort();
   idx.fill(-1);for(int j=0;j<n;j++){idx[p[j]]=j;toggle(p[j],true);}
   for(int x=0;x<N;x++)if(!active[x])outside.push_back(x);
   for(int block=0;block<rounds;block++){
      k=6+pick(12); // Vary the radius, including changes well outside the smallest records.
      if(n<30)k=1+pick(min(4,n-1));
      int x=outside[pick(outside.size())];bag.clear();
      auto take=[&](int i){if(i>=0&&i<n&&active[p[i]]&&int(bag.size())<k){bag.push_back(i);toggle(p[i],false);}};
      for(int d=0;d<dim;d++){int j=idx[x^(1<<d)];if(j>=0)take(j);}
      while(int(bag.size())<k)take(pick(n));
      auto options=avail();int score=rate(options);
      for(int step=0;step<500;step++){
         int q=pick(k),old=bag[q],next;
         do{
            if(pick(4)&&!bag.empty()){
               int pivot=p[bag[pick(k)]];int y=pivot^(1<<pick(dim));
               if(pick(2))y^=1<<pick(dim);
               next=idx[y];if(next<0)next=bag[pick(k)]+pick(9)-4;
            }else next=pick(n);
         }while(next<0||next>=n||!active[p[next]]);
         toggle(p[old],true);toggle(p[next],false);auto cand=avail();int score2=rate(cand);
         if(int(cand.size())>=k+gain){
            viable++;if(add(cand,0,k+gain))return true;
         }
         tested++;
         double temp=5.-3.8*(step%100)/100.;
         if(score2>=score||std::generate_canonical<double,32>(gen)<exp((score2-score)/temp)){
            score=score2;bag[q]=next;
         }else{toggle(p[next],true);toggle(p[old],false);}
      }
      for(int j:bag)toggle(p[j],true);
   }
   return false;
 }
};
int main(int argc,char**argv){
 if(argc!=4&&argc!=5)return 1;
 if(const char* file=getenv("Q9_AVOID_SHAPES")){
    ifstream in(file);string key;while(in>>key)blockedFragments.insert(key);
    if(blockedFragments.size()!=17974)return 2;
 }int row=0;string l;
 while(getline(cin,l)){
   Sample s{};s.dim=stoi(argv[1]);if(argc==5)s.gain=stoi(argv[4]);s.gen.seed(stoul(argv[3])+row);istringstream f(l);int x;while(f>>x)s.p.push_back(x);
   bool ok=s.sample(stoi(argv[2]));cout<<row++<<" "<<(ok?"FOUND":"SAMPLED")<<" "<<s.tested<<" "<<s.viable<<" "<<s.trials;
   for(int v:s.witness)cout<<" "<<v;
   cout<<endl;if(ok&&s.witness.size()>=193)break;
 }
}
