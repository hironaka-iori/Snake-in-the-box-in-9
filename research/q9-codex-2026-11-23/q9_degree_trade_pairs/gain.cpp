#define main legacy_exchange_entry
#include "../search_q9_four_deletions.cpp"
#undef main
int main(int argc,char**argv){
 if(argc!=4)return 2;string line;int row=0;
 while(getline(cin,line)){
   Exchange s{};s.dim=stoi(argv[1]);s.k=stoi(argv[2]);s.gain=stoi(argv[3]);s.fastPairs=true;
   if(s.dim<1||s.dim>9||s.gain<1||s.gain>3||s.k<0)return 2;
   istringstream in(line);for(int v;in>>v;)s.p.push_back(v);if(s.p.empty())return 2;
   bool hit;
   if(s.k){hit=s.run();}else{
     s.n=s.p.size();s.N=1<<s.dim;if(!s.valid(s.p))return 3;
     for(int x:s.p)s.toggle(x,true);
     for(int i=0;i<s.N;i++)if(!s.active[i])s.outside.push_back(i);
     s.tested=1;hit=s.add(s.outside,0,s.gain);
   }
   cout<<row++<<" "<<hit<<" "<<s.tested<<" "<<s.viable<<" "<<s.trials;
   if(hit)for(int v:s.witness)cout<<" "<<v;
   cout<<endl;
 }
}
