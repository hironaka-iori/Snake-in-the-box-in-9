#define main previous_odd_driver
#include "search_q9_odd_hamilton.cpp"
#undef main
#include <unordered_set>
#include <algorithm>
int main(int argc,char**argv){
 if(argc!=3)return 2;
 Odd odd(argv[1],stoi(argv[2]));set<Path> even_checked;uint64_t tested=0,undecided=0,rows=0;
 string l;while(getline(cin,l)){
  istringstream f(l);int x;Path p;while(f>>x)p.push_back(x);if(p.size()!=193)abort();++rows;
  Path a,b;for(int i=0;i<193;i++)(i%2?b:a).push_back(p[i]);
  auto tryset=[&](Path t,bool major,bool probe){
   sort(t.begin(),t.end());if(!even_checked.insert(t).second)return false;
   Search s(t,16000,major);tested++;
   if(s.test())return true;undecided+=s.unknown;
   if(probe&&odd.test(t))return true;return false;
  };
  if(tryset(a,true,false)||tryset(b,false,true))return 0;
  for(int k=0;k<97;k++){auto q=a;q.erase(q.begin()+k);if(tryset(q,false,true))return 0;}
  if(rows%200==0)cout<<"RUN "<<rows<<" sets "<<tested<<" even unknown "<<undecided<<" orders "<<odd.orders<<" lifts "<<odd.lifts<<" unknown "<<odd.unknown<<" new "<<odd.novel.size()<<endl;
 }
 cout<<"DONE "<<rows<<" sets "<<tested<<" even unknown "<<undecided<<" orders "<<odd.orders<<" lifts "<<odd.lifts<<" odd unknown "<<odd.unknown<<" new "<<odd.novel.size()<<endl;
}
