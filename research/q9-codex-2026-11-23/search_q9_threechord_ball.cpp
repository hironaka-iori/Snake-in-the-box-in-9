// Explore an energy-three neighborhood of a bank of 192-step one-chord walks under square moves, end moves,
// and all pivots that transpose two coordinate axes on a whole suffix.
#define Q9_FIXED_BRIDGE_NO_DRIVER
#include "search_q9_fixed_bridge.cpp"
#include <deque>
int main(int argc,char**argv){
 if(argc!=3)return 2;int cap=stoi(argv[1]);long long overflow=0,newone=0;ofstream out(argv[2]);if(!out)return 3;
 unordered_set<string> seen;
 deque<vector<int>>queue;
 string line;long long moves=0,accepted=0;
 auto observe=[&](const vector<int>&p,int energy){
  if(energy>3)return false;
  if(!energy){Walk test(9,p);test.verify();if(test.E)abort();cout<<"FOUND";for(int v:p)cout<<" "<<v;cout<<endl;return true;}
  if(energy>=2 && seen.size()>=400000){overflow++;return false;}
  if(seen.insert(key(p)).second){
   Walk test(9,p);test.verify();if(test.E!=energy)abort();
   if(energy==3){queue.push_back(p);return false;}
   if(energy==2){queue.push_front(p);return false;}
   newone++;queue.push_front(p);for(size_t i=0;i<p.size();i++)out<<(i?" ":"")<<p[i];out<<endl;accepted++;
  }
  return false;
 };
 while(getline(cin,line)){istringstream is(line);vector<int>p;int x;while(is>>x)p.push_back(x);if(p.empty())continue;Walk w(9,p);w.verify();if(w.E>3)return 4;if(observe(p,w.E))return 0;}
 int expanded=0;
 while(!queue.empty()&&expanded<cap){
  auto path=queue.front();queue.pop_front();int n=path.size();Walk w(9,path);
  for(int i=1;i+1<n;i++){
   int a=path[i-1]^path[i]^path[i+1];if(a==path[i]||w.cnt[a])continue;
   int orig=path[i];w.edit(orig,-1);w.edit(a,1);path[i]=a;moves++;
   if(observe(path,w.E))return 0;
   path[i]=orig;w.edit(a,-1);w.edit(orig,1);
  }
  for(int side=0;side<2;side++){
   reverse(path.begin(),path.end());
   for(int end=0;end<2;end++){
    int removed=end?path[0]:path[n-1],base=end?path[n-1]:path[n-2];w.edit(removed,-1);
    for(int d=0;d<9;d++){
     int v=base^(1<<d);if(w.cnt[v])continue;
     w.edit(v,1);moves++;
     if(w.E<=3){vector<int>q=path;if(end){q.erase(q.begin());q.push_back(v);}else q.back()=v;if(observe(q,w.E))return 0;}
     w.edit(v,-1);
    }
    w.edit(removed,1);
   }
   for(int j=2;j<n;j++)if(popcount((unsigned)(path[j]^path[0]))==1){
    auto q=path;reverse(q.begin(),q.begin()+j);moves++;if(observe(q,w.E))return 0;
   }
  }
  for(int a=0;a<9;a++)for(int b=0;b<a;b++)for(int c=0;c<=1;c++){
   int mask=(1<<a)|(1<<b);
   vector<int> moved;for(int x:path)moved.push_back(x^((bool(x&1<<a)^bool(x&1<<b)^bool(c))?mask:0));
   Walk sweep(9,moved);
   int last_changed=n-1;while(last_changed>=0&&moved[last_changed]==path[last_changed])last_changed--;
   for(int i=0;i<last_changed;i++){
    if(moved[i]!=path[i]){sweep.edit(moved[i],-1);sweep.edit(path[i],1);continue;}
    moves++;if(sweep.E<=3){
     vector<int> q=path;copy(moved.begin()+i+1,moved.end(),q.begin()+i+1);
     if(observe(q,sweep.E))return 0;
    }
   }
  }
  if(++expanded%1000==0)cout<<"CHECK "<<expanded<<" distinct "<<seen.size()<<" queue "<<queue.size()<<" moves "<<moves<<" one "<<newone<<" overflow "<<overflow<<endl;
 }
 cout<<"DONE expanded "<<expanded<<" distinct "<<seen.size()<<" queue "<<queue.size()<<" moves "<<moves<<" one "<<newone<<" overflow "<<overflow<<endl;
}
