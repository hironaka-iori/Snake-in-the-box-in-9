#define main all_arm_pairs_driver
#include "armpairs.cpp"
#undef main
struct Bound:Path {
 int depth(int x){
  int m=0;for(int i=0;i<9;i++){int v=x^(1<<i);if(used[v]||near[v]!=1)continue;add(v,1);m=max(m,1+depth(v));add(v,-1);}return m;
 }
 bool exceeds(const string&w,int target,int&pairtests){
  vector<int> p{0};for(char c:w)p.push_back(p.back()^(1<<(c-'0')));for(int v:p)add(v,1);
  int need=target-int(w.size());if(depth(p.front())+depth(p.back())<need)return false;
  pairtests++;
  vector<Arm>left,right;Arm a;arms(p.front(),a,left);arms(p.back(),a,right);
  auto cmp=[](auto&u,auto&v){return u.n>v.n;};sort(left.begin(),left.end(),cmp);sort(right.begin(),right.end(),cmp);
  for(auto&u:left){if(u.n+right[0].n<need)break;for(auto&v:right){if(u.n+v.n<need)break;
   bool compatible=true;for(int k=0;k<8;k++)if(u.points[k]&v.blocked[k]){compatible=false;break;}if(compatible)return true;
  }}return false;
 }
};
int main(int argc,char**argv){if(argc!=3)return 2;int n=0,tests=0,hits=0,goal=stoi(argv[2]);ifstream in(argv[1]);string s;
 while(getline(in,s)){auto i=s.find(' '),j=s.find(' ',i+1);Bound b;
  if(b.exceeds(s.substr(i+1,j-i-1),goal,tests)){hits++;cout<<"HIT "<<n+1<<endl;}
  if(++n%50000==0)cout<<"AT "<<n<<" paired "<<tests<<endl;
 }cout<<"DONE "<<n<<" goal "<<goal<<" paired "<<tests<<" hits "<<hits<<endl;
}
